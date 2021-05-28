// Copyright (c) 2021 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf
package speedy

import com.daml.lf.transaction.{NodeId, GenTransaction}
import com.daml.lf.transaction.Node.{GenNode, NodeRollback, NodeExercises, LeafOnlyActionNode}
import com.daml.lf.value.Value
import com.daml.lf.data.ImmArray

import scala.collection.mutable
import scala.annotation.tailrec

private[lf] object NormalizeRollbacks {

  private[this] type Nid = NodeId
  private[this] type Cid = Value.ContractId
  private[this] type TX = GenTransaction[Nid, Cid]
  private[this] type Node = GenNode[Nid, Cid]
  private[this] type LeafNode = LeafOnlyActionNode[Cid]
  private[this] type ExeNode = NodeExercises[Nid, Cid]

  // Normalize a transaction so rollback nodes satisfy the normalization rules.
  // see `makeRoll` below

  import Canonical.{Norm, Case, caseNorms}
  // The normalization phase works by constructing intermediate values which are
  // `Canonical` in the sense that only properly normalized nodes can be represented.
  // Although this doesn't ensure correctness, one class of bugs is avoided.

  def normalizeTx(txOriginal: TX): TX = {

    // Here we traverse the original transaction structure.
    // During the transformation, an original `Node` is mapped into a List[Norm]

    // The List is necessary because the rules can:
    // (1) drop nodes; (2) combine nodes (3) lift nodes from a lower level to a higher level.

    val GenTransaction(nodesOriginal, rootsOriginal) = txOriginal

    final case class TraverseNode(
      wrap: Vector[Norm] => Vector[Norm],
      children: Vector[Norm],
      todo: List[Nid],
    )

    def go(ns: List[TraverseNode]): Vector[Norm] = ns match {
      case Nil => Vector.empty
      case TraverseNode(wrap, children, Nil) :: Nil => wrap(children)
      case TraverseNode(wrap, children, Nil) :: n :: ns =>
        go(n.copy(children = n.children ++ wrap(children)) :: ns)
      case (n @ TraverseNode(_, _, t :: todo)) :: ns => nodesOriginal(t) match {
        case NodeRollback(children) =>
          val oldNode = n.copy(todo = todo)
          val rbNode = TraverseNode(
            children => makeRoll(children),
            children = Vector.empty,
            todo = children.toList)
          go(rbNode :: oldNode :: ns)
        case exe : NodeExercises[_, _] =>
          val oldNode = n.copy(todo = todo)
          val exeNode = TraverseNode(
            children => Vector(Norm.Exe(exe, children.toList)),
            children = Vector.empty,
            todo = exe.children.toList)
          go(exeNode :: oldNode :: ns)
        case leaf: LeafOnlyActionNode[_] =>
          go(n.copy(children = n.children :+ Norm.Leaf(leaf), todo = todo) :: ns)
      }

    }
    //pass 1
    val norms = go(List(TraverseNode(identity, Vector.empty, rootsOriginal.toList)))
    //pass 2
    val (finalState, roots) = pushNorms(initialState, norms)
    GenTransaction(finalState.nodeMap, roots)
  }

  // makeRoll: encodes the normalization transformation rules:
  //   rule #1: ROLL [ ] -> ε
  //   rule #2: ROLL [ ROLL [ xs… ] , ys… ] -> ROLL [ xs… ] , ROLL [ ys… ]
  //   rule #3: ROLL [ xs… , ROLL [ ys… ] ] ->  ROLL [ xs… , ys… ]

  //   rule #2/#3 overlap: ROLL [ ROLL [ xs… ] ] -> ROLL [ xs… ]

  @tailrec
  private[this] def makeRoll[R](
    norms: Vector[Norm],
    done: Vector[Norm] = Vector.empty,
  ): Vector[Norm] = {
    caseNorms(norms) match {
      case Case.Empty =>
        // normalization rule #1
        done

      case Case.Single(roll: Norm.Roll) =>
        // normalization rule #2/#3 overlap
        done :+ roll

      case Case.Single(act: Norm.Act) =>
        // no rule
        done :+ Norm.Roll1(act)

      case Case.Multi(h: Norm.Roll, m, t) =>
        // normalization rule #2
        makeRoll(m :+ t, done :+ h)

      case Case.Multi(h: Norm.Act, m, t: Norm.Roll) =>
        // normalization rule #3
        done :+ pushIntoRoll(h, m, t)

      case Case.Multi(h: Norm.Act, m, t: Norm.Act) =>
        // no rule
        done :+ Norm.Roll2(h, m, t)
    }
  }

  private def pushIntoRoll(a1: Norm.Act, xs2: Vector[Norm], t: Norm.Roll): Norm.Roll = {
    t match {
      case Norm.Roll1(a3) => Norm.Roll2(a1, xs2, a3)
      case Norm.Roll2(a3, xs4, a5) => Norm.Roll2(a1, xs2 ++ Vector(a3) ++ xs4, a5)
    }
  }

  // State manages a counter for node-id generation, and accumulates the nodes-map for
  // the normalized transaction

  // There is no connection between the ids in the original and normalized transaction.

  private[this] case class State(index: Int, nodeMap: Map[Nid, Node]) {

    def next: (State, Nid) =
      (State(index + 1, nodeMap), NodeId(index))

    def push(nid: Nid, node: Node): State =
      State(index, nodeMap = nodeMap + (nid -> node))
  }

  // The `push*` functions convert the Canonical types to the tx being collected in State.
  // Ensuring:
  // - The final tx has increasing node-ids when nodes are listed in pre-order.
  // - The root node-id is 0 (we have tests that rely on this)

  private val initialState = State(0, Map.empty)

  private final case class ProcessingNode(
      addNode: (State, ImmArray[Nid]) => State,
      children: mutable.Builder[Nid, ImmArray[Nid]],
      childrenTodo: Seq[Norm],
  )

  @tailrec
  private def go(s: State, xs: List[ProcessingNode]): State = xs match {
    case Nil => s
    case (node @ ProcessingNode(_, _, c +: cs)) :: xs =>
      val (s2, nid) = s.next
      val node2 = node.copy(children = node.children += nid, childrenTodo = cs)
      c match {
        case act: Norm.Act =>
          act match {
            case Norm.Leaf(node) => go(s2.push(nid, node), node2 :: xs)
            case Norm.Exe(node, children) =>
              val node3 = ProcessingNode(
                (s, children) => s.push(nid, node.copy(children = children)),
                ImmArray.newBuilder,
                children,
              )
              go(s2, node3 :: node2 :: xs)
          }
        case roll: Norm.Roll =>
          roll match {
            case Norm.Roll1(act) =>
              val node3 =
                ProcessingNode((s, children) => s.push(nid, NodeRollback(children)), ImmArray.newBuilder, List(act))
              go(s2, node3 :: node2 :: xs)
            case Norm.Roll2(h, m, t) =>
              val node3 = ProcessingNode(
                (s, children) => s.push(nid, NodeRollback(children)),
                ImmArray.newBuilder,
                h +: m :+ t,
              )
              go(s2, node3 :: node2 :: xs)
          }
      }
    case ProcessingNode(addNode, children, _) :: xs =>
      go(addNode(s, children.result()), xs)
  }

  private def pushNorms(s: State, xs: Vector[Norm]): (State, ImmArray[Nid]) = {
    var roots: ImmArray[Nid] = ImmArray.empty
    val finalState = go(
      s,
      List(
        ProcessingNode(
          (s, children) => {
            roots = children
            s
          },
          ImmArray.newBuilder,
          xs.toList,
        )
      ),
    )
    (finalState, roots)
  }

  // Types which ensure we can only represent the properly normalized cases.
  private object Canonical {

    // A properly normalized Tx/node
    sealed trait Norm
    object Norm {

      // A non-rollback tx/node
      sealed trait Act extends Norm
      final case class Leaf(node: LeafNode) extends Act
      final case class Exe(node: ExeNode, children: List[Norm]) extends Act

      // A *normalized* rollback tx/node. 2 cases:
      // - rollback containing a single non-rollback tx/node.
      // - rollback of 2 or more tx/nodes, such that first and last are not rollbacks.
      sealed trait Roll extends Norm
      final case class Roll1(act: Act) extends Roll
      final case class Roll2(head: Act, middle: Vector[Norm], tail: Act) extends Roll
    }

    // Case analysis on a list of Norms, distinuishing: Empty, Single and Multi forms
    // The Multi form separes the head and tail element for the middle-list.
    sealed trait Case
    object Case {
      final case object Empty extends Case
      final case class Single(n: Norm) extends Case
      final case class Multi(h: Norm, m: Vector[Norm], t: Norm) extends Case
    }

    def caseNorms(xs: Vector[Norm]): Case = {
      xs.length match {
        case 0 => Case.Empty
        case 1 => Case.Single(xs(0))
        case n => Case.Multi(xs(0), xs.slice(1, n - 1), xs(n - 1))
      }
    }
  }
}
