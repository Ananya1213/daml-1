// Copyright (c) 2021 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf
package engine

import com.daml.lf.transaction.GlobalKey
import com.daml.lf.value.Value._

//TODO: Errors
sealed trait Error {
  // msg is intended to be a single line message
  def msg: String

  // details for debugging should be included here
  def detailMsg: String
  override def toString: String = "Error(" + msg + ")"
}

object Error {

  def withError[A](e: Error)(optional: Option[A]): Either[Error, A] = {
    optional.fold[Either[Error, A]](Left(e))(v => Right(v))
  }

  /** small conversion from option to either error with specific error */
  implicit class optionError[A](o: Option[A]) {
    def errorIfEmpty(e: Error) = withError(e)(o)
  }

  def apply(description: String) = new Error {
    val msg = description
    override def detailMsg = msg
  }

  def apply(description: String, details: String) = new Error {
    val msg = description
    val detailMsg = details
  }

}

final case class ContractNotFound(ci: ContractId) extends Error {
  override def msg = s"Contract could not be found with id $ci"
  override def detailMsg: String = msg
}

/** See com.daml.lf.transaction.Transaction.DuplicateContractKey
  * for more information.
  */
final case class DuplicateContractKey(key: GlobalKey) extends Error {
  override def msg = s"Duplicate contract key $key"
  override def detailMsg: String = msg
}

final case class ValidationError(override val msg: String)
    extends RuntimeException(s"ValidationError: $msg", null, true, false)
    with Error {
  override def detailMsg: String = msg
}

final case class ReplayMismatch(
    mismatch: transaction.ReplayMismatch[transaction.NodeId, ContractId]
) extends RuntimeException(s"ValidationError: ${mismatch.msg}", null, true, false)
    with Error {
  override def msg: String = mismatch.msg
  override def detailMsg: String = mismatch.msg
}

final case class AuthorizationError(override val msg: String) extends Error {
  override def detailMsg: String = msg
}

final case class SerializationError(override val msg: String) extends Error {
  override def detailMsg: String = s"Cannot serialize the transaction: $msg"
}
