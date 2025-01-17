// Copyright (c) 2021 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.platform.store.backend.postgresql

import java.time.format.DateTimeFormatter
import java.time.{Instant, ZoneOffset}

import com.daml.platform.store.backend.DBDTOV1
import com.daml.scalautil.NeverEqualsOverride

import scala.collection.mutable

// TODO append-only: consider removing the builder logic and switch to much easier multi-pass collecting, if memory pressure is not significantly bigger
// TODO append-only: hurts one to look around here, the whole file is a boilerplate, including related PostgreDAO artifacts (prepared statements and execution of them)
// TODO append-only: ideas:
//   - switch to weakly/runtime-typed: probably slower, verification problematic, ugly in a strongly typed context
//   - code generation script to generate from the DAO-s the necessary scala files
//   - scala macros
//   - some persistence mapper which is not getting in the way (unlikely for this specific usage)
case class RawDBBatchPostgreSQLV1(
    eventsBatchDivulgence: Option[EventsBatchDivulgence],
    eventsBatchCreate: Option[EventsBatchCreate],
    eventsBatchConsumingExercise: Option[EventsBatchExercise],
    eventsBatchNonConsumingExercise: Option[EventsBatchExercise],
    configurationEntriesBatch: Option[ConfigurationEntriesBatch],
    packageEntriesBatch: Option[PackageEntriesBatch],
    packagesBatch: Option[PackagesBatch],
    partiesBatch: Option[PartiesBatch],
    partyEntriesBatch: Option[PartyEntriesBatch],
    commandCompletionsBatch: Option[CommandCompletionsBatch],
    commandDeduplicationBatch: Option[CommandDeduplicationBatch],
)

case class EventsBatchDivulgence(
    event_offset: Array[String],
    command_id: Array[String],
    workflow_id: Array[String],
    application_id: Array[String],
    submitters: Array[String], // '|' separated list
    contract_id: Array[String],
    template_id: Array[String],
    tree_event_witnesses: Array[String], // '|' separated list
    create_argument: Array[Array[Byte]],
    event_sequential_id: Array[Long],
    create_argument_compression: Array[java.lang.Integer],
) extends NeverEqualsOverride

case class EventsBatchCreate(
    event_offset: Array[String],
    transaction_id: Array[String],
    ledger_effective_time: Array[String], // timestamp
    command_id: Array[String],
    workflow_id: Array[String],
    application_id: Array[String],
    submitters: Array[String], // '|' separated list
    node_index: Array[java.lang.Integer],
    event_id: Array[String],
    contract_id: Array[String],
    template_id: Array[String],
    flat_event_witnesses: Array[String], // '|' separated list
    tree_event_witnesses: Array[String], // '|' separated list
    create_argument: Array[Array[Byte]],
    create_signatories: Array[String], // '|' separated list
    create_observers: Array[String], // '|' separated list
    create_agreement_text: Array[String],
    create_key_value: Array[Array[Byte]],
    create_key_hash: Array[String],
    event_sequential_id: Array[Long],
    create_argument_compression: Array[java.lang.Integer],
    create_key_value_compression: Array[java.lang.Integer],
) extends NeverEqualsOverride

case class EventsBatchExercise(
    event_offset: Array[String],
    transaction_id: Array[String],
    ledger_effective_time: Array[String], // timestamp
    command_id: Array[String],
    workflow_id: Array[String],
    application_id: Array[String],
    submitters: Array[String], // '|' separated list
    node_index: Array[java.lang.Integer],
    event_id: Array[String],
    contract_id: Array[String],
    template_id: Array[String],
    flat_event_witnesses: Array[String], // '|' separated list
    tree_event_witnesses: Array[String], // '|' separated list
    create_key_value: Array[Array[Byte]],
    exercise_choice: Array[String],
    exercise_argument: Array[Array[Byte]],
    exercise_result: Array[Array[Byte]],
    exercise_actors: Array[String], // '|' separated list
    exercise_child_event_ids: Array[String], // '|' separated list
    event_sequential_id: Array[Long],
    create_key_value_compression: Array[java.lang.Integer],
    exercise_argument_compression: Array[java.lang.Integer],
    exercise_result_compression: Array[java.lang.Integer],
) extends NeverEqualsOverride

case class ConfigurationEntriesBatch(
    ledger_offset: Array[String],
    recorded_at: Array[String], // timestamp
    submission_id: Array[String],
    typ: Array[String],
    configuration: Array[Array[Byte]],
    rejection_reason: Array[String],
) extends NeverEqualsOverride

case class PackageEntriesBatch(
    ledger_offset: Array[String],
    recorded_at: Array[String], // timestamp
    submission_id: Array[String],
    typ: Array[String],
    rejection_reason: Array[String],
) extends NeverEqualsOverride

case class PackagesBatch(
    package_id: Array[String],
    upload_id: Array[String],
    source_description: Array[String],
    size: Array[Long],
    known_since: Array[String], // timestamp
    ledger_offset: Array[String],
    _package: Array[Array[Byte]],
) extends NeverEqualsOverride

case class PartiesBatch(
    party: Array[String],
    display_name: Array[String],
    explicit: Array[Boolean],
    ledger_offset: Array[String],
    is_local: Array[Boolean],
) extends NeverEqualsOverride

case class PartyEntriesBatch(
    ledger_offset: Array[String],
    recorded_at: Array[String], // timestamp
    submission_id: Array[String],
    party: Array[String],
    display_name: Array[String],
    typ: Array[String],
    rejection_reason: Array[String],
    is_local: Array[java.lang.Boolean],
) extends NeverEqualsOverride

case class CommandCompletionsBatch(
    completion_offset: Array[String],
    record_time: Array[String], // timestamp
    application_id: Array[String],
    submitters: Array[String], // '|' separated list
    command_id: Array[String],
    transaction_id: Array[String],
    status_code: Array[java.lang.Integer],
    status_message: Array[String],
) extends NeverEqualsOverride

case class CommandDeduplicationBatch(deduplication_key: Array[String]) extends NeverEqualsOverride

object RawDBBatchPostgreSQLV1 {

  case class EventsBatchBuilderDivulgence(
      event_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      command_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      workflow_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      application_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      submitters: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      contract_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      template_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      tree_event_witnesses: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      create_argument: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      event_sequential_id: mutable.ArrayBuilder[Long] = mutable.ArrayBuilder.make[Long],
      create_argument_compression: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
  )

  case class EventsBatchBuilderCreate(
      event_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      transaction_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      ledger_effective_time: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // timestamp
      command_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      workflow_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      application_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      submitters: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      node_index: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
      event_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      contract_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      template_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      flat_event_witnesses: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      tree_event_witnesses: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      create_argument: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      create_signatories: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      create_observers: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      create_agreement_text: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      create_key_value: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      create_key_hash: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      event_sequential_id: mutable.ArrayBuilder[Long] = mutable.ArrayBuilder.make[Long],
      create_argument_compression: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
      create_key_value_compression: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
  )

  case class EventsBatchBuilderExercise(
      event_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      transaction_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      ledger_effective_time: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // timestamp
      command_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      workflow_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      application_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      submitters: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      node_index: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
      event_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      contract_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      template_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      flat_event_witnesses: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      tree_event_witnesses: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      create_key_value: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      exercise_choice: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      exercise_argument: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      exercise_result: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      exercise_actors: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      exercise_child_event_ids: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      event_sequential_id: mutable.ArrayBuilder[Long] = mutable.ArrayBuilder.make[Long],
      create_key_value_compression: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
      exercise_argument_compression: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
      exercise_result_compression: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
  )

  case class ConfigurationEntriesBatchBuilder(
      ledger_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      recorded_at: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String], // timestamp
      submission_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      typ: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      configuration: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
      rejection_reason: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
  )

  case class PackageEntriesBatchBuilder(
      ledger_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      recorded_at: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String], // timestamp
      submission_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      typ: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      rejection_reason: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
  )

  case class PackagesBatchBuilder(
      package_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      upload_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      source_description: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      size: mutable.ArrayBuilder[Long] = mutable.ArrayBuilder.make[Long],
      known_since: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String], // timestamp
      ledger_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      _package: mutable.ArrayBuilder[Array[Byte]] = mutable.ArrayBuilder.make[Array[Byte]],
  )

  case class PartiesBatchBuilder(
      party: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      display_name: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      explicit: mutable.ArrayBuilder[Boolean] = mutable.ArrayBuilder.make[Boolean],
      ledger_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      is_local: mutable.ArrayBuilder[Boolean] = mutable.ArrayBuilder.make[Boolean],
  )

  case class PartyEntriesBatchBuilder(
      ledger_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      recorded_at: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String], // timestamp
      submission_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      party: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      display_name: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      typ: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      rejection_reason: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      is_local: mutable.ArrayBuilder[java.lang.Boolean] =
        mutable.ArrayBuilder.make[java.lang.Boolean],
  )

  case class CommandCompletionsBatchBuilder(
      completion_offset: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      record_time: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String], // timestamp
      application_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      submitters: mutable.ArrayBuilder[String] =
        mutable.ArrayBuilder.make[String], // '|' separated list
      command_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      transaction_id: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
      status_code: mutable.ArrayBuilder[java.lang.Integer] =
        mutable.ArrayBuilder.make[java.lang.Integer],
      status_message: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String],
  )

  case class CommandDeduplicationBatchBuilder(
      deduplication_key: mutable.ArrayBuilder[String] = mutable.ArrayBuilder.make[String]
  )

  // WARNING! MUTABLE! not thread safe
  case class Builder() {

    import DBDTOV1._

    private[this] var eventsBatchBuilderDivulgence: EventsBatchBuilderDivulgence = _
    private[this] var eventsBatchBuilderCreate: EventsBatchBuilderCreate = _
    private[this] var eventsBatchBuilderConsumingExercise: EventsBatchBuilderExercise = _
    private[this] var eventsBatchBuilderNonConsumingExercise: EventsBatchBuilderExercise = _
    private[this] var configurationEntriesBatchBuilder: ConfigurationEntriesBatchBuilder = _
    private[this] var packageEntriesBatchBuilder: PackageEntriesBatchBuilder = _
    private[this] var packagesBatchBuilder: PackagesBatchBuilder = _
    private[this] var partiesBatchBuilder: PartiesBatchBuilder = _
    private[this] var partyEntriesBatchBuilder: PartyEntriesBatchBuilder = _
    private[this] var commandCompletionsBatchBuilder: CommandCompletionsBatchBuilder = _
    private[this] var commandDeduplicationBatchBuilder: CommandDeduplicationBatchBuilder = _

    def add(entry: DBDTOV1): Unit = {
      entry match {
        case e: EventDivulgence =>
          val eventsBatchBuilder: EventsBatchBuilderDivulgence =
            if (eventsBatchBuilderDivulgence == null) {
              eventsBatchBuilderDivulgence = EventsBatchBuilderDivulgence()
              eventsBatchBuilderDivulgence
            } else {
              eventsBatchBuilderDivulgence
            }
          eventsBatchBuilder.event_offset += e.event_offset.orNull
          eventsBatchBuilder.command_id += e.command_id.orNull
          eventsBatchBuilder.workflow_id += e.workflow_id.orNull
          eventsBatchBuilder.application_id += e.application_id.orNull
          eventsBatchBuilder.submitters += e.submitters.map(encodeTextArray).orNull
          eventsBatchBuilder.contract_id += e.contract_id
          eventsBatchBuilder.template_id += e.template_id.orNull
          eventsBatchBuilder.tree_event_witnesses += encodeTextArray(e.tree_event_witnesses)
          eventsBatchBuilder.create_argument += e.create_argument.orNull
          eventsBatchBuilder.event_sequential_id += e.event_sequential_id
          eventsBatchBuilder.create_argument_compression += e.create_argument_compression
            .map(x => x: java.lang.Integer)
            .orNull

        case e: EventCreate =>
          val eventsBatchBuilder: EventsBatchBuilderCreate =
            if (eventsBatchBuilderCreate == null) {
              eventsBatchBuilderCreate = EventsBatchBuilderCreate()
              eventsBatchBuilderCreate
            } else {
              eventsBatchBuilderCreate
            }
          eventsBatchBuilder.event_offset += e.event_offset.orNull
          eventsBatchBuilder.transaction_id += e.transaction_id.orNull
          eventsBatchBuilder.ledger_effective_time += e.ledger_effective_time
            .map(toPGTimestampString)
            .orNull
          eventsBatchBuilder.command_id += e.command_id.orNull
          eventsBatchBuilder.workflow_id += e.workflow_id.orNull
          eventsBatchBuilder.application_id += e.application_id.orNull
          eventsBatchBuilder.submitters += e.submitters.map(encodeTextArray).orNull
          eventsBatchBuilder.node_index += e.node_index.map(x => x: java.lang.Integer).orNull
          eventsBatchBuilder.event_id += e.event_id.orNull
          eventsBatchBuilder.contract_id += e.contract_id
          eventsBatchBuilder.template_id += e.template_id.orNull
          eventsBatchBuilder.flat_event_witnesses += encodeTextArray(e.flat_event_witnesses)
          eventsBatchBuilder.tree_event_witnesses += encodeTextArray(e.tree_event_witnesses)
          eventsBatchBuilder.create_argument += e.create_argument.orNull
          eventsBatchBuilder.create_signatories += e.create_signatories.map(encodeTextArray).orNull
          eventsBatchBuilder.create_observers += e.create_observers.map(encodeTextArray).orNull
          eventsBatchBuilder.create_agreement_text += e.create_agreement_text.orNull
          eventsBatchBuilder.create_key_value += e.create_key_value.orNull
          eventsBatchBuilder.create_key_hash += e.create_key_hash.orNull
          eventsBatchBuilder.event_sequential_id += e.event_sequential_id
          eventsBatchBuilder.create_argument_compression += e.create_argument_compression
            .map(x => x: java.lang.Integer)
            .orNull
          eventsBatchBuilder.create_key_value_compression += e.create_key_value_compression
            .map(x => x: java.lang.Integer)
            .orNull

        case e: EventExercise =>
          val eventsBatchBuilder: EventsBatchBuilderExercise =
            if (e.consuming) {
              if (eventsBatchBuilderConsumingExercise == null) {
                eventsBatchBuilderConsumingExercise = EventsBatchBuilderExercise()
                eventsBatchBuilderConsumingExercise
              } else {
                eventsBatchBuilderConsumingExercise
              }
            } else {
              if (eventsBatchBuilderNonConsumingExercise == null) {
                eventsBatchBuilderNonConsumingExercise = EventsBatchBuilderExercise()
                eventsBatchBuilderNonConsumingExercise
              } else {
                eventsBatchBuilderNonConsumingExercise
              }
            }
          eventsBatchBuilder.event_offset += e.event_offset.orNull
          eventsBatchBuilder.transaction_id += e.transaction_id.orNull
          eventsBatchBuilder.ledger_effective_time += e.ledger_effective_time
            .map(toPGTimestampString)
            .orNull
          eventsBatchBuilder.command_id += e.command_id.orNull
          eventsBatchBuilder.workflow_id += e.workflow_id.orNull
          eventsBatchBuilder.application_id += e.application_id.orNull
          eventsBatchBuilder.submitters += e.submitters.map(encodeTextArray).orNull
          eventsBatchBuilder.node_index += e.node_index.map(x => x: java.lang.Integer).orNull
          eventsBatchBuilder.event_id += e.event_id.orNull
          eventsBatchBuilder.contract_id += e.contract_id
          eventsBatchBuilder.template_id += e.template_id.orNull
          eventsBatchBuilder.flat_event_witnesses += encodeTextArray(e.flat_event_witnesses)
          eventsBatchBuilder.tree_event_witnesses += encodeTextArray(e.tree_event_witnesses)
          eventsBatchBuilder.create_key_value += e.create_key_value.orNull
          eventsBatchBuilder.exercise_choice += e.exercise_choice.orNull
          eventsBatchBuilder.exercise_argument += e.exercise_argument.orNull
          eventsBatchBuilder.exercise_result += e.exercise_result.orNull
          eventsBatchBuilder.exercise_actors += e.exercise_actors.map(encodeTextArray).orNull
          eventsBatchBuilder.exercise_child_event_ids += e.exercise_child_event_ids
            .map(encodeTextArray)
            .orNull
          eventsBatchBuilder.event_sequential_id += e.event_sequential_id
          eventsBatchBuilder.exercise_argument_compression += e.exercise_argument_compression
            .map(x => x: java.lang.Integer)
            .orNull
          eventsBatchBuilder.exercise_result_compression += e.exercise_result_compression
            .map(x => x: java.lang.Integer)
            .orNull

        case e: ConfigurationEntry =>
          if (configurationEntriesBatchBuilder == null)
            configurationEntriesBatchBuilder = ConfigurationEntriesBatchBuilder()
          configurationEntriesBatchBuilder.ledger_offset += e.ledger_offset
          configurationEntriesBatchBuilder.recorded_at += toPGTimestampString(e.recorded_at)
          configurationEntriesBatchBuilder.submission_id += e.submission_id
          configurationEntriesBatchBuilder.typ += e.typ
          configurationEntriesBatchBuilder.configuration += e.configuration
          configurationEntriesBatchBuilder.rejection_reason += e.rejection_reason.orNull

        case e: PackageEntry =>
          if (packageEntriesBatchBuilder == null)
            packageEntriesBatchBuilder = PackageEntriesBatchBuilder()
          packageEntriesBatchBuilder.ledger_offset += e.ledger_offset
          packageEntriesBatchBuilder.recorded_at += toPGTimestampString(e.recorded_at)
          packageEntriesBatchBuilder.submission_id += e.submission_id.orNull
          packageEntriesBatchBuilder.typ += e.typ
          packageEntriesBatchBuilder.rejection_reason += e.rejection_reason.orNull

        case e: Package =>
          if (packagesBatchBuilder == null) packagesBatchBuilder = PackagesBatchBuilder()
          packagesBatchBuilder.package_id += e.package_id
          packagesBatchBuilder.upload_id += e.upload_id
          packagesBatchBuilder.source_description += e.source_description.orNull
          packagesBatchBuilder.size += e.size
          packagesBatchBuilder.known_since += toPGTimestampString(e.known_since)
          packagesBatchBuilder.ledger_offset += e.ledger_offset
          packagesBatchBuilder._package += e._package

        case e: PartyEntry =>
          if (partyEntriesBatchBuilder == null)
            partyEntriesBatchBuilder = PartyEntriesBatchBuilder()
          partyEntriesBatchBuilder.ledger_offset += e.ledger_offset
          partyEntriesBatchBuilder.recorded_at += toPGTimestampString(e.recorded_at)
          partyEntriesBatchBuilder.submission_id += e.submission_id.orNull
          partyEntriesBatchBuilder.party += e.party.orNull
          partyEntriesBatchBuilder.display_name += e.display_name.orNull
          partyEntriesBatchBuilder.typ += e.typ
          partyEntriesBatchBuilder.rejection_reason += e.rejection_reason.orNull
          partyEntriesBatchBuilder.is_local += e.is_local.map(x => x: java.lang.Boolean).orNull

        case e: Party =>
          if (partiesBatchBuilder == null) partiesBatchBuilder = PartiesBatchBuilder()
          partiesBatchBuilder.party += e.party
          partiesBatchBuilder.display_name += e.display_name.orNull
          partiesBatchBuilder.explicit += e.explicit
          partiesBatchBuilder.ledger_offset += e.ledger_offset.orNull
          partiesBatchBuilder.is_local += e.is_local

        case e: CommandCompletion =>
          if (commandCompletionsBatchBuilder == null)
            commandCompletionsBatchBuilder = CommandCompletionsBatchBuilder()
          commandCompletionsBatchBuilder.completion_offset += e.completion_offset
          commandCompletionsBatchBuilder.record_time += toPGTimestampString(e.record_time)
          commandCompletionsBatchBuilder.application_id += e.application_id
          commandCompletionsBatchBuilder.submitters += encodeTextArray(e.submitters)
          commandCompletionsBatchBuilder.command_id += e.command_id
          commandCompletionsBatchBuilder.transaction_id += e.transaction_id.orNull
          commandCompletionsBatchBuilder.status_code += e.status_code
            .map(x => x: java.lang.Integer)
            .orNull
          commandCompletionsBatchBuilder.status_message += e.status_message.orNull

        case e: CommandDeduplication =>
          if (commandDeduplicationBatchBuilder == null)
            commandDeduplicationBatchBuilder = CommandDeduplicationBatchBuilder()
          commandDeduplicationBatchBuilder.deduplication_key += e.deduplication_key
      }
      ()
    }

    def build(): RawDBBatchPostgreSQLV1 = RawDBBatchPostgreSQLV1(
      eventsBatchDivulgence = Option(eventsBatchBuilderDivulgence).map(b =>
        EventsBatchDivulgence(
          event_offset = b.event_offset.result(),
          command_id = b.command_id.result(),
          workflow_id = b.workflow_id.result(),
          application_id = b.application_id.result(),
          submitters = b.submitters.result(),
          contract_id = b.contract_id.result(),
          template_id = b.template_id.result(),
          tree_event_witnesses = b.tree_event_witnesses.result(),
          create_argument = b.create_argument.result(),
          event_sequential_id = b.event_sequential_id.result(),
          create_argument_compression = b.create_argument_compression.result(),
        )
      ),
      eventsBatchCreate = Option(eventsBatchBuilderCreate).map(b =>
        EventsBatchCreate(
          event_offset = b.event_offset.result(),
          transaction_id = b.transaction_id.result(),
          ledger_effective_time = b.ledger_effective_time.result(),
          command_id = b.command_id.result(),
          workflow_id = b.workflow_id.result(),
          application_id = b.application_id.result(),
          submitters = b.submitters.result(),
          node_index = b.node_index.result(),
          event_id = b.event_id.result(),
          contract_id = b.contract_id.result(),
          template_id = b.template_id.result(),
          flat_event_witnesses = b.flat_event_witnesses.result(),
          tree_event_witnesses = b.tree_event_witnesses.result(),
          create_argument = b.create_argument.result(),
          create_signatories = b.create_signatories.result(),
          create_observers = b.create_observers.result(),
          create_agreement_text = b.create_agreement_text.result(),
          create_key_value = b.create_key_value.result(),
          create_key_hash = b.create_key_hash.result(),
          event_sequential_id = b.event_sequential_id.result(),
          create_argument_compression = b.create_argument_compression.result(),
          create_key_value_compression = b.create_key_value_compression.result(),
        )
      ),
      eventsBatchConsumingExercise = Option(eventsBatchBuilderConsumingExercise).map(b =>
        EventsBatchExercise(
          event_offset = b.event_offset.result(),
          transaction_id = b.transaction_id.result(),
          ledger_effective_time = b.ledger_effective_time.result(),
          command_id = b.command_id.result(),
          workflow_id = b.workflow_id.result(),
          application_id = b.application_id.result(),
          submitters = b.submitters.result(),
          node_index = b.node_index.result(),
          event_id = b.event_id.result(),
          contract_id = b.contract_id.result(),
          template_id = b.template_id.result(),
          flat_event_witnesses = b.flat_event_witnesses.result(),
          tree_event_witnesses = b.tree_event_witnesses.result(),
          create_key_value = b.create_key_value.result(),
          exercise_choice = b.exercise_choice.result(),
          exercise_argument = b.exercise_argument.result(),
          exercise_result = b.exercise_result.result(),
          exercise_actors = b.exercise_actors.result(),
          exercise_child_event_ids = b.exercise_child_event_ids.result(),
          event_sequential_id = b.event_sequential_id.result(),
          create_key_value_compression = b.create_key_value_compression.result(),
          exercise_argument_compression = b.exercise_argument_compression.result(),
          exercise_result_compression = b.exercise_result_compression.result(),
        )
      ),
      eventsBatchNonConsumingExercise = Option(eventsBatchBuilderNonConsumingExercise).map(b =>
        EventsBatchExercise(
          event_offset = b.event_offset.result(),
          transaction_id = b.transaction_id.result(),
          ledger_effective_time = b.ledger_effective_time.result(),
          command_id = b.command_id.result(),
          workflow_id = b.workflow_id.result(),
          application_id = b.application_id.result(),
          submitters = b.submitters.result(),
          node_index = b.node_index.result(),
          event_id = b.event_id.result(),
          contract_id = b.contract_id.result(),
          template_id = b.template_id.result(),
          flat_event_witnesses = b.flat_event_witnesses.result(),
          tree_event_witnesses = b.tree_event_witnesses.result(),
          create_key_value = b.create_key_value.result(),
          exercise_choice = b.exercise_choice.result(),
          exercise_argument = b.exercise_argument.result(),
          exercise_result = b.exercise_result.result(),
          exercise_actors = b.exercise_actors.result(),
          exercise_child_event_ids = b.exercise_child_event_ids.result(),
          event_sequential_id = b.event_sequential_id.result(),
          create_key_value_compression = b.create_key_value_compression.result(),
          exercise_argument_compression = b.exercise_argument_compression.result(),
          exercise_result_compression = b.exercise_result_compression.result(),
        )
      ),
      configurationEntriesBatch = Option(configurationEntriesBatchBuilder).map(b =>
        ConfigurationEntriesBatch(
          ledger_offset = b.ledger_offset.result(),
          recorded_at = b.recorded_at.result(),
          submission_id = b.submission_id.result(),
          typ = b.typ.result(),
          configuration = b.configuration.result(),
          rejection_reason = b.rejection_reason.result(),
        )
      ),
      packageEntriesBatch = Option(packageEntriesBatchBuilder).map(b =>
        PackageEntriesBatch(
          ledger_offset = b.ledger_offset.result(),
          recorded_at = b.recorded_at.result(),
          submission_id = b.submission_id.result(),
          typ = b.typ.result(),
          rejection_reason = b.rejection_reason.result(),
        )
      ),
      packagesBatch = Option(packagesBatchBuilder).map(b =>
        PackagesBatch(
          package_id = b.package_id.result(),
          upload_id = b.upload_id.result(),
          source_description = b.source_description.result(),
          size = b.size.result(),
          known_since = b.known_since.result(),
          ledger_offset = b.ledger_offset.result(),
          _package = b._package.result(),
        )
      ),
      partiesBatch = Option(partiesBatchBuilder).map(b =>
        PartiesBatch(
          party = b.party.result(),
          display_name = b.display_name.result(),
          explicit = b.explicit.result(),
          ledger_offset = b.ledger_offset.result(),
          is_local = b.is_local.result(),
        )
      ),
      partyEntriesBatch = Option(partyEntriesBatchBuilder).map(b =>
        PartyEntriesBatch(
          ledger_offset = b.ledger_offset.result(),
          recorded_at = b.recorded_at.result(),
          submission_id = b.submission_id.result(),
          party = b.party.result(),
          display_name = b.display_name.result(),
          typ = b.typ.result(),
          rejection_reason = b.rejection_reason.result(),
          is_local = b.is_local.result(),
        )
      ),
      commandCompletionsBatch = Option(commandCompletionsBatchBuilder).map(b =>
        CommandCompletionsBatch(
          completion_offset = b.completion_offset.result(),
          record_time = b.record_time.result(),
          application_id = b.application_id.result(),
          submitters = b.submitters.result(),
          command_id = b.command_id.result(),
          transaction_id = b.transaction_id.result(),
          status_code = b.status_code.result(),
          status_message = b.status_message.result(),
        )
      ),
      commandDeduplicationBatch = Option(commandDeduplicationBatchBuilder).map(b =>
        CommandDeduplicationBatch(
          deduplication_key = b.deduplication_key.result()
        )
      ),
    )
  }

  // TODO append-only: idea: string is a bit chatty for timestamp communication, maybe we can switch to epoch somehow?
  private val PGTimestampFormat =
    DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss.SSSSSS")
  def toPGTimestampString(instant: Instant): String =
    instant
      .atZone(ZoneOffset.UTC)
      .toLocalDateTime
      .format(PGTimestampFormat)

  def encodeTextArray(from: Iterable[String]): String =
    from.mkString("|") // FIXME safeguard/escape pipe chars in from
}
