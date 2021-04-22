package com.daml.platform.store.dao

import org.scalatest.flatspec.AsyncFlatSpec
import org.scalatest.matchers.should.Matchers

class JdbcLedgerDaoPipelinedOracleSpec extends AsyncFlatSpec
  with Matchers
  with JdbcLedgerDaoSuite
  with JdbcLedgerDaoBackendOracle
  with JdbcLedgerDaoPackagesSpec
  with JdbcLedgerDaoActiveContractsSpec
  with JdbcLedgerDaoCompletionsSpec
  with JdbcLedgerDaoContractsSpec
  with JdbcLedgerDaoDivulgenceSpec
  with JdbcLedgerDaoTransactionsSpec
  with JdbcLedgerDaoTransactionTreesSpec
  with JdbcLedgerDaoTransactionsWriterSpec
  with JdbcPipelinedInsertionsSpec
  with JdbcPipelinedTransactionInsertion
