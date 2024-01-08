//! Mock dispatch context for use in tests.
use std::collections::BTreeMap;

use oasis_core_runtime::{
    common::{namespace::Namespace, version::Version},
    consensus::{beacon, roothash, state::ConsensusState, Event},
    protocol::{self, HostInfo},
    storage::mkvs,
    types::EventKind,
    Protocol,
};

use crate::{
    context::{BatchContext, Mode, RuntimeBatchContext},
    crypto::random::RootRng,
    dispatcher,
    error::RuntimeError,
    history,
    keymanager::KeyManager,
    module::MigrationHandler,
    modules,
    read_syncer::{self, HostTree},
    runtime::Runtime,
    storage::{CurrentStore, MKVSStore},
    testing::{configmap, keymanager::MockKeyManagerClient},
    types::{address::SignatureAddressSpec, transaction},
};

pub struct Config;

impl modules::core::Config for Config {}

/// A mock runtime that only has the core module.
pub struct EmptyRuntime;

impl Runtime for EmptyRuntime {
    const VERSION: Version = Version::new(0, 0, 0);

    type Core = modules::core::Module<Config>;

    type Modules = modules::core::Module<Config>;

    fn genesis_state() -> <Self::Modules as MigrationHandler>::Genesis {
        Default::default()
    }
}

struct EmptyHistory;

impl history::HistoryHost for EmptyHistory {
    fn consensus_state_at(&self, _height: u64) -> Result<ConsensusState, history::Error> {
        Err(history::Error::FailedToFetchBlock)
    }

    fn consensus_events_at(
        &self,
        _height: u64,
        _kind: EventKind,
    ) -> Result<Vec<Event>, history::Error> {
        Err(history::Error::FailedToFetchEvents)
    }
}

struct EmptyHostTree;

impl read_syncer::HostTree for EmptyHostTree {
    fn tree(&self, _root: mkvs::Root) -> mkvs::Tree {
        mkvs::Tree::builder()
            .with_root_type(mkvs::RootType::State)
            .build(Box::new(mkvs::sync::NoopReadSyncer))
    }
}

/// Mock dispatch context factory.
pub struct Mock {
    pub host_info: HostInfo,
    pub read_syncer: Box<dyn HostTree>,
    pub runtime_header: roothash::Header,
    pub runtime_round_results: roothash::RoundResults,
    pub consensus_state: ConsensusState,
    pub history: Box<dyn history::HistoryHost>,
    pub epoch: beacon::EpochTime,
    pub rng: RootRng,

    pub max_messages: u32,
}

impl Mock {
    /// Create a new mock dispatch context.
    pub fn create_ctx(&mut self) -> RuntimeBatchContext<'_, EmptyRuntime> {
        self.create_ctx_for_runtime(Mode::ExecuteTx, false)
    }

    pub fn create_check_ctx(&mut self) -> RuntimeBatchContext<'_, EmptyRuntime> {
        self.create_ctx_for_runtime(Mode::CheckTx, false)
    }

    /// Create a new mock dispatch context.
    pub fn create_ctx_for_runtime<R: Runtime>(
        &mut self,
        mode: Mode,
        confidential: bool,
    ) -> RuntimeBatchContext<'_, R> {
        RuntimeBatchContext::new(
            mode,
            &self.host_info,
            &self.read_syncer,
            if confidential {
                Some(Box::new(MockKeyManagerClient::new()) as Box<dyn KeyManager>)
            } else {
                None
            },
            &self.runtime_header,
            &self.runtime_round_results,
            &self.consensus_state,
            &self.history,
            self.epoch,
            &self.rng,
            self.max_messages,
        )
    }

    /// Create an instance with the given local configuration.
    pub fn with_local_config(local_config: BTreeMap<String, cbor::Value>) -> Self {
        // Ensure a current store is always available during tests. Note that one can always use a
        // different store by calling CurrentStore::enter explicitly.
        CurrentStore::init_local_fallback();

        let consensus_tree = mkvs::Tree::builder()
            .with_root_type(mkvs::RootType::State)
            .build(Box::new(mkvs::sync::NoopReadSyncer));

        let read_syncer: Box<dyn HostTree> = Box::new(EmptyHostTree);

        Self {
            host_info: HostInfo {
                runtime_id: Namespace::default(),
                consensus_backend: "mock".to_string(),
                consensus_protocol_version: Version::default(),
                consensus_chain_context: "test".to_string(),
                local_config,
            },
            read_syncer: read_syncer,
            runtime_header: roothash::Header::default(),
            runtime_round_results: roothash::RoundResults::default(),
            consensus_state: ConsensusState::new(1, consensus_tree),
            history: Box::new(EmptyHistory),
            epoch: 1,
            rng: RootRng::new(),
            max_messages: 32,
        }
    }
}

impl Default for Mock {
    fn default() -> Self {
        let local_config_for_tests = configmap! {
            // Allow expensive gas estimation and expensive queries so they can be tested.
            "estimate_gas_by_simulating_contracts" => true,
            "allowed_queries" => vec![
                configmap! {"all_expensive" => true}
            ],
        };
        Self::with_local_config(local_config_for_tests)
    }
}

/// Create an empty MKVS store.
pub fn empty_store() -> MKVSStore<mkvs::OverlayTree<mkvs::Tree>> {
    let root = mkvs::OverlayTree::new(
        mkvs::Tree::builder()
            .with_root_type(mkvs::RootType::State)
            .build(Box::new(mkvs::sync::NoopReadSyncer)),
    );
    MKVSStore::new(root)
}

/// Create a new mock transaction.
pub fn transaction() -> transaction::Transaction {
    transaction::Transaction {
        version: 1,
        call: transaction::Call {
            format: transaction::CallFormat::Plain,
            method: "mock".to_owned(),
            body: cbor::Value::Simple(cbor::SimpleValue::NullValue),
            ..Default::default()
        },
        auth_info: transaction::AuthInfo {
            signer_info: vec![],
            fee: transaction::Fee {
                amount: Default::default(),
                gas: 1_000_000,
                consensus_messages: 32,
            },
            ..Default::default()
        },
    }
}

/// Options that can be used during mock signer calls.
#[derive(Clone, Debug)]
pub struct CallOptions {
    /// Transaction fee.
    pub fee: transaction::Fee,
}

impl Default for CallOptions {
    fn default() -> Self {
        Self {
            fee: transaction::Fee {
                amount: Default::default(),
                gas: 1_000_000,
                consensus_messages: 0,
            },
        }
    }
}

/// A mock signer for use during tests.
pub struct Signer {
    nonce: u64,
    sigspec: SignatureAddressSpec,
}

impl Signer {
    /// Create a new mock signer using the given nonce and signature spec.
    pub fn new(nonce: u64, sigspec: SignatureAddressSpec) -> Self {
        Self { nonce, sigspec }
    }

    /// Address specification for this signer.
    pub fn sigspec(&self) -> &SignatureAddressSpec {
        &self.sigspec
    }

    /// Dispatch a call to the given method.
    pub fn call<C, B>(&mut self, ctx: &mut C, method: &str, body: B) -> dispatcher::DispatchResult
    where
        C: BatchContext,
        B: cbor::Encode,
    {
        self.call_opts(ctx, method, body, Default::default())
    }

    /// Dispatch a call to the given method with the given options.
    pub fn call_opts<C, B>(
        &mut self,
        ctx: &mut C,
        method: &str,
        body: B,
        opts: CallOptions,
    ) -> dispatcher::DispatchResult
    where
        C: BatchContext,
        B: cbor::Encode,
    {
        let tx = transaction::Transaction {
            version: 1,
            call: transaction::Call {
                format: transaction::CallFormat::Plain,
                method: method.to_owned(),
                body: cbor::to_value(body),
                ..Default::default()
            },
            auth_info: transaction::AuthInfo {
                signer_info: vec![transaction::SignerInfo::new_sigspec(
                    self.sigspec.clone(),
                    self.nonce,
                )],
                fee: opts.fee,
                ..Default::default()
            },
        };

        let result = dispatcher::Dispatcher::<C::Runtime>::dispatch_tx(ctx, 1024, tx, 0)
            .expect("dispatch should work");

        // Increment the nonce.
        self.nonce += 1;

        result
    }

    /// Dispatch a query to the given method.
    pub fn query<C, A, R>(&self, ctx: &mut C, method: &str, args: A) -> Result<R, RuntimeError>
    where
        C: BatchContext,
        A: cbor::Encode,
        R: cbor::Decode,
    {
        let result =
            dispatcher::Dispatcher::<C::Runtime>::dispatch_query(ctx, method, cbor::to_vec(args))?;
        Ok(cbor::from_slice(&result).expect("result should decode correctly"))
    }
}
