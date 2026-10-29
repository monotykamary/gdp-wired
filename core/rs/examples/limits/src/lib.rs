//! Fixtures for the Rust front end's tests (core/extract-rs.test.ts).
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase { Idle = 0, Running = 1, Done = 2 }

/// A u8 budget: `+` panics past 255, the wrapping and checked forms don't.
#[derive(Default)]
pub struct Budget { spent: u8, limit: u8, laps: u8, phase: Option<u32> }

impl Budget {
    pub fn new(limit: u8) -> Self { Self { spent: 0, limit, laps: 0, phase: None } }
    pub fn spend(&mut self, n: u8) -> Result<(), String> {
        if self.spent + n > self.limit { return Err("over".to_string()); }
        self.spent += n;
        Ok(())
    }
    pub fn lap(&mut self) { self.laps = self.laps.wrapping_add(1); }
    pub fn try_spend(&mut self, n: u8) -> bool {
        match self.spent.checked_add(n) {
            Some(s) if s <= self.limit => { self.spent = s; true }
            _ => false,
        }
    }
    pub fn mark(&mut self, p: u32) -> u32 { let old = self.phase.unwrap_or(0); self.phase = Some(p); old }
}

pub struct Job { phase: Phase, hits: AtomicU32 }

impl Job {
    pub fn new() -> Self { Job { phase: Phase::Idle, hits: AtomicU32::new(0) } }
    pub fn start(&mut self) -> bool {
        if self.phase != Phase::Idle { return false; }
        self.phase = Phase::Running;
        self.hits.fetch_add(1, Ordering::SeqCst);
        true
    }
    pub fn finish(&mut self) -> Result<u32, String> {
        match self.phase {
            Phase::Running => { self.phase = Phase::Done; Ok(self.phase as u32) }
            _ => Err("not running".into()),
        }
    }
}

pub struct Tally { total: u64 }
impl Tally {
    pub fn new() -> Self { Tally { total: 0 } }
    pub fn add_all(&mut self, xs: u64) { for _ in 0..xs { self.total += 1; } }
}

pub struct Ledger { balances: HashMap<u32, u64> }
impl Ledger { pub fn new() -> Self { Ledger { balances: HashMap::new() } } }
