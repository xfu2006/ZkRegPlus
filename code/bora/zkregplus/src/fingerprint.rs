//! Flag-off regression fingerprint for the SDE-aggressive milestones.
//! A structured snapshot (DB universe + per-circuit r1cs dims and IO
//! arity) of a non-aggressive run; each milestone diffs it against the
//! M0 baseline to prove the flag-off circuit shape is unchanged.

use std::collections::BTreeMap;

/// One run's fingerprint: a sorted label -> value map. Stored as text,
/// diffed field-by-field (not a raw-text compare).
#[derive(Clone, Debug, Default)]
pub struct RunFingerprint {
	pub fields: BTreeMap<String, u64>,
}

impl RunFingerprint {
	/// Fold raw sink pairs, keeping the LAST value per label (a circuit
	/// re-synthesized each step emits identical dims; keep one entry).
	pub fn from_sink(raw: &[(String, u64)]) -> Self {
		let mut fields = BTreeMap::new();
		for (k, v) in raw { fields.insert(k.clone(), *v); }
		Self { fields }
	}

	/// Field-by-field diff vs baseline: one line per added/removed/
	/// changed label. Empty = identical. This is the gate.
	pub fn diff(&self, base: &RunFingerprint) -> Vec<String> {
		let mut out = vec![];
		for (k, v) in &self.fields {
			match base.fields.get(k) {
				None => out.push(format!("ADDED   {} = {}", k, v)),
				Some(b) if b != v =>
					out.push(format!("CHANGED {}: {} -> {}", k, b, v)),
				_ => {}
			}
		}
		for k in base.fields.keys() {
			if !self.fields.contains_key(k) {
				out.push(format!("REMOVED {}", k));
			}
		}
		out
	}

	pub fn save(&self, path: &str) -> std::io::Result<()> {
		let mut s = String::new();
		for (k, v) in &self.fields { s.push_str(&format!("{} {}\n", k, v)); }
		std::fs::write(path, s)
	}

	pub fn load(path: &str) -> std::io::Result<Self> {
		let txt = std::fs::read_to_string(path)?;
		let mut fields = BTreeMap::new();
		for line in txt.lines() {
			let line = line.trim();
			if line.is_empty() { continue; }
			let mut it = line.rsplitn(2, ' ');
			let v = it.next().unwrap().parse::<u64>().unwrap();
			let k = it.next().unwrap().to_string();
			fields.insert(k, v);
		}
		Ok(Self { fields })
	}
}
