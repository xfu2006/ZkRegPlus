#!/usr/bin/env python3
"""ALL_T1020 checks of the generators' missing-data and dry paths.
Run from this folder: python3 -m unittest test_generators (not by RUNALL)."""
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import common                                   # noqa: E402
import dna_reef_bora                            # noqa: E402
import gen_compare_measured                     # noqa: E402
import gen_overall_perf                         # noqa: E402
import gen_zombie_table                         # noqa: E402

LOG = """[job 0] -- prove_step cost: i: 1, circ_id: 0, stmt_len: 9, wtns size: 9 1000 ms
[job 0] -- prove_step cost: i: 2, circ_id: 1, stmt_len: 9, wtns size: 9 2000 ms
[job 0] Phase 1 step 7: PROVE STEPS done for n_steps: 2 3 s
[job 0] -- prove_step cost: i: 1, circ_id: 0, stmt_len: 9, wtns size: 9 7000 ms
[job 1] -- prove_step cost: i: 1, circ_id: 0, stmt_len: 9, wtns size: 9 500 ms
[job 1] Phase 1 step 7: PROVE STEPS done for n_steps: 1 1 s
"""


class GeneratorTest(unittest.TestCase):
    def test_circuit_step_times_phase1_only(self):
        with tempfile.NamedTemporaryFile("w", suffix=".log") as f:
            f.write(LOG)
            f.flush()
            self.assertEqual(common.circuit_step_times(f.name),
                             {0: (2, 1.5), 1: (1, 2.0)})

    def test_dry_reads_dry_names(self):
        with tempfile.TemporaryDirectory() as td, \
             mock.patch.object(common, "FIG_DRY", True), \
             mock.patch.object(common, "raw_data_root",
                               return_value=Path(td)):
            d = Path(td) / common.SERVER_TO_USE
            d.mkdir()
            (d / "x.dry.log").write_text("")
            self.assertEqual(common.server_file("x.log"), d / "x.dry.log")
            self.assertEqual(common.server_file("y.log"), d / "y.log")

    def test_source_line_dates_each_input(self):
        """W807 (h): each input with its mtime date, parts first, else
        missing, so an August file left in place shows."""
        with tempfile.TemporaryDirectory() as td, \
             mock.patch.object(common, "get_paper_root",
                               return_value=Path(td)):
            d = Path(td) / "data" / "raw_data" / "jet1tb"
            d.mkdir(parents=True)
            for n in ("full_dlp.tgz", "full_dlp.part1.tgz"):
                (d / n).write_text("")
                os.utime(d / n, (1755734400, 1755734400))  # 2025-08-21 UTC
            self.assertEqual(
                common.source_line(d / "full_dlp.tgz", d / "full_dna.tgz"),
                "% SOURCE: data/raw_data/jet1tb/full_dlp.part1.tgz@2025-08-21"
                ", data/raw_data/jet1tb/full_dna.tgz@missing")

    def test_reef_always_from_jet1tb(self):
        """W807 (g): Reef stays jet1tb/ whatever BORA_FIG_SERVER names."""
        with mock.patch.object(common, "SERVER_TO_USE", "jet1tb_v2"):
            self.assertEqual(common.reef_file().parent.name, "jet1tb")

    def test_missing_logs_print_markers_not_fallbacks(self):
        t9 = dna_reef_bora.build_table(None, None)
        self.assertEqual(t9.count(common.MISSING), 3)
        self.assertNotIn("Estimate", t9)
        t3 = gen_overall_perf.build_table({"Mal": None, "Dna": None,
                                           "Dlp": None})
        self.assertNotIn("1{,}152", t3)
        self.assertNotIn("approx}29", t3)

    def test_pending_same_sample_rows_omitted(self):
        sweep = {a: {"n": 1, "total_r1cs": a, "total_proof_bytes": 1}
                 for a in gen_zombie_table.ARMS}
        t10 = gen_zombie_table.build_table(sweep, {})
        self.assertNotIn("Prove/e-mail", t10)      # no D5: R1CS only
        same = {1000: {"emails": 32, "proofs": 1, "prove_s": 1.0,
                       "verify_s": 0.1}}
        t10 = gen_zombie_table.build_table(sweep, same)
        self.assertIn("    2,000 & 1 & 2,000 &", t10)      # compile row kept
        self.assertIn("% OMITTED timing arm 2000", t10)
        self.assertNotIn("Population-weighted", t10)
        self.assertNotIn("derived row", t10)       # B2: caption silent too
        full = {a: same[1000] for a in gen_zombie_table.ARMS}
        t10 = gen_zombie_table.build_table(sweep, full)
        self.assertNotIn("derived row", t10)       # Q5a: no mix, no row
        t10 = gen_zombie_table.build_table(
            sweep, full, {1000: 0.25, 2000: 0.25, 4000: 0.5})
        self.assertIn(r"25.0\%/25.0\%/50.0\%", t10)
        self.assertIn("derived row", t10)
        self.assertIn("Population-weighted", t10)
        w203 = gen_compare_measured.build_table(None, None, same, {})
        self.assertNotIn("Dlp", w203.split("OMITTED Dlp 4000 B")[1])
        self.assertIn("% OMITTED Dlp 1000 B", w203)
        self.assertNotIn("all arms", w203)         # Q4: needs every arm
        arms = gen_compare_measured.ARMS
        w203 = gen_compare_measured.build_table(
            None, None, {a: same[1000] for a in arms},
            {a: (32, 64.0) for a in arms})
        self.assertIn(r"all arms & Zombie, 96 e-mails", w203)
        self.assertIn(r"BORA, 96 e-mails", w203)
        self.assertIn(r"$2.0$\,s", w203)            # 192 s over 96 e-mails


if __name__ == "__main__":
    unittest.main()
