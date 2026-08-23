# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code.
# Purpose: perc-parameterized dry run of eval_reef.py. Re-invokes the
#          same 6-call sequence as its __main__ block with a smaller,
#          perc-scaled sample_size (the per-category cap already
#          native to seq_run_categories() as a plain argument), so
#          fewer variants get run. Zero edits to eval_reef.py itself --
#          the only extra step mirrors the scaled sample_size back onto
#          the module so write_log()'s own banner text (which reads
#          the module global directly, not a parameter) stays accurate
#          about how many samples were actually taken.
# -------------------------------------------

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import eval_reef as m  # noqa: E402


def dry_sample_size(perc):
    return max(1, round(m.sample_size * perc / 100))


def main(argv=None):
    argv = sys.argv if argv is None else argv
    if len(argv) < 2:
        raise SystemExit("usage: dry_run_eval_reef.py <perc>")
    try:
        perc = int(argv[1])
    except ValueError:
        raise SystemExit("dry_run_eval_reef.py: perc must be an integer, "
                          "got %r" % argv[1])

    m.verify_tool_existence()
    m.setup()
    full_category = m.gen_assessment()
    pool = m.gen_sample_pool()
    dry_size = dry_sample_size(perc)
    m.sample_size = dry_size
    seq_run_results, discarded = m.seq_run_categories(
        pool, m.timeout, m.threshold_perc, dry_size, m.max_discard)
    m.write_log(seq_run_results, full_category, discarded)
    return 0


if __name__ == "__main__":
    sys.exit(main())
