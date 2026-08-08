# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code.
# Purpose: perc-parameterized dry run of run_zombie.py. Monkeypatches
#          list_policy_names() to an evenly-spaced perc% subset of the
#          policy corpus, and VEC_SIZE to a smaller, proximity-safe sweep
#          ([700, 800, 1000] instead of the real [1000, 2000, 4000]),
#          then delegates entirely to run_zombie.main(). Zero edits to
#          run_zombie.py itself -- the patch is a runtime attribute
#          override on the already-imported module.
# -------------------------------------------

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_zombie  # noqa: E402

DRY_VEC_SIZE = [700, 800, 1000]


def evenly_spaced_subset(items, perc):
    n = len(items)
    if n == 0 or perc <= 0:
        return []
    keep = min(n, max(1, (n * perc + 99) // 100))
    step = n / keep
    return [items[min(n - 1, round(i * step))] for i in range(keep)]


def _make_dry_list_policy_names(perc, original_fn):
    def dry_list_policy_names(full_dir):
        return evenly_spaced_subset(original_fn(full_dir), perc)
    return dry_list_policy_names


def main(argv=None):
    argv = sys.argv if argv is None else argv
    if len(argv) < 2:
        raise SystemExit("usage: dry_run_zombie.py <perc>")
    try:
        perc = int(argv[1])
    except ValueError:
        raise SystemExit("dry_run_zombie.py: perc must be an integer, "
                          "got %r" % argv[1])

    run_zombie.VEC_SIZE = DRY_VEC_SIZE
    run_zombie.list_policy_names = _make_dry_list_policy_names(
        perc, run_zombie.list_policy_names)
    return run_zombie.main()


if __name__ == "__main__":
    sys.exit(main())
