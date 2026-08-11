# -------------------------------------------
# Creator: BORA Author. Implemented with Claude Code.
# Purpose: perc-parameterized dry run of run_zombie.py. Monkeypatches
#          list_policy_names() to an evenly-spaced perc% subset of the
#          policy corpus -- drawn from a pool first capped by .regex size
#          so peak RSS stays inside budget -- and VEC_SIZE to a smaller,
#          proximity-safe sweep ([700, 800, 1000] instead of the real
#          [1000, 2000, 4000]), then delegates entirely to
#          run_zombie.main(). Zero edits to run_zombie.py itself -- the
#          patch is a runtime attribute override on the imported module.
# -------------------------------------------

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_zombie  # noqa: E402

DRY_VEC_SIZE = [700, 800, 1000]

# Peak-RSS budget for the dry sweep, expressed as a .regex byte cap.
# RSS is driven by a policy's kws_len, for which the .regex size is a
# proxy (ratio ~2.05 in the heavy regime): 7032 B -> kws 3441 -> 22.5 GB
# measured. 7100 keeps the whole corpus but one 7526 B outlier that
# extrapolates to ~24.4 GB. Policies run in sequence, so peak RSS is the
# max over the sample -- capping the POOL bounds it independently of
# perc, which is then free to tune wall time alone.
DRY_MAX_REGEX_BYTES = 7100


def regex_bytes(full_dir, name):
    """Byte size of <full_dir>/<name>.regex, 0 when it cannot be stat'd.
    Names come from a directory listing, so a miss means a synthetic
    name in a test, never a real heavy policy."""
    try:
        return os.path.getsize(os.path.join(full_dir, name + ".regex"))
    except OSError:
        return 0


def under_size_cap(full_dir, names, max_bytes):
    """Drop policies whose .regex exceeds max_bytes -- the ones whose
    peak RSS would breach the dry-run budget."""
    return [n for n in names
            if regex_bytes(full_dir, n) <= max_bytes]


def evenly_spaced_subset(items, perc):
    n = len(items)
    if n == 0 or perc <= 0:
        return []
    keep = min(n, max(1, (n * perc + 99) // 100))
    step = n / keep
    return [items[min(n - 1, round(i * step))] for i in range(keep)]


def _make_dry_list_policy_names(perc, original_fn):
    def dry_list_policy_names(full_dir):
        names = under_size_cap(full_dir, original_fn(full_dir),
                                DRY_MAX_REGEX_BYTES)
        return evenly_spaced_subset(names, perc)
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
