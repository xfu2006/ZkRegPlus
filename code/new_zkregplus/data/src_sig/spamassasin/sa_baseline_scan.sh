#!/usr/bin/env bash
#
# Baseline SpamAssassin scan of the Enron corpus using the
# downloaded sa-update ruleset. Pure regex evaluation:
#   - Unix domain socket (no TCP / no privileged ports / no network).
#   - -L plus `dns_available no` plus `skip_rbl_checks 1` so SA never
#     issues a DNS query; tflags-net / DNSBL / URIBL rules go inert.
#   - -x and an empty siteconfigpath so /etc/mail/spamassassin and
#     ~/.spamassassin are excluded; only $WORK is read.
# Emits TSV of spam-flagged messages:
#   "<score>/<threshold>\t<path>"
#
# Usage:
#   ./sa_baseline_scan.sh
#   OUT=/tmp/foo.tsv JOBS=16 ./sa_baseline_scan.sh
#
# Requires: spamd, spamc on PATH (apt install spamassassin).

set -u

HERE=$(cd "$(dirname "$0")" && pwd)
RULES=${RULES:-$HERE/original_src/updates_spamassassin_org}
ENRON=${ENRON:-$HERE/../../samples/email/src/maildir}
WORK=${WORK:-/tmp/sa_baseline_full}
OUT=${OUT:-/tmp/enron_flagged.tsv}
LOG=${LOG:-/tmp/spamd.log}
PIDFILE=${PIDFILE:-/tmp/spamd.pid}
SOCK=${SOCK:-/tmp/spamd.sock}
JOBS=${JOBS:-$(nproc)}

# --- sanity checks --------------------------------------------------

[ -d "$RULES" ] || {
  echo "RULES dir not found: $RULES" >&2; exit 1; }
[ -d "$ENRON" ] || {
  echo "ENRON dir not found: $ENRON" >&2; exit 1; }
command -v spamd >/dev/null || {
  echo "spamd not on PATH (apt install spamassassin)" >&2
  exit 1; }
command -v spamc >/dev/null || {
  echo "spamc not on PATH (apt install spamassassin)" >&2
  exit 1; }

# --- assemble configpath: downloaded .cf + system .pre --------------

mkdir -p "$WORK" /tmp/sa_empty
rm -f "$WORK"/*.cf "$WORK"/*.pre
cp "$RULES"/*.cf "$WORK"/
cp /etc/spamassassin/*.pre "$WORK"/ 2>/dev/null || true
# Force SA to assume no DNS / network — pure regex evaluation only.
# Any rule with `tflags net` or DNS-plugin eval becomes inert.
cat > "$WORK"/local.cf <<'EOF'
dns_available no
skip_rbl_checks 1
EOF
N_CF=$(ls -1 "$WORK"/*.cf 2>/dev/null | wc -l)
N_PRE=$(ls -1 "$WORK"/*.pre 2>/dev/null | wc -l)
echo "configpath: $WORK ($N_CF .cf, $N_PRE .pre)"

# --- start spamd (reuse if already running on our pidfile) ----------

STARTED_SPAMD=0
cleanup() {
  if [ "$STARTED_SPAMD" = "1" ] && [ -f "$PIDFILE" ] \
       && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    kill "$(cat "$PIDFILE")"
    rm -f "$SOCK"
    echo "spamd stopped."
  fi
}
trap cleanup EXIT INT TERM

if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
  echo "spamd already running (pid $(cat "$PIDFILE")), reusing."
else
  echo "starting spamd with $JOBS workers (unix socket $SOCK)..."
  rm -f "$SOCK"
  spamd -L -x -d \
        --siteconfigpath=/tmp/sa_empty \
        --configpath="$WORK" \
        --max-children="$JOBS" \
        --pidfile="$PIDFILE" \
        --socketpath="$SOCK" \
        --socketowner="$USER" \
        --socketmode=0600 \
        -s "$LOG" || {
    echo "spamd failed to start; see $LOG" >&2
    exit 1; }
  STARTED_SPAMD=1
  # wait for daemon to accept connections (max ~30s)
  for _ in $(seq 1 30); do
    echo "Subject: warmup" \
      | spamc -U "$SOCK" -t 5 > /dev/null 2>&1 && break
    sleep 1
  done
fi

# --- parallel scan --------------------------------------------------

echo "counting messages under $ENRON ..."
TOTAL=$(find "$ENRON" -type f | wc -l)
echo "total messages: $TOTAL"
: > "$OUT"

START=$(date +%s)
find "$ENRON" -type f -print0 \
  | xargs -0 -P "$JOBS" -I {} bash -c '
      out=$(spamc -U "'"$SOCK"'" -c -s 5000000 < "$0" 2>/dev/null)
      [ $? -eq 1 ] && printf "%s\t%s\n" "$out" "$0"
      exit 0
    ' {} >> "$OUT"
END=$(date +%s)

FLAGGED=$(wc -l < "$OUT")
echo "done in $((END - START))s. flagged: $FLAGGED / $TOTAL"
echo "output: $OUT"
echo "top 10 by score:"
sort -t$'\t' -k1,1 -gr "$OUT" | head -10
