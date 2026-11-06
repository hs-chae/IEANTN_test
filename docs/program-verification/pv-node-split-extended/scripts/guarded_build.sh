#!/usr/bin/env bash
# guarded_build.sh <log> <dir> <cmd...>
# Runs <cmd> in <dir> in its own process group under GNU time; a sampler records every 2 s the number of
# `lean` processes and their summed RSS (descendants of the build), MemAvailable and free disk on <dir>'s fs.
# It kills the whole group if MemAvailable < MEM_FLOOR_GB (default 300) or free disk < DISK_FLOOR_GB (default 60).
# Prints one summary line to stdout and appends it to <log>.summary.
set -u
LOG=$1; DIR=$2; shift 2
MEM_FLOOR_GB=${MEM_FLOOR_GB:-300}; DISK_FLOOR_GB=${DISK_FLOOR_GB:-60}
start=$(date +%s.%N)
( cd "$DIR" && exec setsid /usr/bin/time -v "$@" ) > "$LOG" 2>&1 &
PID=$!
sleep 0.5
PGID=$(ps -o pgid= -p $PID 2>/dev/null | tr -d ' ')
peak_n=0; peak_rss=0; min_avail=999999; killed=""
while kill -0 $PID 2>/dev/null; do
  avail=$(awk '/MemAvailable/{printf "%d", $2/1048576}' /proc/meminfo)
  disk=$(df -BG --output=avail "$DIR" | tail -1 | tr -dc 0-9)
  if [ -n "$PGID" ]; then
    read n rss < <(ps -eo pgid=,rss=,comm= | awk -v g=$PGID '$1==g && $3=="lean"{n++; s+=$2} END{printf "%d %d\n", n, s/1048576}')
  else n=0; rss=0; fi
  [ "$n" -gt "$peak_n" ] && peak_n=$n; [ "$rss" -gt "$peak_rss" ] && peak_rss=$rss; [ "$avail" -lt "$min_avail" ] && min_avail=$avail
  if [ "$avail" -lt "$MEM_FLOOR_GB" ] || [ "$disk" -lt "$DISK_FLOOR_GB" ]; then
    killed="KILLED(avail=${avail}G disk=${disk}G)"; kill -TERM -- -$PGID 2>/dev/null; sleep 5; kill -KILL -- -$PGID 2>/dev/null; break; fi
  sleep 2
done
wait $PID; rc=$?
end=$(date +%s.%N)
maxrss_kb=$(grep -m1 'Maximum resident set size' "$LOG" | awk '{print $NF}')
line="$(date -u +%FT%TZ) rc=$rc wall=$(printf '%.1f' $(echo "$end - $start" | bc))s max_single_rss=$(( ${maxrss_kb:-0} / 1048576 ))GB peak_lean_procs=$peak_n peak_sum_lean_rss=${peak_rss}GB min_MemAvailable=${min_avail}GB ${killed} cmd=[$*] dir=$DIR"
echo "$line" | tee -a "$LOG.summary"
