# Source this, then prefix a gh READ with gh_retry: three tries, 20s then 40s apart, through GitHub's transient 5xx
# (2026-11-04: a run list got 502 in run 41863141144 and failed the step). Never a dispatch: a `gh workflow run`
# answered 500 can still have landed, and firing it again cancels whatever queued meanwhile in a shared group
# (leanstral and headtohead share one, where a new pending run replaces the waiting one; Codex 20261104T225804993745Z).
gh_retry() {
  local i
  for i in 1 2 3; do
    "$@" && return 0
    [ "$i" = 3 ] && return 1
    echo "gh failed (try $i/3), retrying in $((20 * i))s: $*" >&2
    sleep $((20 * i))
  done
}
