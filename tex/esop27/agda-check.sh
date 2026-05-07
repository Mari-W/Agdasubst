#!/usr/bin/env bash
# agda-check.sh — CLI wrapper around `agda` and `agda --interaction`
#
# Subcommands:
#   check <file>                            — typecheck one file
#   check-all                                — typecheck all entry points
#   goals <file>                             — list all holes + types
#   goal <file> <id>                         — show goal type + context for hole N
#   infer <file> <id> <expr>                 — infer type of expr in hole N's ctx
#   normalize <file> <id> <expr>             — normal form of expr in hole N's ctx
#   clean                                    — delete .agdai interface files
#
# Configure your project-specific paths in the CONFIG section below.

set -u

# ========================================================================
# CONFIG — edit these for your project
# ========================================================================

# Include paths passed to agda (directories containing .agda-lib or sources).
# Sources live in src/, so agda must resolve module names relative to that
# directory (e.g. src/Foo.agda ↔ module Foo).
AGDA_INCLUDES=(".")

# Entry-point files for `check-all`. List the top modules of your project.
# `check-all` will typecheck these; Agda will pull in their dependencies.
ENTRY_POINTS=(
    "SystemF.agda"
    "SystemF2.agda"
)

# Path to the agda binary.
AGDA=${AGDA:-agda}

# ========================================================================
# Internals
# ========================================================================

die() { echo "agda-check: $*" >&2; exit 2; }

# Build the include-path arguments for agda CLI invocations.
agda_include_args() {
    local args=()
    for p in "${AGDA_INCLUDES[@]}"; do
        args+=(-i "$p")
    done
    printf '%s\n' "${args[@]}"
}

# Absolute path helper (Agda's interaction mode requires absolute paths).
abspath() {
    if command -v realpath >/dev/null 2>&1; then
        realpath "$1"
    else
        # POSIX fallback
        (cd "$(dirname "$1")" 2>/dev/null && printf '%s/%s\n' "$PWD" "$(basename "$1")")
    fi
}

# Send one IOTCM command to agda --interaction and print its raw output.
# $1 = absolute file path, $2 = interaction command (without the IOTCM wrapper)
send_iotcm() {
    local absfile=$1
    local cmd=$2
    # Feed a Cmd_load first so agda knows about the file, then the command.
    # We use `NonInteractive Direct` which prints responses to stdout.
    {
        printf 'IOTCM "%s" NonInteractive Direct (Cmd_load "%s" [%s])\n' \
            "$absfile" "$absfile" "$(printf '"%s",' "${AGDA_INCLUDES[@]}" | sed 's/,$//')"
        printf 'IOTCM "%s" NonInteractive Direct (%s)\n' "$absfile" "$cmd"
    } | "$AGDA" --interaction 2>&1
}

# Extract the content of an (agda2-info-action "<TITLE>" "<BODY>" ...) sexp.
# $1 = title to match (e.g. "*All Goals*", "*Goal type etc.*")
# Reads response text from stdin.
extract_info() {
    local title=$1
    # Agda emits lines like: (agda2-info-action "*All Goals*" "body\nbody2" nil)
    # Use python for reliable unescaping of the body string.
    python3 - "$title" <<'PYEOF'
import sys, re
title = sys.argv[1]
data = sys.stdin.read()
# Non-greedy match of the escaped string body. Handles \" and \\ inside.
pat = r'\(agda2-info-action\s+"' + re.escape(title) + r'"\s+"((?:[^"\\]|\\.)*)"'
m = re.findall(pat, data)
if not m:
    sys.exit(0)
for body in m:
    # Unescape standard sequences.
    out = body.encode('utf-8').decode('unicode_escape')
    print(out)
PYEOF
}

# ========================================================================
# Subcommands
# ========================================================================

cmd_check() {
    [[ $# -eq 1 ]] || die "usage: check <file.agda>"
    local file=$1
    [[ -f $file ]] || die "no such file: $file"
    # Plain CLI typecheck. Errors go to stderr in file:line:col: form.
    "$AGDA" $(agda_include_args) "$file"
}

cmd_check_all() {
    if [[ ${#ENTRY_POINTS[@]} -eq 0 ]]; then
        die "check-all: no ENTRY_POINTS configured. Edit $(basename "$0") and list your top modules."
    fi
    local rc=0
    for ep in "${ENTRY_POINTS[@]}"; do
        echo "=== $ep ==="
        "$AGDA" $(agda_include_args) "$ep" || rc=$?
    done
    return $rc
}

cmd_goals() {
    [[ $# -eq 1 ]] || die "usage: goals <file.agda>"
    local file
    file=$(abspath "$1") || die "cannot resolve path: $1"
    [[ -f $file ]] || die "no such file: $file"
    # A Cmd_load alone causes agda to emit *All Goals* in the response stream.
    # We send a harmless Cmd_metas as the "second" command to force a flush.
    local out
    out=$(send_iotcm "$file" "Cmd_metas")
    # Check for load errors first.
    local err
    err=$(printf '%s\n' "$out" | extract_info "*Error*")
    if [[ -n $err ]]; then
        echo "LOAD ERROR:"
        echo "$err"
        return 1
    fi
    # Prefer *All Goals* (only holes) over *All Done* (nothing to do).
    local goals
    goals=$(printf '%s\n' "$out" | extract_info "*All Goals*")
    if [[ -n $goals ]]; then
        echo "$goals"
    else
        echo "(no open goals)"
    fi
}

cmd_goal() {
    [[ $# -eq 2 ]] || die "usage: goal <file.agda> <goal-id>"
    local file
    file=$(abspath "$1") || die "cannot resolve path: $1"
    local id=$2
    [[ -f $file ]] || die "no such file: $file"
    [[ $id =~ ^[0-9]+$ ]] || die "goal id must be a non-negative integer"
    # Cmd_goal_type_context prints both the goal type and the local context.
    # `Simplified` = normal "simplified" rewriting (matches agda-mode default).
    # `noRange` works when the goal id is given; we pass an empty range.
    local out
    out=$(send_iotcm "$file" \
        "Cmd_goal_type_context Simplified $id noRange \"\"")
    local body
    body=$(printf '%s\n' "$out" | extract_info "*Goal type etc.*")
    if [[ -z $body ]]; then
        # Fall back: maybe load failed.
        local err
        err=$(printf '%s\n' "$out" | extract_info "*Error*")
        if [[ -n $err ]]; then
            echo "ERROR:"
            echo "$err"
            return 1
        fi
        echo "(no goal info returned — is goal id $id valid? try: goals $1)"
        return 1
    fi
    echo "$body"
}

cmd_infer() {
    [[ $# -eq 3 ]] || die "usage: infer <file.agda> <goal-id> <expr>"
    local file
    file=$(abspath "$1") || die "cannot resolve path: $1"
    local id=$2 expr=$3
    [[ -f $file ]] || die "no such file: $file"
    [[ $id =~ ^[0-9]+$ ]] || die "goal id must be a non-negative integer"
    # Escape backslashes and quotes for the IOTCM string literal.
    local esc=${expr//\\/\\\\}
    esc=${esc//\"/\\\"}
    local out
    out=$(send_iotcm "$file" \
        "Cmd_infer Simplified $id noRange \"$esc\"")
    local body
    body=$(printf '%s\n' "$out" | extract_info "*Inferred Type*")
    if [[ -z $body ]]; then
        local err
        err=$(printf '%s\n' "$out" | extract_info "*Error*")
        [[ -n $err ]] && { echo "ERROR:"; echo "$err"; return 1; }
        echo "(no type returned)"
        return 1
    fi
    echo "$body"
}

cmd_normalize() {
    [[ $# -eq 3 ]] || die "usage: normalize <file.agda> <goal-id> <expr>"
    local file
    file=$(abspath "$1") || die "cannot resolve path: $1"
    local id=$2 expr=$3
    [[ -f $file ]] || die "no such file: $file"
    [[ $id =~ ^[0-9]+$ ]] || die "goal id must be a non-negative integer"
    local esc=${expr//\\/\\\\}
    esc=${esc//\"/\\\"}
    # DefaultCompute = normal reduction (no ignoring abstract, no head-only).
    local out
    out=$(send_iotcm "$file" \
        "Cmd_compute DefaultCompute $id noRange \"$esc\"")
    local body
    body=$(printf '%s\n' "$out" | extract_info "*Normal Form*")
    if [[ -z $body ]]; then
        local err
        err=$(printf '%s\n' "$out" | extract_info "*Error*")
        [[ -n $err ]] && { echo "ERROR:"; echo "$err"; return 1; }
        echo "(no normal form returned)"
        return 1
    fi
    echo "$body"
}

# ========================================================================
# Dispatch
# ========================================================================

usage() {
    sed -n '2,14p' "$0"
}

main() {
    [[ $# -ge 1 ]] || { usage; exit 1; }
    local sub=$1; shift
    case $sub in
        check)      cmd_check "$@" ;;
        check-all)  cmd_check_all "$@" ;;
        goals)      cmd_goals "$@" ;;
        goal)       cmd_goal "$@" ;;
        infer)      cmd_infer "$@" ;;
        normalize)  cmd_normalize "$@" ;;
        -h|--help)  usage ;;
        *)          usage; exit 1 ;;
    esac
}

main "$@"