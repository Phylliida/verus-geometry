#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"
CHECKOUT_ACTION_REF="${CHECKOUT_ACTION_REF:-actions/checkout@v4.2.2}"

usage() {
  cat <<'USAGE'
usage: ./scripts/check.sh [--require-verus] [--forbid-trusted-escapes] [--min-verified N] [--offline]

options:
  --require-verus           fail instead of skipping when Verus verification cannot run
  --forbid-trusted-escapes  fail if non-test source uses trusted proof escapes (`admit`, `assume`, verifier externals, `#[verifier::truncate]`, `#[verifier::exec_allows_no_decreases_clause]`, or `unsafe`)
  --min-verified N          fail if any Verus run reports fewer than N verified items
  --offline                 run cargo commands in offline mode (`cargo --offline`)
  -h, --help                show this help
USAGE
}

REQUIRE_VERUS=0
FORBID_TRUSTED_ESCAPES=0
OFFLINE=0
MIN_VERIFIED=""
LAST_VERIFIED_COUNT=""
while [[ "$#" -gt 0 ]]; do
  case "${1:-}" in
    --require-verus)
      REQUIRE_VERUS=1
      ;;
    --forbid-trusted-escapes)
      FORBID_TRUSTED_ESCAPES=1
      ;;
    --min-verified)
      if [[ "$#" -lt 2 ]]; then
        echo "error: --min-verified requires an integer argument"
        usage
        exit 1
      fi
      MIN_VERIFIED="${2:-}"
      if ! [[ "$MIN_VERIFIED" =~ ^[0-9]+$ ]]; then
        echo "error: --min-verified expects a nonnegative integer"
        usage
        exit 1
      fi
      shift
      ;;
    --offline)
      OFFLINE=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument '$1'"
      usage
      exit 1
      ;;
  esac
  shift
done

if [[ "$OFFLINE" == "1" ]]; then
  export CARGO_NET_OFFLINE=true
fi

CARGO_CMD=(cargo)
if [[ "$OFFLINE" == "1" ]]; then
  CARGO_CMD+=(--offline)
fi

require_command() {
  local cmd="$1"
  local hint="${2:-}"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "error: required command '$cmd' not found in PATH"
    if [[ -n "$hint" ]]; then
      echo "hint: $hint"
    fi
    exit 1
  fi
}

normalize_inline_command() {
  local cmd="$1"
  cmd="$(printf '%s' "$cmd" | tr '\t' ' ')"
  cmd="$(printf '%s' "$cmd" | sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//')"
  printf '%s' "$cmd"
}

extract_ci_check_command_from_workflow() {
  local workflow_file="$1"
  rg -No '\./scripts/check\.sh[^\n]*' "$workflow_file" \
    | rg -- '--require-verus' \
    | rg -- '--min-verified' \
    | head -n 1 || true
}

extract_ci_check_command_from_readme() {
  local readme_file="$1"
  rg -No '\./scripts/check\.sh[^\n`]*' "$readme_file" \
    | rg -- '--require-verus' \
    | rg -- '--min-verified' \
    | head -n 1 || true
}

extract_min_verified_arg() {
  local cmd="$1"
  printf '%s\n' "$cmd" \
    | rg -No -- '--min-verified[[:space:]]+[0-9]+' \
    | rg -No -- '[0-9]+' \
    | head -n 1 || true
}

extract_ci_toolchain_install_from_workflow() {
  local workflow_file="$1"
  rg -No 'rustup\s+toolchain\s+install\s+([[:graph:]]+)' -r '$1' "$workflow_file" \
    | head -n 1 || true
}

extract_ci_toolchain_default_from_workflow() {
  local workflow_file="$1"
  rg -No 'rustup\s+default\s+([[:graph:]]+)' -r '$1' "$workflow_file" \
    | head -n 1 || true
}

extract_named_workflow_step_block() {
  local workflow_file="$1"
  local step_name="$2"

  awk -v step_name="$step_name" '
    {
      if (in_step && $0 ~ /^[[:space:]]*- name:/) {
        exit
      }

      line = $0
      sub(/^[[:space:]]*- name:[[:space:]]*/, "", line)
      if (!in_step && line == step_name) {
        in_step = 1
      }

      if (in_step) {
        print $0
      }
    }
  ' "$workflow_file"
}

extract_top_level_permissions_block() {
  local workflow_file="$1"

  awk '
    /^permissions:[[:space:]]*$/ {
      in_permissions = 1
      print $0
      next
    }

    in_permissions && /^[^[:space:]]/ {
      exit
    }

    in_permissions {
      print $0
    }
  ' "$workflow_file"
}

extract_top_level_on_block() {
  local workflow_file="$1"

  awk '
    /^on:[[:space:]]*$/ {
      in_on = 1
      print $0
      next
    }

    in_on && /^[^[:space:]]/ {
      exit
    }

    in_on {
      print $0
    }
  ' "$workflow_file"
}

extract_on_event_block() {
  local on_block="$1"
  local event_name="$2"

  awk -v event_name="$event_name" '
    {
      if (in_event && $0 ~ /^[[:space:]]{2}[A-Za-z0-9_-]+:[[:space:]]*$/) {
        exit
      }

      line = $0
      sub(/^[[:space:]]+/, "", line)
      if (!in_event && line == event_name ":") {
        in_event = 1
      }

      if (in_event) {
        print $0
      }
    }
  ' <<<"$on_block"
}

extract_verify_job_block() {
  local workflow_file="$1"

  awk '
    /^jobs:[[:space:]]*$/ {
      in_jobs = 1
      next
    }

    in_jobs && /^[[:space:]]{2}verify:[[:space:]]*$/ {
      in_verify = 1
      print $0
      next
    }

    in_verify && /^[[:space:]]{2}[A-Za-z0-9_-]+:[[:space:]]*$/ {
      exit
    }

    in_verify {
      print $0
    }
  ' "$workflow_file"
}

check_workflow_step_fail_fast() {
  local step_name="$1"
  local step_block="$2"

  if printf '%s\n' "$step_block" | rg -q '^[[:space:]]+if:[[:space:]]'; then
    echo "error: workflow step '$step_name' must not set step-level if: gating"
    exit 1
  fi

  if printf '%s\n' "$step_block" | rg -q 'continue-on-error:[[:space:]]*true'; then
    echo "error: workflow step '$step_name' must not set continue-on-error: true"
    exit 1
  fi

  if ! printf '%s\n' "$step_block" | rg -q 'set[[:space:]]+-euo[[:space:]]+pipefail'; then
    echo "error: workflow step '$step_name' must set 'set -euo pipefail'"
    exit 1
  fi

  if printf '%s\n' "$step_block" | rg -q '\|\|[[:space:]]*true'; then
    echo "error: workflow step '$step_name' must not mask failures with '|| true'"
    exit 1
  fi
}

check_ci_workflow_trigger_coverage() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local on_block=""
  local pull_request_block=""
  local push_block=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  on_block="$(extract_top_level_on_block "$workflow_file")"
  if [[ -z "$on_block" ]]; then
    echo "error: workflow must declare a top-level on: block"
    echo "expected triggers: pull_request and push (branches: [main])"
    exit 1
  fi

  pull_request_block="$(extract_on_event_block "$on_block" "pull_request")"
  if [[ -z "$pull_request_block" ]]; then
    echo "error: workflow must include an unconditional pull_request trigger"
    exit 1
  fi

  push_block="$(extract_on_event_block "$on_block" "push")"
  if [[ -z "$push_block" ]]; then
    echo "error: workflow must include a push trigger"
    exit 1
  fi

  if ! printf '%s\n' "$push_block" | rg -q '^[[:space:]]+branches:[[:space:]]*$'; then
    echo "error: workflow push trigger must explicitly pin branches"
    printf '%s\n' "$push_block"
    exit 1
  fi

  if ! printf '%s\n' "$push_block" | rg -q '^[[:space:]]*-[[:space:]]*main[[:space:]]*$'; then
    echo "error: workflow push trigger must include branch 'main'"
    printf '%s\n' "$push_block"
    exit 1
  fi

  if printf '%s\n' "$on_block" | rg -q '^[[:space:]]+paths(-ignore)?:[[:space:]]*$'; then
    echo "error: workflow triggers must not use paths/paths-ignore filters that can skip strict checks"
    printf '%s\n' "$on_block"
    exit 1
  fi

  if printf '%s\n' "$on_block" | rg -q '^[[:space:]]+branches-ignore:[[:space:]]*$'; then
    echo "error: workflow triggers must not use branches-ignore filters"
    printf '%s\n' "$on_block"
    exit 1
  fi
}

check_ci_verify_job_execution_contract() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local verify_job_block=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  verify_job_block="$(extract_verify_job_block "$workflow_file")"
  if [[ -z "$verify_job_block" ]]; then
    echo "error: workflow must define a 'verify' job"
    exit 1
  fi

  if printf '%s\n' "$verify_job_block" | rg -q '^[[:space:]]{4}if:[[:space:]]'; then
    echo "error: workflow 'verify' job must not be conditionally gated with a job-level if"
    printf '%s\n' "$verify_job_block"
    exit 1
  fi

  if printf '%s\n' "$verify_job_block" | rg -q '^[[:space:]]{4}continue-on-error:[[:space:]]'; then
    echo "error: workflow 'verify' job must not set job-level continue-on-error"
    printf '%s\n' "$verify_job_block"
    exit 1
  fi

  if ! printf '%s\n' "$verify_job_block" | rg -q '^[[:space:]]{4}timeout-minutes:[[:space:]]*[0-9]+[[:space:]]*$'; then
    echo "error: workflow 'verify' job must declare an explicit timeout-minutes"
    printf '%s\n' "$verify_job_block"
    exit 1
  fi
}

check_ci_verify_runner_pinning() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local verify_job_block=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  verify_job_block="$(extract_verify_job_block "$workflow_file")"
  if [[ -z "$verify_job_block" ]]; then
    echo "error: workflow must define a 'verify' job"
    exit 1
  fi

  if printf '%s\n' "$verify_job_block" | rg -q '^[[:space:]]{4}runs-on:[[:space:]]*\$\{\{'; then
    echo "error: workflow 'verify' job runs-on must be statically pinned (no expression interpolation)"
    printf '%s\n' "$verify_job_block"
    exit 1
  fi

  if printf '%s\n' "$verify_job_block" | rg -q 'self-hosted'; then
    echo "error: workflow 'verify' job must not target self-hosted runners"
    printf '%s\n' "$verify_job_block"
    exit 1
  fi

  if ! printf '%s\n' "$verify_job_block" | rg -q '^[[:space:]]{4}runs-on:[[:space:]]*ubuntu-22\.04[[:space:]]*$'; then
    echo "error: workflow 'verify' job must pin runs-on to ubuntu-22.04"
    printf '%s\n' "$verify_job_block"
    exit 1
  fi
}

check_ci_workflow_permissions_hardening() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local permissions_block=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  permissions_block="$(extract_top_level_permissions_block "$workflow_file")"
  if [[ -z "$permissions_block" ]]; then
    echo "error: workflow must declare a top-level permissions block"
    echo "expected:"
    echo "permissions:"
    echo "  contents: read"
    exit 1
  fi

  if ! printf '%s\n' "$permissions_block" | rg -q '^[[:space:]]+contents:[[:space:]]*read[[:space:]]*$'; then
    echo "error: workflow permissions must include 'contents: read'"
    printf '%s\n' "$permissions_block"
    exit 1
  fi

  if printf '%s\n' "$permissions_block" | rg -q ':[[:space:]]*write([[:space:]]|$)'; then
    echo "error: workflow permissions block must not grant write permissions"
    printf '%s\n' "$permissions_block"
    exit 1
  fi

  if printf '%s\n' "$permissions_block" | rg -q ':[[:space:]]*(read-all|write-all)([[:space:]]|$)'; then
    echo "error: workflow permissions must avoid broad read-all/write-all grants"
    printf '%s\n' "$permissions_block"
    exit 1
  fi
}

check_ci_workflow_checkout_wiring() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local checkout_geometry_step=""
  local checkout_verus_step=""
  local checkout_algebra_step=""
  local checkout_linalg_step=""
  local checkout_geometry_line=""
  local checkout_verus_line=""
  local checkout_algebra_line=""
  local checkout_linalg_line=""
  local build_line=""
  local strict_line=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  checkout_geometry_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Checkout verus-geometry[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  checkout_verus_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Checkout Verus[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  checkout_algebra_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Checkout verus-algebra[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  checkout_linalg_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Checkout verus-linalg[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  build_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Build Verus tools[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  strict_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Run strict checks[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"

  if [[ -z "$checkout_geometry_line" || -z "$checkout_verus_line" || -z "$checkout_algebra_line" || -z "$checkout_linalg_line" ]]; then
    echo "error: required checkout steps missing in $workflow_file"
    echo "expected steps: 'Checkout verus-geometry', 'Checkout Verus', 'Checkout verus-algebra', and 'Checkout verus-linalg'"
    exit 1
  fi
  if [[ -z "$build_line" || -z "$strict_line" ]]; then
    echo "error: required workflow steps missing in $workflow_file"
    echo "expected steps: 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi
  if (( checkout_geometry_line >= build_line || checkout_geometry_line >= strict_line )); then
    echo "error: workflow checkout step order invalid for 'Checkout verus-geometry'"
    echo "expected it to run before 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi
  if (( checkout_verus_line >= build_line || checkout_verus_line >= strict_line )); then
    echo "error: workflow checkout step order invalid for 'Checkout Verus'"
    echo "expected it to run before 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi
  if (( checkout_algebra_line >= build_line || checkout_algebra_line >= strict_line )); then
    echo "error: workflow checkout step order invalid for 'Checkout verus-algebra'"
    echo "expected it to run before 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi
  if (( checkout_linalg_line >= build_line || checkout_linalg_line >= strict_line )); then
    echo "error: workflow checkout step order invalid for 'Checkout verus-linalg'"
    echo "expected it to run before 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi

  checkout_geometry_step="$(extract_named_workflow_step_block "$workflow_file" "Checkout verus-geometry")"
  checkout_verus_step="$(extract_named_workflow_step_block "$workflow_file" "Checkout Verus")"
  checkout_algebra_step="$(extract_named_workflow_step_block "$workflow_file" "Checkout verus-algebra")"
  checkout_linalg_step="$(extract_named_workflow_step_block "$workflow_file" "Checkout verus-linalg")"
  if [[ -z "$checkout_geometry_step" || -z "$checkout_verus_step" || -z "$checkout_algebra_step" || -z "$checkout_linalg_step" ]]; then
    echo "error: failed to parse required checkout step block(s) in $workflow_file"
    exit 1
  fi

  if ! printf '%s\n' "$checkout_geometry_step" | rg -Fq "uses: $CHECKOUT_ACTION_REF"; then
    echo "error: workflow 'Checkout verus-geometry' step must pin uses: $CHECKOUT_ACTION_REF"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_geometry_step" | rg -q 'path:[[:space:]]*verus-geometry'; then
    echo "error: workflow 'Checkout verus-geometry' step must set path: verus-geometry"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_geometry_step" | rg -q 'persist-credentials:[[:space:]]*false'; then
    echo "error: workflow 'Checkout verus-geometry' step must set persist-credentials: false"
    exit 1
  fi

  if ! printf '%s\n' "$checkout_verus_step" | rg -Fq "uses: $CHECKOUT_ACTION_REF"; then
    echo "error: workflow 'Checkout Verus' step must pin uses: $CHECKOUT_ACTION_REF"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_verus_step" | rg -q 'repository:[[:space:]]*verus-lang/verus'; then
    echo "error: workflow 'Checkout Verus' step must set repository: verus-lang/verus"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_verus_step" | rg -q 'path:[[:space:]]*verus'; then
    echo "error: workflow 'Checkout Verus' step must set path: verus"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_verus_step" | rg -q 'persist-credentials:[[:space:]]*false'; then
    echo "error: workflow 'Checkout Verus' step must set persist-credentials: false"
    exit 1
  fi

  if ! printf '%s\n' "$checkout_algebra_step" | rg -Fq "uses: $CHECKOUT_ACTION_REF"; then
    echo "error: workflow 'Checkout verus-algebra' step must pin uses: $CHECKOUT_ACTION_REF"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_algebra_step" | rg -q 'repository:[[:space:]]*Phylliida/verus-algebra'; then
    echo "error: workflow 'Checkout verus-algebra' step must set repository: Phylliida/verus-algebra"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_algebra_step" | rg -q 'path:[[:space:]]*verus-algebra'; then
    echo "error: workflow 'Checkout verus-algebra' step must set path: verus-algebra"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_algebra_step" | rg -q 'persist-credentials:[[:space:]]*false'; then
    echo "error: workflow 'Checkout verus-algebra' step must set persist-credentials: false"
    exit 1
  fi

  if ! printf '%s\n' "$checkout_linalg_step" | rg -Fq "uses: $CHECKOUT_ACTION_REF"; then
    echo "error: workflow 'Checkout verus-linalg' step must pin uses: $CHECKOUT_ACTION_REF"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_linalg_step" | rg -q 'repository:[[:space:]]*Phylliida/verus-linalg'; then
    echo "error: workflow 'Checkout verus-linalg' step must set repository: Phylliida/verus-linalg"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_linalg_step" | rg -q 'path:[[:space:]]*verus-linalg'; then
    echo "error: workflow 'Checkout verus-linalg' step must set path: verus-linalg"
    exit 1
  fi
  if ! printf '%s\n' "$checkout_linalg_step" | rg -q 'persist-credentials:[[:space:]]*false'; then
    echo "error: workflow 'Checkout verus-linalg' step must set persist-credentials: false"
    exit 1
  fi
}

check_ci_workflow_end_to_end_structure() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local build_step=""
  local strict_step=""
  local build_line=""
  local strict_line=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  build_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Build Verus tools[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  strict_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Run strict checks[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  if [[ -z "$build_line" || -z "$strict_line" ]]; then
    echo "error: required workflow steps missing in $workflow_file"
    echo "expected steps: 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi
  if (( build_line >= strict_line )); then
    echo "error: workflow step order invalid in $workflow_file"
    echo "expected 'Build Verus tools' to run before 'Run strict checks'"
    exit 1
  fi

  build_step="$(extract_named_workflow_step_block "$workflow_file" "Build Verus tools")"
  strict_step="$(extract_named_workflow_step_block "$workflow_file" "Run strict checks")"

  if [[ -z "$build_step" ]]; then
    echo "error: failed to parse 'Build Verus tools' step block in $workflow_file"
    exit 1
  fi
  if [[ -z "$strict_step" ]]; then
    echo "error: failed to parse 'Run strict checks' step block in $workflow_file"
    exit 1
  fi

  check_workflow_step_fail_fast "Build Verus tools" "$build_step"
  check_workflow_step_fail_fast "Run strict checks" "$strict_step"

  if ! printf '%s\n' "$build_step" | rg -q 'working-directory:[[:space:]]*verus/source'; then
    echo "error: workflow 'Build Verus tools' step must run in verus/source"
    exit 1
  fi
  if ! printf '%s\n' "$build_step" | rg -Fq './tools/get-z3.sh'; then
    echo "error: workflow 'Build Verus tools' step must fetch z3 via ./tools/get-z3.sh"
    exit 1
  fi
  if ! printf '%s\n' "$build_step" | rg -q 'vargo[[:space:]]+build[[:space:]]+--release'; then
    echo "error: workflow 'Build Verus tools' step must build Verus tools via 'vargo build --release'"
    exit 1
  fi

  if ! printf '%s\n' "$strict_step" | rg -q 'working-directory:[[:space:]]*verus-geometry'; then
    echo "error: workflow 'Run strict checks' step must run in verus-geometry"
    exit 1
  fi
  if ! printf '%s\n' "$strict_step" | rg -Fq 'VERUS_ROOT: ${{ github.workspace }}/verus'; then
    echo "error: workflow 'Run strict checks' step must export VERUS_ROOT to the checked-out Verus tree"
    exit 1
  fi
  if ! printf '%s\n' "$strict_step" | rg -q '\./scripts/check\.sh'; then
    echo "error: workflow 'Run strict checks' step must execute ./scripts/check.sh"
    exit 1
  fi
}

check_ci_toolchain_install_wiring() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local install_step=""
  local install_line=""
  local build_line=""
  local strict_line=""
  local component=""
  local -a required_components=(
    "rustfmt"
    "rustc-dev"
    "llvm-tools"
  )

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  install_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Install required Rust toolchain[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  build_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Build Verus tools[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  strict_line="$(rg -n '^[[:space:]]*- name:[[:space:]]*Run strict checks[[:space:]]*$' "$workflow_file" | head -n 1 | cut -d: -f1)"
  if [[ -z "$install_line" || -z "$build_line" || -z "$strict_line" ]]; then
    echo "error: required workflow steps missing in $workflow_file"
    echo "expected steps: 'Install required Rust toolchain', 'Build Verus tools', and 'Run strict checks'"
    exit 1
  fi
  if (( install_line >= build_line || install_line >= strict_line )); then
    echo "error: workflow step order invalid for 'Install required Rust toolchain'"
    echo "expected it to run before 'Build Verus tools' and 'Run strict checks'"
    exit 1
  fi

  install_step="$(extract_named_workflow_step_block "$workflow_file" "Install required Rust toolchain")"
  if [[ -z "$install_step" ]]; then
    echo "error: failed to parse 'Install required Rust toolchain' step block in $workflow_file"
    exit 1
  fi

  check_workflow_step_fail_fast "Install required Rust toolchain" "$install_step"

  if ! printf '%s\n' "$install_step" | rg -q "rustup[[:space:]]+toolchain[[:space:]]+install[[:space:]]+$TOOLCHAIN([[:space:]]|$)"; then
    echo "error: workflow toolchain-install step must install the pinned toolchain '$TOOLCHAIN'"
    printf '%s\n' "$install_step"
    exit 1
  fi

  if ! printf '%s\n' "$install_step" | rg -q -- '--profile[[:space:]]+minimal'; then
    echo "error: workflow toolchain-install step must use '--profile minimal'"
    printf '%s\n' "$install_step"
    exit 1
  fi

  for component in "${required_components[@]}"; do
    if ! printf '%s\n' "$install_step" | rg -q -- "--component[[:space:]]+$component([[:space:]]|$)"; then
      echo "error: workflow toolchain-install step must include '--component $component'"
      printf '%s\n' "$install_step"
      exit 1
    fi
  done

  if ! printf '%s\n' "$install_step" | rg -q "rustup[[:space:]]+default[[:space:]]+$TOOLCHAIN([[:space:]]|$)"; then
    echo "error: workflow toolchain-install step must set rustup default to '$TOOLCHAIN'"
    printf '%s\n' "$install_step"
    exit 1
  fi
}

check_ci_toolchain_alignment() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local workflow_install_toolchain=""
  local workflow_default_toolchain=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi

  workflow_install_toolchain="$(extract_ci_toolchain_install_from_workflow "$workflow_file")"
  workflow_default_toolchain="$(extract_ci_toolchain_default_from_workflow "$workflow_file")"
  if [[ -z "$workflow_install_toolchain" || -z "$workflow_default_toolchain" ]]; then
    echo "error: failed to parse rustup toolchain from $workflow_file"
    echo "expected both \`rustup toolchain install <toolchain>\` and \`rustup default <toolchain>\`"
    exit 1
  fi

  if [[ "$workflow_install_toolchain" != "$workflow_default_toolchain" ]]; then
    echo "error: workflow rustup install/default toolchains drifted"
    echo "install: $workflow_install_toolchain"
    echo "default: $workflow_default_toolchain"
    exit 1
  fi

  if [[ "$workflow_install_toolchain" != "$TOOLCHAIN" ]]; then
    echo "error: workflow/check.sh toolchain mismatch"
    echo "check.sh TOOLCHAIN: $TOOLCHAIN"
    echo "workflow toolchain: $workflow_install_toolchain"
    exit 1
  fi
}

check_ci_strict_gate_alignment() {
  local workflow_file="$ROOT_DIR/.github/workflows/check.yml"
  local readme_file="$ROOT_DIR/README.md"
  local workflow_cmd=""
  local readme_cmd=""
  local workflow_norm=""
  local readme_norm=""
  local workflow_min=""
  local readme_min=""
  local -a required_flags=(
    "--require-verus"
    "--forbid-trusted-escapes"
    "--min-verified"
  )
  local flag=""

  if [[ ! -f "$workflow_file" ]]; then
    echo "error: workflow file not found: $workflow_file"
    exit 1
  fi
  if [[ ! -f "$readme_file" ]]; then
    echo "error: README file not found: $readme_file"
    exit 1
  fi

  workflow_cmd="$(extract_ci_check_command_from_workflow "$workflow_file")"
  readme_cmd="$(extract_ci_check_command_from_readme "$readme_file")"
  if [[ -z "$workflow_cmd" ]]; then
    echo "error: could not find CI-equivalent check command in $workflow_file"
    exit 1
  fi
  if [[ -z "$readme_cmd" ]]; then
    echo "error: could not find CI-equivalent check command in $readme_file"
    echo "expected a README command containing both --require-verus and --min-verified"
    exit 1
  fi

  workflow_norm="$(normalize_inline_command "$workflow_cmd")"
  readme_norm="$(normalize_inline_command "$readme_cmd")"

  for flag in "${required_flags[@]}"; do
    if ! printf '%s\n' "$workflow_norm" | rg -Fq -- "$flag"; then
      echo "error: workflow strict check command is missing required flag: $flag"
      echo "command: $workflow_norm"
      exit 1
    fi
  done

  workflow_min="$(extract_min_verified_arg "$workflow_norm")"
  readme_min="$(extract_min_verified_arg "$readme_norm")"
  if [[ -z "$workflow_min" || -z "$readme_min" ]]; then
    echo "error: failed to parse --min-verified value from workflow/README strict commands"
    echo "workflow: $workflow_norm"
    echo "README:   $readme_norm"
    exit 1
  fi

  if [[ "$workflow_min" != "$readme_min" ]]; then
    echo "error: workflow/README --min-verified mismatch"
    echo "workflow: $workflow_norm"
    echo "README:   $readme_norm"
    exit 1
  fi

  if [[ "$workflow_norm" != "$readme_norm" ]]; then
    echo "error: workflow and README CI-equivalent strict commands drifted"
    echo "workflow: $workflow_norm"
    echo "README:   $readme_norm"
    exit 1
  fi
}

check_no_trusted_escapes_in_non_test_sources() {
  local matches=""
  matches="$(
    rg -n \
      --color never \
      --glob '!**/tests.rs' \
      --glob '!**/test_*.rs' \
      --glob '!**/tests/**' \
      -e '\badmit\s*\(' \
      -e '\bassume\s*\(' \
      -e '#\s*\[\s*verifier::external(_body|_fn_specification|_type_specification)?\b' \
      -e '#\s*\[\s*verifier::truncate\b' \
      -e '#\s*\[\s*verifier::exec_allows_no_decreases_clause\b' \
      -e '\bunsafe\b' \
      "$ROOT_DIR/src" || true
  )"

  if [[ -n "$matches" ]]; then
    echo "error: non-test source files use trusted proof escapes"
    printf '%s\n' "$matches"
    exit 1
  fi
}

skip_or_fail_verus_unavailable() {
  local reason="$1"
  local hint="$2"

  if [[ "$REQUIRE_VERUS" == "1" ]]; then
    echo "[check] error: Verus verification required but unavailable: $reason" >&2
    if [[ -n "$hint" ]]; then
      echo "hint: $hint" >&2
    fi
    exit 1
  fi

  echo "[check] Skipping Verus verification: $reason"
  if [[ -n "$hint" ]]; then
    echo "hint: $hint"
  fi
  exit 0
}

run_cargo_verus_verify() {
  local feature_flags="${1:-}"

  if command -v rustup >/dev/null 2>&1; then
    export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
    export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
    export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
    cd "$ROOT_DIR"
    if [[ -n "$feature_flags" ]]; then
      # shellcheck disable=SC2086
      "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-geometry $feature_flags -- --triggers-mode silent
    else
      "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-geometry -- --triggers-mode silent
    fi
  elif command -v nix-shell >/dev/null 2>&1; then
    if nix-shell -p rustup --run "rustup --version >/dev/null 2>&1" >/dev/null 2>&1; then
      OFFLINE_CARGO_FLAG=""
      OFFLINE_EXPORT=""
      if [[ "$OFFLINE" == "1" ]]; then
        OFFLINE_CARGO_FLAG="--offline"
        OFFLINE_EXPORT="export CARGO_NET_OFFLINE=true"
      fi
      nix-shell -p rustup --run "
        set -euo pipefail
        $OFFLINE_EXPORT
        export RUSTUP_TOOLCHAIN='$TOOLCHAIN'
        export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
        export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
        cd '$ROOT_DIR'
        cargo $OFFLINE_CARGO_FLAG verus verify --manifest-path Cargo.toml -p verus-geometry $feature_flags -- --triggers-mode silent
      "
    else
      skip_or_fail_verus_unavailable \
        "rustup is unavailable and nix-shell could not provide it in this environment" \
        "install rustup locally, or use an environment where nix-shell can access the nix daemon"
    fi
  else
    skip_or_fail_verus_unavailable \
      "rustup not found in PATH" \
      "install rustup with default toolchain $TOOLCHAIN"
  fi
}

extract_verus_verified_count() {
  local log_file="$1"
  local summary=""
  local verified_count=""
  local error_count=""

  summary="$(rg -No 'verification results::\s*([0-9]+) verified,\s*([0-9]+) errors' -r '$1|$2' "$log_file" | tail -n 1 || true)"
  if [[ -z "$summary" ]]; then
    echo "error: could not parse Verus verification summary"
    cat "$log_file"
    exit 1
  fi

  verified_count="${summary%%|*}"
  error_count="${summary##*|}"
  if ! [[ "$verified_count" =~ ^[0-9]+$ && "$error_count" =~ ^[0-9]+$ ]]; then
    echo "error: malformed Verus verification summary: $summary"
    cat "$log_file"
    exit 1
  fi

  if (( error_count != 0 )); then
    echo "error: Verus verification summary reported nonzero errors: $error_count"
    cat "$log_file"
    exit 1
  fi

  printf '%s' "$verified_count"
}

verify_verus_summary_threshold() {
  local log_file="$1"
  local threshold="$2"
  local verified_count="$3"

  if (( verified_count < threshold )); then
    echo "error: Verus verified-count regression: expected at least $threshold, got $verified_count"
    cat "$log_file"
    exit 1
  fi

  echo "[check] Verus verified-count gate passed ($verified_count >= $threshold)"
}

run_cargo_verus_verify_with_threshold() {
  local feature_flags="${1:-}"
  local verus_log=""
  local verus_status=0

  verus_log="$(mktemp)"
  set +e
  run_cargo_verus_verify "$feature_flags" 2>&1 | tee "$verus_log"
  verus_status="${PIPESTATUS[0]}"
  set -e

  if (( verus_status != 0 )); then
    rm -f "$verus_log"
    exit "$verus_status"
  fi

  LAST_VERIFIED_COUNT="$(extract_verus_verified_count "$verus_log")"
  echo "[check] Observed Verus verified count: $LAST_VERIFIED_COUNT"

  if [[ -n "$MIN_VERIFIED" ]]; then
    verify_verus_summary_threshold "$verus_log" "$MIN_VERIFIED" "$LAST_VERIFIED_COUNT"
  fi

  rm -f "$verus_log"
}

require_command rg "install ripgrep (binary: rg) before running strict checks"

echo "[check] Verifying CI toolchain alignment (workflow vs check.sh)"
check_ci_toolchain_alignment

echo "[check] Verifying CI toolchain-install step wiring"
check_ci_toolchain_install_wiring

echo "[check] Verifying CI workflow permissions hardening"
check_ci_workflow_permissions_hardening

echo "[check] Verifying CI workflow trigger coverage"
check_ci_workflow_trigger_coverage

echo "[check] Verifying CI verify-job execution contract"
check_ci_verify_job_execution_contract

echo "[check] Verifying CI verify-job runner pinning"
check_ci_verify_runner_pinning

echo "[check] Verifying CI workflow checkout wiring"
check_ci_workflow_checkout_wiring

echo "[check] Verifying CI workflow end-to-end structure"
check_ci_workflow_end_to_end_structure

echo "[check] Verifying CI strict-gate command alignment (workflow vs README)"
check_ci_strict_gate_alignment

if [[ "$FORBID_TRUSTED_ESCAPES" == "1" ]]; then
  echo "[check] Verifying non-test source tree excludes trusted proof escapes"
  check_no_trusted_escapes_in_non_test_sources
fi

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  skip_or_fail_verus_unavailable \
    "cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus" \
    "build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  skip_or_fail_verus_unavailable \
    "z3 not found at $VERUS_SOURCE/z3" \
    "build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
fi

echo "[check] Running cargo verus verify"
run_cargo_verus_verify_with_threshold ""
