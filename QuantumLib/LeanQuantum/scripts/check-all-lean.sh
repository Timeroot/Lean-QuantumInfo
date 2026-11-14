#!/usr/bin/env bash

set -u -o pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/.." && pwd)"

cd "${repo_root}"

mapfile -t modules < <(
  find Quantum -type f -name '*.lean' | sort | sed -e 's#/#.#g' -e 's#\.lean$##'
)

if [ "${#modules[@]}" -eq 0 ]; then
  echo "No Lean modules found under Quantum."
  exit 1
fi

failures=()
total="${#modules[@]}"
index=0

for module in "${modules[@]}"; do
  index=$((index + 1))
  echo "[${index}/${total}] Building ${module}"
  if ! lake build "${module}"; then
    failures+=("${module}")
  fi
done

if [ "${#failures[@]}" -ne 0 ]; then
  echo
  echo "Lean module audit failed for ${#failures[@]} module(s):"
  printf ' - %s\n' "${failures[@]}"
  exit 1
fi

echo
echo "Lean module audit succeeded: ${total} module(s) built."
