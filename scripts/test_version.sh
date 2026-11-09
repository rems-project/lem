#!/usr/bin/env bash
# Exercise the production Makefile recipe in an isolated Git repository.
# Tags created here never touch the source repository's refs.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lem-version.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_COUNT=0
unset GIT_CONFIG_PARAMETERS GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE
export GIT_AUTHOR_NAME='Version test' GIT_AUTHOR_EMAIL='version@example.invalid'
export GIT_COMMITTER_NAME="$GIT_AUTHOR_NAME" GIT_COMMITTER_EMAIL="$GIT_AUTHOR_EMAIL"
cd "$scratch"
git init -q
mkdir src
printf 'src/version.ml\n' > .gitignore
git add .gitignore
git commit -qm initial
version() {
  make --no-print-directory -s -f "$root/Makefile" version
  sed -n 's/^let v="\(.*\)"$/\1/p' src/version.ml
}
hash=$(git rev-parse --short HEAD)
[[ $(version) == "$hash" ]]
git tag -a release-test -m 'scratch annotated tag'
[[ $(version) == "release-test-0-g$hash" ]]
printf '\n' >> .gitignore
[[ $(version) == "release-test-0-g$hash-dirty" ]]
git add .gitignore
git commit -qm second
hash=$(git rev-parse --short HEAD)
[[ $(version) == "release-test-1-g$hash" ]]
# A source archive has no commit identity. Keep the release fallback, and
# let consumers that require a hash reject it rather than inventing one.
mv .git git-metadata
[[ $(GIT_DIR="$scratch/missing-git-directory" version) == '2026-05-01' ]]
echo 'test_version: OK (untagged, exact annotated tag, dirty tag, post-tag, archive fallback)'
