# Branch and worktree inventory — public-readiness S7

Measured 2026-09-25T00:56:15.513935+00:00. Derived counts below.

[AGENT] Classification is advisory. No branch, tag or worktree is deleted.
Ancestry does not establish that rebased audit records are disposable. Active
cleanup, audit/review, upstream submission and prototype records are retained;
the operator decides whether a merged record can be archived and removed.
The failed SC prototype is a parked record, not a release dependency.
Only Git metadata was read; no retired checkout, dependency tree or worktree was operated.

Commands: `git for-each-ref --format="%(refname:short)|%(objectname)" refs/heads`,
`git worktree list --porcelain`, and `git merge-base --is-ancestor <head> <mainline>`.
Full hashes below are the verbatim ref values; classifications and counts are derived.
The snapshot precedes this round’s commits and may differ from the overseer’s later landing.

## lem-lean

Mainline `mdd/lean-backend` = `38f87d5fa6b29ec90edfa457faba8a309e32c118`.
Derived inventory: 14 local branches, 7 registered worktrees.

| Branch | Head | Classification |
|---|---|---|
| `arc/effect-retirement` | `045dcb0d57a171eb4fb3a6eb5abe288c227270ce` | merged; candidate-delete only after operator record/ownership check |
| `arc/effects-totality` | `d25f982d85bd5504dab7930c7b370e07713bbc3c` | merged; candidate-delete only after operator record/ownership check |
| `arc/libc-load` | `bd7e2ebeaf5d24bc643c59cdac7b31549afd2f2f` | merged; candidate-delete only after operator record/ownership check |
| `arc/next` | `f6542f8e6860d12d4655e6648bc4c45dabd1d798` | merged; candidate-delete only after operator record/ownership check; attached worktree |
| `arc/totality-sweep` | `574e326ff694069bf37e0d51cd06bef1b69a63e7` | merged; candidate-delete only after operator record/ownership check |
| `audit/public-readiness-must-20260924` | `0df91caaf30e5a2c92440d5a981a7ceffd4f584d` | keep-as-record / protected reference; attached worktree |
| `cerberus-pin` | `38f87d5fa6b29ec90edfa457faba8a309e32c118` | keep-as-record / protected reference (merged); attached worktree |
| `cleanup/public-readiness-20260924` | `6b20bfd02de924d078725efa96c6675115b8b17a` | keep-as-record / protected reference; attached worktree |
| `cleanup/public-readiness-should-20260925` | `6b20bfd02de924d078725efa96c6675115b8b17a` | keep-as-record / protected reference; attached worktree |
| `master` | `3802cb04b53d5f1096a464e51ecbfb2a750a7ccd` | keep-as-record / protected reference (merged) |
| `mdd/lean-backend` | `38f87d5fa6b29ec90edfa457faba8a309e32c118` | keep-as-record / protected reference; attached worktree |
| `noodle/backend` | `a02cb6f5aa3fc5d0955fb48c922376125f40470d` | keep-as-record; unmerged, ownership/status to confirm |
| `review/backend-quality` | `09628141121a42e25981779127dc038ae8b64c35` | keep-as-record / protected reference |
| `review/public-readiness-20260924` | `07b709e95b604aff305c3a3dc6b5ebeed088796b` | keep-as-record / protected reference; attached worktree |

Verbatim registered worktree metadata:

```text
worktree /home/dev/projects/cerberus-lean-proj/lem-lean
HEAD 38f87d5fa6b29ec90edfa457faba8a309e32c118
branch refs/heads/mdd/lean-backend

worktree /home/dev/projects/cerberus-lean-proj/deps/lem-pinned
HEAD 38f87d5fa6b29ec90edfa457faba8a309e32c118
branch refs/heads/cerberus-pin

worktree /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/fuel-parameter
HEAD f6542f8e6860d12d4655e6648bc4c45dabd1d798
branch refs/heads/arc/next

worktree /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-audit/public-readiness-must-20260924
HEAD 0df91caaf30e5a2c92440d5a981a7ceffd4f584d
branch refs/heads/audit/public-readiness-must-20260924

worktree /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-cleanup-public-readiness-20260924
HEAD 6b20bfd02de924d078725efa96c6675115b8b17a
branch refs/heads/cleanup/public-readiness-20260924

worktree /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-cleanup-public-readiness-should-20260925
HEAD 6b20bfd02de924d078725efa96c6675115b8b17a
branch refs/heads/cleanup/public-readiness-should-20260925

worktree /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-public-readiness-20260924
HEAD 07b709e95b604aff305c3a3dc6b5ebeed088796b
branch refs/heads/review/public-readiness-20260924
```

| Worktree | Classification |
|---|---|
| `/home/dev/projects/cerberus-lean-proj/lem-lean` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/deps/lem-pinned` | keep-as-record / protected reference (merged) |
| `/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/fuel-parameter` | merged; candidate-delete only after operator record/ownership check |
| `/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-audit/public-readiness-must-20260924` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-cleanup-public-readiness-20260924` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-cleanup-public-readiness-should-20260925` | keep; active worktree for this follow-up |
| `/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-public-readiness-20260924` | keep-as-record / protected reference |

## cerberus-lean

Mainline `mdd/cerberus-lean` = `e9f9d049ffaaf005c392495b0f6418d21f4df29f`.
Derived inventory: 53 local branches, 22 registered worktrees.

| Branch | Head | Classification |
|---|---|---|
| `arc/address-space-bound-part-two` | `0457732e1865a3ba2bc678f6ca8c35e532471baa` | merged; candidate-delete only after operator record/ownership check |
| `arc/allocator-soundness-address-bound` | `e64819de7e5169ea1ea34b284ad000a13edbcdda` | merged; candidate-delete only after operator record/ownership check |
| `arc/concurrency-landing` | `1349ec56fc8892fbc97f0522056d862c74b682f3` | keep-as-record / protected reference |
| `arc/lean-only-outcomes-S0` | `8f8c4dfe7bf30c8733d2ea9590f8f5ef3c4a930b` | keep-as-record; unmerged, ownership/status to confirm; attached worktree |
| `arc/next` | `e30810be76e4150fa9bd8e2f0736282a30b6da30` | merged; candidate-delete only after operator record/ownership check; attached worktree |
| `arc/pristine-oracle-instrument` | `4a23d98aafa71923ce5f205ee5590bf2f5372d56` | merged; candidate-delete only after operator record/ownership check |
| `arc/program-data-parameters` | `df85e95b7b37826dfb3f2ac97a41473580f1e0b9` | merged; candidate-delete only after operator record/ownership check |
| `arc/run-digest` | `34ac493f989bbf3bd3954bba0ba1d05c018e269c` | merged; candidate-delete only after operator record/ownership check |
| `arc/sc-concurrency` | `a740c48aea28852d9ed2e334c9bcb49eefaba17b` | keep-as-record / protected reference; attached worktree |
| `arc/sc-prototype` | `4860f0ef0d20f2a2a4d8d96e6ecfc7b2c99ceed2` | keep-as-record / protected reference; attached worktree |
| `arc/seam-hygiene` | `a8d00feed49e2b05dffddabf7f5727fb5635329b` | merged; candidate-delete only after operator record/ownership check |
| `arc/segment-ladder` | `fcfa8934cd113e91df45b72d023694e653449087` | keep-as-record; unmerged, ownership/status to confirm |
| `arc/t5-seal` | `6f321327ad5f3fc18039bc4be72a11d5d9acd463` | keep-as-record; unmerged, ownership/status to confirm |
| `arc/validation-foundations` | `d607409f92a96c3fb9c207acbabf0f76a23cb227` | keep-as-record; unmerged, ownership/status to confirm |
| `arc/validation-foundations-concurrency` | `86a2aea547804b78eb7f1eae633bb9c24c713b7f` | keep-as-record / protected reference |
| `audit/allocator-part-one` | `f8222307f9554149127eae4bbf2fbfcab15f8857` | keep-as-record / protected reference |
| `audit/concurrency-design-20260919` | `38d7d2123ca1dd2a0769c19518b9410c7d4ea1f5` | keep-as-record / protected reference; attached worktree |
| `audit/concurrency-premerge` | `c0a926707477768abc06073b4782b093258449d4` | keep-as-record / protected reference |
| `audit/enum-base-20260920` | `5407597d9eeba0259d65b728e86a860ad4614ab3` | keep-as-record / protected reference (merged); attached worktree |
| `audit/enum-premerge-20260920` | `880a8ead8357acc31b1339131e0ad9c00cfe36f1` | keep-as-record / protected reference; attached worktree |
| `audit/enum-repairs-20260921` | `44e7989afa50f07582bbcbe99ea84f488e1129ea` | keep-as-record / protected reference; attached worktree |
| `audit/fuel-forms-carriers` | `bda941a5a1ebb38a2d7569ab1dbd1370b2119a0b` | keep-as-record / protected reference |
| `audit/item7-rereview-20260922` | `3e8f7c4bd72f7fd5289ce5e59766fd55763db2c6` | keep-as-record / protected reference |
| `audit/item7-round3-review-20260923` | `629aab197cd9ffd559b4bc78569e651614f477f0` | keep-as-record / protected reference |
| `audit/match-pattern-arity-20260921` | `14457f1a0b30e1de3762310af51684bf6d2e347f` | keep-as-record / protected reference; attached worktree |
| `audit/pristine-oracle-instrument` | `4df08432e27d37394ea56afa15c60d0e84e18e67` | keep-as-record / protected reference |
| `audit/program-data-parameters-S0.5` | `57a2d3bd7def5bc8bf1c758a04e61e6fac35496f` | keep-as-record / protected reference |
| `audit/public-readiness-must-20260924` | `c3e2070b43d4695ad95fd604ecc8ebb0bdfd9bed` | keep-as-record / protected reference; attached worktree |
| `audit/run-digest-20260922` | `97c98bcce147217713de7ce93f65ff5868350be0` | keep-as-record / protected reference; attached worktree |
| `audit/seam-hygiene` | `05d208f45a65cd118bf9d8a2d24f7ef3a477f121` | keep-as-record / protected reference |
| `cleanup/public-readiness-20260924` | `c13a1054133b49c954fe27ac4c1b4e33a418c51f` | keep-as-record / protected reference; attached worktree |
| `cleanup/public-readiness-should-20260925` | `c13a1054133b49c954fe27ac4c1b4e33a418c51f` | keep-as-record / protected reference; attached worktree |
| `docs/concurrency-landing-scoping` | `6da619f69c1d8fd1fc070dac56630468321672d9` | keep-as-record / protected reference (merged) |
| `docs/concurrency-pause` | `b7e45d55e3ef2ed5f837755e4e5b7649c204dd6f` | keep-as-record / protected reference (merged) |
| `docs/concurrency-research-20260920` | `02a6adc9091f72cecac6c5ff15845f93fa81fa84` | keep-as-record / protected reference; attached worktree |
| `docs/concurrency-scoping-erratum` | `bb09cb745a6b2d80a5a82f0ec1e11b76fb008014` | keep-as-record / protected reference (merged) |
| `docs/consumer-repin-2026-09-23` | `e9f9d049ffaaf005c392495b0f6418d21f4df29f` | keep-as-record / protected reference (merged) |
| `docs/d2-structural-outcomes-response` | `59dbb603d328c11781f8c79065a919a566b19a57` | keep-as-record / protected reference (merged) |
| `docs/lean-only-outcomes-S0-record` | `bfca41724d43b526604a0f0f30b1f629eb8d8b92` | keep-as-record / protected reference (merged) |
| `docs/lean-only-outcomes-plan-review` | `0c78635cbf0cddea72d696372c3cbbc974328e00` | keep-as-record / protected reference (merged) |
| `docs/program-data-parameters-design` | `1c319a40ef54ee980e1dbaf2caeca26ccdb778d0` | keep-as-record / protected reference; attached worktree |
| `docs/public-readiness-must-checkpoint-note` | `c9d57da9bc7db76229f98c4503431db5bac9450c` | keep-as-record / protected reference; attached worktree |
| `docs/run-digest-design` | `4d777218ec9b1124d7e14f76aadf8cf431b08a16` | keep-as-record / protected reference |
| `docs/tray-44-allocator-division` | `b7b8e42505eb16fcca21586ba2712d50e7a0e5c0` | keep-as-record / protected reference (merged) |
| `feature/concurrency` | `086d8762d382eff375c101f5f0c64d3ffe9bccc7` | keep-as-record / protected reference; attached worktree |
| `fix/match-pattern-arity` | `2b51d2a57179d890a51dda404aedf59d80196926` | merged; candidate-delete only after operator record/ownership check |
| `master` | `b9aeedcb4dd438763b0eef7f95ac19e93875d7de` | keep-as-record / protected reference (merged) |
| `mdd/cerberus-lean` | `e9f9d049ffaaf005c392495b0f6418d21f4df29f` | keep-as-record / protected reference; attached worktree |
| `review/sc-concurrency-plan-20260925` | `e280ba684e95be1c4e6c38ec8e21fa09316950df` | keep-as-record / protected reference; attached worktree |
| `upstream-pr/bswap64` | `c44d30dcfa52e4ac5fc9627cbfd543fa3264650b` | keep-as-record; unmerged, ownership/status to confirm; attached worktree |
| `upstream-pr/char-escapes` | `da993e5a094973343dbec96a1e7d50cb58b71e93` | keep-as-record; unmerged, ownership/status to confirm; attached worktree |
| `upstream-pr/pp-roundtrip` | `c3d18a49fd8511fbb1fb5103128b94bc321e4268` | keep-as-record; unmerged, ownership/status to confirm; attached worktree |
| `wip/fuel-parameter-C1-scratch` | `b0f718edaa498a8899185a77bca8759d8d82375d` | keep-as-record; unmerged, ownership/status to confirm |

Verbatim registered worktree metadata:

```text
worktree /home/dev/projects/cerberus-lean-proj/cerberus-lean
HEAD e9f9d049ffaaf005c392495b0f6418d21f4df29f
branch refs/heads/mdd/cerberus-lean

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/lean-only-outcomes-S0
HEAD 8f8c4dfe7bf30c8733d2ea9590f8f5ef3c4a930b
branch refs/heads/arc/lean-only-outcomes-S0

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/sc-concurrency
HEAD a740c48aea28852d9ed2e334c9bcb49eefaba17b
branch refs/heads/arc/sc-concurrency

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/sc-prototype
HEAD 4860f0ef0d20f2a2a4d8d96e6ecfc7b2c99ceed2
branch refs/heads/arc/sc-prototype

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/zero-discrepancy
HEAD e30810be76e4150fa9bd8e2f0736282a30b6da30
branch refs/heads/arc/next

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/concurrency-design-20260919
HEAD 38d7d2123ca1dd2a0769c19518b9410c7d4ea1f5
branch refs/heads/audit/concurrency-design-20260919

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-base-20260920
HEAD 5407597d9eeba0259d65b728e86a860ad4614ab3
branch refs/heads/audit/enum-base-20260920

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-premerge-20260920
HEAD 880a8ead8357acc31b1339131e0ad9c00cfe36f1
branch refs/heads/audit/enum-premerge-20260920

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-repairs-20260921
HEAD 44e7989afa50f07582bbcbe99ea84f488e1129ea
branch refs/heads/audit/enum-repairs-20260921

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/match-pattern-arity-20260921
HEAD 14457f1a0b30e1de3762310af51684bf6d2e347f
branch refs/heads/audit/match-pattern-arity-20260921

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/public-readiness-must-20260924
HEAD c3e2070b43d4695ad95fd604ecc8ebb0bdfd9bed
branch refs/heads/audit/public-readiness-must-20260924

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/run-digest-20260922
HEAD 97c98bcce147217713de7ce93f65ff5868350be0
branch refs/heads/audit/run-digest-20260922

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-cleanup-public-readiness-20260924
HEAD c13a1054133b49c954fe27ac4c1b4e33a418c51f
branch refs/heads/cleanup/public-readiness-20260924

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-cleanup-public-readiness-should-20260925
HEAD c13a1054133b49c954fe27ac4c1b4e33a418c51f
branch refs/heads/cleanup/public-readiness-should-20260925

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/concurrency-research-20260920
HEAD 02a6adc9091f72cecac6c5ff15845f93fa81fa84
branch refs/heads/docs/concurrency-research-20260920

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/program-data-parameters-design
HEAD 1c319a40ef54ee980e1dbaf2caeca26ccdb778d0
branch refs/heads/docs/program-data-parameters-design

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/public-readiness-must-note
HEAD c9d57da9bc7db76229f98c4503431db5bac9450c
branch refs/heads/docs/public-readiness-must-checkpoint-note

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-feature/concurrency
HEAD 086d8762d382eff375c101f5f0c64d3ffe9bccc7
branch refs/heads/feature/concurrency

worktree /home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-review/sc-concurrency-plan-20260925
HEAD e280ba684e95be1c4e6c38ec8e21fa09316950df
branch refs/heads/review/sc-concurrency-plan-20260925

worktree /home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-bswap64
HEAD c44d30dcfa52e4ac5fc9627cbfd543fa3264650b
branch refs/heads/upstream-pr/bswap64

worktree /home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-char-escapes
HEAD da993e5a094973343dbec96a1e7d50cb58b71e93
branch refs/heads/upstream-pr/char-escapes

worktree /home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-pp-roundtrip
HEAD c3d18a49fd8511fbb1fb5103128b94bc321e4268
branch refs/heads/upstream-pr/pp-roundtrip
```

| Worktree | Classification |
|---|---|
| `/home/dev/projects/cerberus-lean-proj/cerberus-lean` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/lean-only-outcomes-S0` | keep-as-record; unmerged, ownership/status to confirm |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/sc-concurrency` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/sc-prototype` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/zero-discrepancy` | merged; candidate-delete only after operator record/ownership check |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/concurrency-design-20260919` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-base-20260920` | keep-as-record / protected reference (merged) |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-premerge-20260920` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-repairs-20260921` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/match-pattern-arity-20260921` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/public-readiness-must-20260924` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/run-digest-20260922` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-cleanup-public-readiness-20260924` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-cleanup-public-readiness-should-20260925` | keep; active worktree for this follow-up |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/concurrency-research-20260920` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/program-data-parameters-design` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/public-readiness-must-note` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-feature/concurrency` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-review/sc-concurrency-plan-20260925` | keep-as-record / protected reference |
| `/home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-bswap64` | keep-as-record; unmerged, ownership/status to confirm |
| `/home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-char-escapes` | keep-as-record; unmerged, ownership/status to confirm |
| `/home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-pp-roundtrip` | keep-as-record; unmerged, ownership/status to confirm |

