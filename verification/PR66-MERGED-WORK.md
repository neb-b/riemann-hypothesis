# Merged-work tradeoffs of PR #66

Compared main `2dea9900` with Vasily's published source `9b1ee601`, integrated in `716d8a58`. Source and build configuration remain byte-identical to the published build.

| Previously merged work | Outcome |
|---|---|
| [#68: shared finiteness proof and pruning](https://github.com/leanprover-community/riemann-hypothesis/pull/68) | Rolled back: 180 of its 181 deleted files return, together with the longer automorphic-finiteness proof. One deleted file remains absent. |
| [#57: five compact proof cleanups](https://github.com/leanprover-community/riemann-hypothesis/pull/57) | Partly reverted: `CoboundaryOfGenerator` grows from 131 to 1,134 lines, and `FgZ1T` from 69 to 527. The other three cleaned proofs remain compact. |
| [#60: FixPiIff cleanup](https://github.com/leanprover-community/riemann-hypothesis/pull/60) | Retained: 45 lines become 49 with the module wrapper. |
| [#65: four proof cleanups](https://github.com/leanprover-community/riemann-hypothesis/pull/65) | Retained, with module wrappers and Lean 4.36 API adaptations. |
| [#72: runner diagnostics](https://github.com/leanprover-community/riemann-hypothesis/pull/72), and current main's other non-source CI/cache infrastructure | Preserved exactly. |

The useful work lost is proof simplification and pruning. These are maintenance/build-size regressions, not evidence of changed mathematical conclusions. Restoring #68 and the two reverted #57 cleanups should be separately validated follow-ups after the archive-compatible 4.36 release.

Audit scope: Git source inventories and the named cleanup files. Since the common base `f1f6d654`, only #68 changed Lean source; #72 changed no source files. This is not a theorem-by-theorem audit of the complete Lean 4.36 port. No proofs were rebuilt for this report.
