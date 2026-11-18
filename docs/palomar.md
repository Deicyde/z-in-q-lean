# Palomar verification

Palomar certifies named declarations at an immutable public commit. It checks that a solution proves the types in an independently readable challenge. For the polynomial theorem, the challenge must express the twelve mathematical hypotheses and the assertion about one polynomial for all rational inputs. Replacing a hypothesis by a stronger assumption changes what has been verified. [Numbered theorem](blueprint/sections/global-height.md#s-113) · [Submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md)

The initial inventory at revision `95357929` covered all 2,121 Lean sources. Five used the module header, 2,116 required migration and the longest file had 1,034 lines. The standard sets a limit of 10,000 physical lines per source. The repository has no Palomar registry identifier for its conditional polynomial theorem. [Audited revision](https://github.com/nasqret/z-in-q-lean/tree/95357929cf16cedd3dd1960c11060cb923f5bdca) · [Registry verification](https://palomar-registry.org/how-to-submit)

## Arithmetic already checked

The root Lake project now builds its 31 foundational modules with Lean 4.35.0. Its first independent comparison covers two strict size and divisibility lemmas used to exclude incorrect multiplication certificates. The challenge imports only `Std`. The solution applies the two existing proofs. A sandboxed run of Comparator compared both declarations and all six bundled kernels accepted the exported solution. This is a project-run comparison. Palomar registration of the conditional polynomial theorem remains open. [Challenge](../Comparison/Challenge.lean) · [Solution](../Comparison/Solution.lean) · [Checked sources and kernel results](../Comparison/verification.json)

From the repository root on Linux with a supported Bubblewrap, run

```sh
lake build
lake comparator --config comparator.json --paranoid
```

The comparison names the two arithmetic lemmas. The permitted axioms and the module names are recorded in the [configuration](../comparator.json).

## Reproduce the source inventory

The current edition has 38 module headers among 2,123 Lean files. The 2,085 files still awaiting migration include the project-specific imports of Theorem 113. Palomar’s pinned source scanner found precisely those 2,085 missing headers. Lean’s own header parser independently counted all 38 modules. No file exceeds the length limit. [Repository-wide source check](../Comparison/repository-inventory.json)

Run `python3 dashboard/palomar_sources.py --json` at the repository root to identify every file requiring a header or length correction. The command returns a nonzero exit status until all sources pass. Lean's parser and the official verifier determine acceptance.

In a separate preview the source scanner accepted all 2,123 files. Lean 4.35 parsed every module header and confirmed that each file imports precisely the same modules, in the same order and with the same visibility. Moving these edits into the edition requires checking the proof bodies against their dependencies. [Preview results](../Comparison/module-preview.json)

To reproduce the preview, run the following commands from a clean checkout with Python 3.11 or later and Lean 4.35.0. The first command writes the proposed sources to a new directory.

```sh
python3 Comparison/preview_modules.py . ../zq-module-preview
git clone https://github.com/PalomarRegistry/PalomarSubmission.git ../palomar-submission
git -C ../palomar-submission checkout --detach 14aa8d6b3c2f14a8540605e37144560b9a00e7e7
python3 Comparison/check_module_preview.py ../palomar-submission "$(command -v lean)" . ../zq-module-preview
```

## What the proof must pass

1. Every Lean file in the submitted repository uses the module system, including archived sources outside the default build targets. Each migrated development needs its imports, exported declarations and proofs checked at the selected toolchain.
2. The challenge imports only Lean core or the allowlisted library closure at authenticated revisions. Its statement must be understandable without importing this project's definitions wholesale. The solution may use the broader pinned development.
3. Comparator checks the named solution declarations against the challenge. The permitted axioms are propositional extensionality, classical choice and quotient soundness. Palomar also checks the exported proof independently.
4. The submission records the repository license, authorship, use of automation, the relationship to earlier work and the scope of prior review. The registry checks the formal and informal statements before a result is registered. [Mechanical and editorial requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md) · [Minimum toolchain](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/toolchains.json)
