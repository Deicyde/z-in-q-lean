# Palomar verification

Palomar certifies named declarations at an immutable public commit. It checks that a solution proves the types in an independently readable challenge. For the polynomial theorem, the challenge must express the twelve mathematical hypotheses and the assertion about one polynomial for all rational inputs. Replacing a hypothesis by a stronger assumption changes what has been verified. [Numbered theorem](blueprint/sections/global-height.md#s-113) · [Submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md)

The initial inventory at revision `95357929` covered all 2,121 Lean sources. Five used the module header, 2,116 required migration and the longest file had 1,034 lines. The standard sets a limit of 10,000 physical lines per source. The repository has no Palomar registry identifier for its conditional polynomial theorem. [Audited revision](https://github.com/nasqret/z-in-q-lean/tree/95357929cf16cedd3dd1960c11060cb923f5bdca) · [Registry verification](https://palomar-registry.org/how-to-submit)

## Reproduce the source inventory

Run `python3 dashboard/palomar_sources.py --json` at the repository root to identify every file requiring a header or length correction. The command returns a nonzero exit status when that part of the inventory is incomplete. Lean's parser and the official verifier determine acceptance.

## What the proof must pass

1. Every Lean file in the submitted repository uses the module system, including archived sources outside the default build targets. Each migrated development needs its imports, exported declarations and proofs checked at the selected toolchain.
2. The challenge imports only Lean core or the allowlisted library closure at authenticated revisions. Its statement must be understandable without importing this project's definitions wholesale. The solution may use the broader pinned development.
3. Comparator checks the named solution declarations against the challenge. The permitted axioms are propositional extensionality, classical choice and quotient soundness. Palomar also checks the exported proof independently.
4. The submission records the repository license, authorship, use of automation, the relationship to earlier work and the scope of prior review. The registry checks the formal and informal statements before a result is registered. [Mechanical and editorial requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md) · [Minimum toolchain](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/toolchains.json)
