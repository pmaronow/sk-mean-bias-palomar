# Source provenance and review status

The paper authors, formalization authors, and responsible maintainers are P. M. Aronow and Patrick Lopatto. The paper's author list is preserved. Sol 6.1 autoformalized the original Lean development. Subsequent Codex preparation produced the public repository and compact Challenge/Solution interface. Codex compiler compatibility work adapted the retained sources to the current pins. Codex automated mathematical-source review, bibliographic review and verification are separate activities, with their findings and outcomes recorded in the scope, coverage and verification documents.

The manuscript preserves the authors' note that its text, except that note and small edits to the abstract, was machine written under their supervision for readability and citation. That note is not a claim of human mathematical proof review. Authorship and responsible maintenance likewise do not establish human mathematical review. The source correspondence review and any checks recorded for this preparation are automated. Their outcomes, including unresolved failures, are stated in [verification.md](verification.md).

## Source lineage

The [release repository](https://github.com/pmaronow/sk-mean-bias-palomar) begins with one source commit. It does not contain the preparation history. The preceding prepared source is [13598f760e19227d0680bac616320fd495f5c4bb](https://github.com/pmaronow/temp-sk-repo/commit/13598f760e19227d0680bac616320fd495f5c4bb); earlier checked revisions cited in [verification.md](verification.md) likewise belong to the external preparation repository. Removing working comments for this release does not establish a fresh build or kernel check.

The development retains the current paper-specific modules and the earlier Gaussian, Parisi, interpolation, scalar stability, replica-source and cavity foundations used by the selected interface or the 58 numbered coverage entries. The distributed source is their local import closure, with the import-only `HexagonUpperBound` entry point; additional modules and the optional external-comparison entry point are excluded. The three build targets are `HexagonUpperBound`, `Challenge` and `Solution`. Their live import graph must cover every retained local Lean source before the verification pipeline can pass.

Modules formerly nested under local vendor roots have been flattened into one Lake project so the retained development can be built from distributed source. Their original module locations are retained in [source-origins.json](../provenance/source-origins.json). Moving or selecting source files does not prove their contents or change their license. Scope limitations from excluded conditional comparisons remain disclosed in [mathematical-scope.md](mathematical-scope.md).

The inherited provenance identifies an earlier formalization commit, `95155652e60e20f1abd6e79ef257ce17854f6a4e`, and earlier Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins. That identifier is an inherited historical claim; it is not the revision of this repository. The supplied material did not include a public repository URL for it. Historical compiler and axiom receipts concerned earlier sources and reused build artifacts. They do not validate the prepared source tree.

This repository uses the pins in [lean-toolchain](../lean-toolchain), [lakefile.toml](../lakefile.toml), and [lake-manifest.json](../lake-manifest.json). Compatibility changes are intended to preserve statement types while adapting proof elaboration and library APIs. The current mathematical scope and exact-target review are recorded separately in [mathematical-scope.md](mathematical-scope.md), [coverage.md](coverage.md), and [numbered-claims.json](numbered-claims.json).

## Verification identity

The [verification report](verification.md) identifies the exact source snapshot checked, its dependency pins, and the outcome of each check. A report tied to a different source hash or commit is historical evidence, not validation of a changed tree. The reproducible scripts create fresh records for the source revision they actually inspect.

Comparator checks the submitted interface and Solution; the numbered-claim check concerns the manuscript correspondence ledger. These are different checks. Compiler acceptance, transitive axiom auditing, independent kernel checking, and mathematical agreement with a source statement must be assessed separately.

## Third-party provenance

Original source is MIT-licensed as specified by the maintainers for this repository. Existing third-party headers and license grants are preserved. [THIRD_PARTY_NOTICES.md](../THIRD_PARTY_NOTICES.md) lists the attribution, recovered upstream license references, and unresolved source-lineage detail. The source-origin manifest provides local lineage even where the original upstream revision was not recorded. Public license-reference commits identify the exact license files recovered during preparation, not an invented source pin for the supplied modules.

The original archive is identified by SHA256 `d7b492141920cac6b16650cb1c4a1670415080c04426e37b4576212037922d10`. The [statement baseline](../provenance/statement-baseline.json) and [preservation checker](../scripts/check_statement_preservation.py) compare original declaration signatures, mathematical definition bodies and contexts with the retained prepared sources. The baseline preserves records derived from the original supplied source; excluded modules do not require distribution of their baseline records. It is not regenerated from repaired proof statements. The checker normalizes documented visibility and helper-name changes, inventories the import-only build wrapper separately, and does not replace kernel validation.
