# Verilog-Rocq

A Verilog semantics in Rocq for foundational hardware verification, forked from the
artifact of Choi, Kim and Kang, *Revamping Verilog Semantics for Foundational
Verification* (OOPSLA 2025). Their development provides a least-fixpoint cycle
semantics, its equivalence with the standard scheduling semantics, and an ITree module
layer with a verified pipelined RISC-V core. This project extends it with a
desugaring front end (source-to-source rewrites with preservation proofs), a
decidable completeness check guaranteeing that nothing in a design is silently
dropped, and ITree-level module composition. Designs are refined against the
`risc-v-itree` ITree specification of RISC-V. Targets: RISC-V designs first, AI
accelerators later.

Provenance of the imported code and every deviation from it is in `docs/UPSTREAM`; the
paper-to-code map from the artifact is in `docs/upstream-artifact-README.md` and still
applies to `src/`.

## Layout

| Path | What |
|---|---|
| `src/Lib/` | Semantic domain: hierarchical maps (`HMap.v`), sized integers (`SZ.v`), tactics. |
| `src/Lang/` | Verilog syntax (`Syntax.v`), the LFP semantics (`Semantics.v`), port analysis, module transition functions, the ITree module layer (`ModuleITree.v`). |
| `src/Lang/Equiv/` | Equivalence of the LFP semantics with the standard scheduling semantics. |
| `src/Ex/RvCore/` | Pipelined RISC-V core (Verilog, embedded via the notation in `Syntax.v`), its caches and frontend, and the per-module simulation proofs. |
| `attic/RvCore-riscv-coq/` | The artifact's RISC-V reference spec and end-to-end theorem, written against `riscv-coq`; parked until redone against `RiscVITree`. Not built. |
| `dep/FreeSim/` | CCR-project/FreeSim (stuttering simulations over ITrees), ported to Rocq 9.0. |
| `dep/Ordinal/` | snu-sf/Ordinal 0.5.6, FreeSim's dependency. |
| `flake.nix` | Rocq 9.0 toolchain and libraries, including `risc-v-itree`. |

All three directories are dune theories: `VerilogRocq` (`src/`), `FreeSim`, `Ordinal`.

## Building

Requires Nix with flakes, and access to the `risc-v-itree` checkout the flake points at
(see the input comment in `flake.nix`; it carries its own nixpkgs pin and the overlays
for stdpp, iris and stdpp-itree).

```sh
nix develop      # Rocq 9.0.1, dune, coqutil, ITree, paco, ExtLib, risc-v-itree
dune build       # builds dep/ and src/; a full check takes a few minutes
```

Notes:
- Rocq 9.0 ships its standard library as a separate package; it is in the shell as
  `stdlib`, and every `(coq.theory)` lists `Stdlib` in `(theories ...)`.
- Dune binds load paths only for theories named in `(theories ...)`, so `src/dune`
  lists the whole transitive closure it uses.
- `Syntax.v` defines a large custom-entry grammar for writing Verilog inside Rocq. On
  9.0 this emits `notation-incompatible-prefix` warnings by the hundreds; they are
  disabled in `src/dune`. The case study parses through that grammar and builds, so the
  notations work for the constructs it uses.

## Gaps in the semantics, and the plan

From a read of `src/Lang/Semantics.v`; items marked *unconfirmed* still need a test
module.

**Silently dropped.** `TrsNotSupported` and `TrsUndriven` failures are swallowed at the
generate-block and module-item levels (`iterate_resume`, `~> iff`), so an unsupported
`always` block never produces updates and the affected signals are simply absent at the
fixpoint. `Analysis.v` only extracts port directions (`getIOIds`); there is no
completeness check anywhere. A design that "runs" has not necessarily been fully
interpreted.

**Computed differently from Verilog, without error.**
- `always @*` / `always @(*)` is treated as sequential; only `always_comb` is combinational (`isComb`).
- Event controls `@(...)` are ignored, so `posedge`/`negedge` are the same and an asynchronous reset becomes synchronous.
- `casez` / `casex` behave as `case` (`cty` unused).
- Function return values come only from `return`; a `return` inside `if`/`case` and the `fname = expr` style are lost (*unconfirmed*).

**Rejected with `TrsNotSupported`.**
- Expressions: indexed part-select `x[i +: W]`, `++`/`--`.
- L-values: anything other than an identifier, hierarchical name or a single index (no `x[7:4] = …`, no `{a,b} = …`).
- Statements: all loops. `trsVStatementForLoop` (bounded unrolling) exists but is not wired into `trsVStatementItem`.
- Module items: `initial`; task declarations are ignored, so task calls fail.
- Instantiation: parameter overrides are destructured but unused in `trsVModuleIns`.

**Planned desugaring passes** (each with a preservation lemma):

| Source | Rewrite to |
|---|---|
| `always @*`, `always @(*)` | `always_comb` |
| `x[i +: W]` | `(x >> i)[W-1:0]` |
| `x[7:4] = e`, `{a,b} = e` | whole-variable read-modify-write |
| loops with static bounds | unrolled (or, in the ITree statement semantics, `iter`) |
| branch-internal `return`, `fname = expr` | temporary plus one final `return` |
| `casez`/`casex` with wildcards | masked-compare `if` chain |
| parameterised instantiation | specialised module per parameter set |
| compound assignments (`+=` …) | plain assignments |
| asynchronous reset, `initial`, latches | rejected with an error, not dropped |

Plus the completeness predicate: decidable, proved sound, and passing means every
construct is in the supported fragment and every declared net and output has a value
at the fixpoint.

**ITree layering, planned.** A statement-level denotation into state events
(`Read`/`WriteWire`/`WriteFlop`) under the existing cycle fixpoint, giving loops a
semantics by `iter` and connecting to `Semantics.v` by a theorem on the loop-free
fragment; above the fixpoint, module composition by interpreting a child's
`Input`/`Output` events in the parent, which is also where multiple clock domains
become expressible.
