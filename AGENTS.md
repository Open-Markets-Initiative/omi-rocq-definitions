# Agent Notes

Every file in this repository is generated from the Open Markets Initiative binary data
models. Editing one here is lost on the next generation: the change belongs in the generator
or in the model it reads.

## What is here

- `Wire.v` — the prelude every definition imports: the field kinds, their encoders and
  decoders, and the lemmas the generated proofs lean on. Written by hand once, and proved.
- `<organization>/<division>/<protocol>/<Name>.v` — one definition per protocol framing, a
  module of record modules, each carrying its own proofs.
- `_CoqProject`, `Makefile` — what the prover builds, prelude first.

## Checking it

```sh
docker run --rm -v "$PWD:/work" -w /work rocq/rocq-prover:9.0 \
  sh -c 'rocq makefile -f _CoqProject -o Makefile.rocq && make -f Makefile.rocq -j4'
```

A definition that does not check is a generator defect, not a file to patch.

## What a proof here claims

For each record: that an encoding is as wide as its fields say, and that decoding what was
encoded gives the record back and leaves the bytes after it alone. The second asks the
record's `bounded` predicate, because a field is an `N` and its width is what bounds it.

A definition's header says what of its model it does **not** state — the framing, the
dispatch, a counted run — so nothing here is read as a claim about a whole packet.

## The same protocols, elsewhere

The Open Markets Initiative provides protocol definitions in several formats:

- [Kaitai Struct Definitions][Kaitai.Definitions.Repository] — Cross language binary parsers with the kaitai struct compiler
- [DFDL Definitions][Dfdl.Definitions.Repository] — Declarative DFDL schemas for cross language parsing
- [P4 Definitions][P4.Definitions.Repository] — P4 programs for software and hardware data planes
- [Spicy Definitions][Spicy.Definitions.Repository] — Declarative Spicy grammars for the spicy toolchain and the zeek network security monitor
- [Lean Definitions][Lean.Definitions.Repository] — Lean 4 definitions with machine checked encode and decode proofs
- [TLA+ Definitions][Tla.Definitions.Repository] — TLA+ modules whose encode and decode are model checked with TLC
- [FIX Dictionaries][Fix.Dictionaries.Repository] — QuickFIX format xml data dictionaries, one per FIX version
- [Xml Specifications][Xml.Specifications.Repository] — Formatted exchange specification xmls

[Kaitai.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-kaitai-struct-definitions "Omi Kaitai Struct Definitions"
[Dfdl.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-dfdl-definitions "Omi DFDL Definitions"
[P4.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-p4-definitions "Omi P4 Definitions"
[Spicy.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-spicy-definitions "Omi Spicy Definitions"
[Lean.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-lean4-definitions "Omi Lean Definitions"
[Tla.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-tlaplus-definitions "Omi TLA+ Definitions"
[Fix.Dictionaries.Repository]: https://github.com/Open-Markets-Initiative/omi-fix-dictionaries "Omi FIX Dictionaries"
[Xml.Specifications.Repository]: https://github.com/Open-Markets-Initiative/omi-xml-specifications "Omi Xml Specifications"
