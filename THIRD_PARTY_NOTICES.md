# Third-party notices

tla2rs contains parts derived from the following works, used under their licenses.

## TLC (tlaplus/tlaplus)

`src/ppr.rs` is a Rust port of TLC's pretty printer for values (`tlc2.pprint`), so that tla2rs prints
states exactly as TLC does. Source: https://github.com/tlaplus/tlaplus

`src/pcal.rs` reproduces the text TLC's PlusCal translator (`pcal.Validator`) checksums, so that tla2rs warns
about a changed algorithm exactly when TLC does. It is written for tla2rs from TLC's measured behaviour and its
published sources.

`src/std_modules.rs` lists, for each of TLC's standard modules (`tla2sany/StandardModules/*.tla` in
tla2tools.jar), the modules it reads, its identifiers, keywords and numbers in the order they first appear, and its
strings, so that tla2rs orders strings as TLC does; and for each definition and declaration it exports, its name,
where it starts and ends and its number of parameters, so that tla2rs reports a name that clashes with one as SANY
does. It is generated from those module files; nothing else of their text is copied.

Some rules of `src/sany.rs` (`var_order`: the names SANY's context of a module holds, which decide the order TLC
prints variables in), `src/runtime.rs` (`fresh_fp`: the state whose VIEW TLC fingerprints under SYMMETRY) and
`src/codegen.rs` (`member_unsorted`: how TLC unites sets; `lazy_fun_string`: how it prints a function it cannot
enumerate) follow TLC 2.19's behaviour as measured and as read from its classes in tla2tools.jar
(`ModuleNode.getVariableDecls`, `Context`, `TLCStateMut.fingerPrint`, `SetEnumValue.cup`,
`FcnLambdaValue.toString`). They are written for tla2rs; no code of TLC is copied.

```
MIT License

Copyright (c) 199? HP Corporation
Copyright (c) 2003 Microsoft Corporation
Copyright (c) 2023 Linux Foundation

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

```

## TLA+ Examples (tlaplus/Examples)

`examples/TwoPhase.tla` is adapted from Leslie Lamport's `TwoPhase` specification in the TLA+ Examples
repository. Source: https://github.com/tlaplus/Examples

```
Copyright (c) 2016: The TLA+ project and other contributors:
https://github.com/tlaplus/Examples/graphs/contributors


Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```

## CommunityModules (tlaplus/CommunityModules)

`src/community.rs` provides modules of the CommunityModules (`Folds`, `Functions`, `FiniteSetsExt`,
`SequencesExt`, `UndirectedGraphs`, `Bitwise`, `Relation`, `BagsExt`, `Graphs`, `Combinatorics`, `Statistics`,
`GraphViz`, `DyadicRationals`, `VectorClocks`, `Quorum`, and parts of `Json` and `IOUtils`) for specs that extend
or instantiate them. Their definitions are written for tla2rs from each operator's documented meaning and from TLC
2.19's measured results on them; what is taken from the modules is their interface (the names each module exports,
in order, with their parameters, and what it extends), so that SANY's context, and the order TLC prints variables
in, come out the same, and the position TLC 2.19 reports for a CASE of `SequencesExt` that has no true condition
(measured). No text of the modules and no Java code of the release is copied. Source:
https://github.com/tlaplus/CommunityModules

```
MIT License

Copyright (c) 2019 TLA+

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
