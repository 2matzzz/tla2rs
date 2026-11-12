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
strings, so that tla2rs orders strings as TLC does. It is generated from those module files; nothing else of their
text is copied.

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
