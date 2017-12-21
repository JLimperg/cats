# Generate Everything.agda

This tool generates a file `Everything.agda` which imports all library files.
Typechecking `Everything.agda` will then typecheck each library module exactly
once.

The code is based on [GenerateEverything.hs from the Agda standard
library](https://github.com/agda/agda-stdlib/blob/964dc0cf1dd3eead91e6ddc1056d733bf245deaf/GenerateEverything.hs),
adapted under the MIT license (see `LICENSE`).
