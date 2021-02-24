# Synthetic Undecidability of IMSELL via FRACTRAN

This repository is a tailored version of the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)
(git branch `coq-8.12`) designed to provide a faster path towards code review of the FSCD'21 submission 
[_Synthetic Undecidability of MSELL via FRACTRAN mechanised in Coq_](https://www.loria.fr/~larchey/papers/fscd21.pdf)
by Dominique Larchey-Wendling.

Indeed, the compilation time for the whole undecidability library could be more 
than half an hour, while the reduction chain from the Halting problem for Turing 
machines to IMSELL is much smaller and should require less than 3 minutes to compile
(with 4 threads).

## Requirements and installation

We recommend that you use [`opam 2`](https://opam.ocaml.org/) on your system to follow the instructions below.
The given script commands correspond to the BASH shell scripting language (`/bin/bash`).

### Upload the project

We advise you create a temporary directory to work in it. Then, use the following commands

```
wget -c https://github.com/DmxLarchey/coq-library-undecidability/archive/fscd21.zip
unzip fscd21.zip 
cd coq-library-undecidability-fscd21
```

### Coq 8.12 requirements

You need Coq `8.12` built on `OCAML >= 4.07.1`, the [Smpl](https://github.com/uds-psl/smpl) package, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. In addition, to review to Coq code, you might want to install CoqIDE `8.12`.

Notice that installing Coq, Equations and MetaCoq from scratch takes some time, possibly ten minutes of compilation.

We recommand that you work in the `coq-library-undecidability-fscd21` directory created in the 
previous section.

If you are using `opam 2` you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda --jobs=4
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only --jobs=4
```

Notice that the command `opam install . --deps-only --jobs=4` above has to be run from the
project directory `coq-library-undecidability-fscd21` because there belongs the
`opam` file that contains the list of required dependencies.

If you want to use CoqIDE to review the code, you can install it with e.g.

```
opam install coqide --jobs=4
eval $(opam env)
```

## Compilation of the IMSELL undecidability result

**Do not type `make all`** if you do not intend to compile the whole library. This takes a lot of time.

Instead we recommend that you type which will only compile the files involved in the
reduction chain from Turing machines halting to IMSELL:

```
cd theories
make -j 4 ILL/IMSELL_undec.vo
```

On a recent computer, this compilation phase should take less than 3 minutes.

## Code review

**After compilation**, you can review the Coq code with your favorite IDE. 
Below are direct links to code relevant to the IMSELL undecidability result:

- `FRACTRAN`: [`FRACTRAN.v`](theories/FRACTRAN/FRACTRAN.v), 
[`fractran_utils.v`](theories/FRACTRAN/FRACTRAN/fractran_utils.v), 
[`FRACTRAN_undec.v`](theories/FRACTRAN/FRACTRAN_undec.v)
- `MinskyMachines`: [`MM.v`](theories/MinskyMachines/MM.v), 
[`MMA.v`](theories/MinskyMachines/MMA.v), 
[`mma_defs.v`](theories/MinskyMachines/MMA/mma_defs.v), 
[`mma_utils.v`](theories/MinskyMachines/MMA/mma_utils.v),
[`fractran_mma.v`](theories/MinskyMachines/MMA/fractran_mma.v),
[`FRACTRAN_to_MMA2.v`](theories/MinskyMachines/Reductions/FRACTRAN_to_MMA2.v),
[`MMA2_undec.v`](theories/MinskyMachines/MMA2_undec.v),
[`ndMM2.v`](theories/MinskyMachines/ndMM2.v),
[`MMA2_to_ndMM2_ACCEPT.v`](theories/MinskyMachines/Reductions/MMA2_to_ndMM2_ACCEPT.v)
[`ndMM2_undec.v`](theories/MinskyMachines/ndMM2_undec.v)
- `ILL`: [`IMSELL.v`](theories/ILL/IMSELL.v), 
[`imsell.v`](theories/ILL/Ll/imsell.v), 
[`ndMM2_IMSELL.v`](theories/ILL/Reductions/ndMM2_IMSELL.v), 
[`IMSELL_undec.v`](theories/ILL/IMSELL_undec.v)









