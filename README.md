# Polynomial Laws and the Universal Divided Power Algebra

This repository contains source code for the article "Formalizing polynomial laws and the universal divided power algebra", [accepted to CPP 2026](https://popl26.sigplan.org/details/CPP-2026-papers/25/Formalizing-polynomial-laws-and-the-universal-divided-power-algebra). 
The code runs over Lean 4 (v4.26.0-rc2) and Mathlib's version [e814276](https://github.com/leanprover-community/mathlib4/tree/e81427609bffc55e8686f7315e5122dd10c4bed1) (November 26, 2025).

The goal of this paper is to present an ongoing formalization, in the framework provided by the Lean/Mathlib mathematical library, of the construction by Roby (1965) of the universal divided power algebra. This is an analogue, in the theory of divided powers, of the classical algebra of polynomials. It is a crucial tool in the development of crystalline cohomology; it is also used in $p$-adic Hodge theory to define the crystalline period ring. 

As an algebra, this universal divided power algebra has a fairly simple definition that shows that it is a graded algebra. The main difficulty in Roby's theorem lies in constructing a divided power structure on its augmentation ideal. To that aim, Roby identified the graded pieces with another universal structure: homogeneous polynomial laws.

We formalize the first steps of the theory of polynomial laws and show how future work will allow to complete the formalization of the above-mentioned divided power structure.

We report on various difficulties that appeared in this formalization: taking care of universes, extending to semirings some aspects of the Mathlib library, and coping with several instances of "invisible mathematics".

## Installation instructions

The formalization has been developed over Lean 4 and its mathematical library Mathlib. For detailed instructions to install Lean, Mathlib, and supporting tools, visit the [Lean Community website](https://leanprover-community.github.io/get_started.html).

After installation, run the commands `git clone https://github.com/mariainesdff/divided_power_algebra_journal.git` to obtain a local copy of the repository and `lake exe cache get!` to download a compiled Mathlib. To open the project in VS Code, either run `path/to/divided_power_algebra_journal` on the command line, 
or use the "Open Folder" menu option to open the project's root directory. To compile the whole project locally, use the command `lake build`.
