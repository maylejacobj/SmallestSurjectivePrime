# SmallestSurjectivePrime

This repository contains the code accompanying the paper *A uniform bound on the smallest surjective prime* by Tyler Genao, Jacob Mayle, and Jeremy Rouse.

The goal of the code is to construct models of the modular curves that appear in the paper, provably determine their rational places, and give an analysis of the j-invariants. We consider modular curves that are fiber products of two prime-power level modular curves. In most cases, we construct these models using the function `ConstructFiberProduct`, but in two cases, we rely on Zywina's `FindModelOfXG`. The models produced by `ConstructFiberProduct` tend to be singular. We provably compute all rational places by calling the functions `RationalPlacesGenus1` or `RationalPlacesGenus2`, or by checking local solvability, as appropriate. In one case, we follow an ad hoc method that involves taking a quotient by an automorphism. The function `AnalyzePlaces` provides the relevant analysis of each rational place, printing the j-invariant, whether it is CM, and the nonsurjective primes.

## Installation Instructions
1. Install the latest version of Magma (at least v2.27) from [http://magma.maths.usyd.edu.au/magma/](http://magma.maths.usyd.edu.au/magma/).
2. Download **ell-adic-galois-images** from [https://github.com/AndrewVSutherland/ell-adic-galois-images](https://github.com/AndrewVSutherland/ell-adic-galois-images).
3. Download **OpenImage** from [https://github.com/davidzywina/OpenImage](https://github.com/davidzywina/OpenImage).
4. Download *FiberProducts.m* from [https://github.com/maylejacobj/SmallestSurjectivePrime](https://github.com/maylejacobj/SmallestSurjectivePrime).
5. Modify the file paths in lines 8 and 16 of *FiberProducts.m* as appropriate.

Please contact us with any questions, comments, or suggestions.
