# geometrically-p

This repository hosts a formalisation project on geometrically-`P` schemes in Lean4
run at the [Formalising Algebraic Geometry](https://judithludwig.github.io/LeanWorkshop2025/)
workshop in Heidelberg in November 2025.

## Contents

We focus mostly on the properties
[geometrically irreducible](https://stacks.math.columbia.edu/tag/0364) and
[geometrically connected](https://stacks.math.columbia.edu/tag/0361).

The first goal is to show that both of these can be checked after base change
to any separably closed field: Let $\Omega$ be a separably closed field extension
of $k$. Then a $k$-scheme $X$ is geometrically irreducible
(resp. geometrically connected) if and only if the base change $X \times_{k} \Omega$
is irreducible (resp. connected).

## Structure

The project is split into a commutative algebra part
(in the `GeometricallyP/Algebra` folder) and a geometry part
(in `GeometricallyP/Geometry`). The geometry part consists of reduction and comparison
lemmas relating the geometric notions to the commutative algebra notions.

Most `sorry`s have accompanying comments containing references to theorems that should
be used in the proof. If the statement has a corresponding stacks project lemma,
the tag is given with the `@[stacks TAG]` attribute.

## Contributing

All project members have push access to non-master branches of this repository. To contribute,
please clone this project and work on a new branch. To add your changes to `master`, please open a
pull request from your branch.
