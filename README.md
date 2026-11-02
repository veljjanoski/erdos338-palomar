# Erdős Problem 338: restricted order of robust sets of positive lower density

[![CI](https://github.com/veljjanoski/erdos338-palomar/actions/workflows/ci.yml/badge.svg)](https://github.com/veljjanoski/erdos338-palomar/actions/workflows/ci.yml)

A Lean 4 proof of a partial result on
[Erdős Problem 338](https://www.erdosproblems.com/338), prepared for the
[Palomar](https://palomar-registry.org/) registry (submission form:
<https://submit.palomar-registry.org/>).

The restricted order of $A \subseteq \mathbb{N}$ is the least $t$, if it exists, such that every
sufficiently large integer is a sum of at most $t$ distinct elements of $A$. Erdős and Graham asked
whether $A$ has a restricted order whenever $A \setminus F$ is a basis for every finite set $F$.

- `Erdos338.erdos_338.variants.lowerDensity_pos`: if $A \setminus F$ is a basis for every finite
  $F$ and $A$ has positive lower density, then $A$ has a restricted order.

The definitions `Set.partialDensity`, `Set.lowerDensity`, `Erdos338.HasOrder` and
`Erdos338.HasRestrictedOrder` in `Challenge.lean` are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjecturesForMathlib/Data/Set/Density.lean` and `FormalConjectures/ErdosProblems/338.lean`
at commit `d995ef5d306637c0a2e489c7e579647168d7df2f`). The hypothesis on $A$ is the one of
`erdos_338.variants.basis_after_finite_removal` there. The statement with a density hypothesis is
not in formal-conjectures.

The statement is the existence part of Theorem 1 of
[veljjanoski/erdos338](https://github.com/veljjanoski/erdos338), which also bounds the
restricted order in terms of the lower density; the Lean proof does not keep that bound.
It follows the proof there with two changes: Kneser's theorem on the lower density of sumsets,
which is not available in Lean, is replaced by Kneser's theorem for finite abelian groups, and the
residue class is fixed directly from the hypothesis (step 1 below). Let $\delta > 0$ be less than
the lower density of $A$.

1. Every residue class modulo every $Q \geq 1$ contains a sum of distinct elements of $A$. Remove
   the elements of $A$ in classes with only finitely many of them; the rest is still a basis, and
   each summand can be replaced by a different element of the same class.
2. For every $R$, the set $M_R$ of numbers with at least $R$ representations $a + b$ with
   $a \neq b$ in $A$ has lower density at least $\delta^2/8$, by counting pairs.
3. There is $K$, depending only on $\delta$, such that all large numbers in one residue class
   modulo some $d \leq K$ are sums of exactly $K$ elements of $M_R$. After normalising the set,
   this uses Kneser's theorem in $\mathbb{Z}/\ell\mathbb{Z}$ for suitable elements $\ell$
   (`Erdos338/Covering.lean`, `Erdos338/Structure.lean`, `Erdos338/Shift.lean`).
4. Fix the residue class with a set $S_0$ from step 1 for the modulus $K!$, so that $|S_0|$ does
   not depend on $R$. With $R$ large, each of the $K$ elements of $M_R$ is $a + b$ with $a$ and
   $b$ not used before, as in Hegyvári, Hennecart and Plagne (Combin. Probab. Comput. 16 (2007)).

Kneser's theorem for finite abelian groups (`Finset.add_kneser`) is the Lean proof by Mantas
Bakšys and Yaël Dillies in [misc-yd](https://github.com/YaelDillies/misc-yd) (Apache-2.0), copied
into `Erdos338/Kneser` at commit `f2f1d413b681dfd7a0f0e8481aee3ab7e0bae7ba` (the changes are listed
at the top of each file).

Not formalized: the explicit bound of Theorem 1, Theorem 2 of the source (block model), and the
questions of Problem 338 for sets of lower density $0$.

## Repository map

- `Challenge.lean`: the statement (with `sorry`) a reader audits.
- `Solution.lean`: the same declaration with a proof.
- `Erdos338/`: the lemmas used by the proof, and the copy of Kneser's theorem.
- `comparator.json`: the declarations `lake comparator` checks.
- `formalization.yaml`: provenance, authorship, automation and review metadata.
- `scripts/`, `test/`, `Gemfile*` and `.github/workflows/ci.yml` come from
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate).

Build with `lake exe cache get && lake build`; check with `scripts/verify-comparator.sh` (Linux,
needs `bwrap`).

## Licence

Apache License 2.0, see `LICENSE`. The definitions copied from formal-conjectures and the files
copied from misc-yd are also under Apache-2.0.
