# Gap Report — MiniAlgebraicGroups

## Missing Proofs

The following deep theorems are stated as axioms, as their
full proofs require substantial algebraic geometry machinery:

1. **Lie-Kolchin theorem**: Full algebraic geometry proof
   requires the Borel fixed point theorem on flag varieties.
   A proof sketch is provided.

2. **Borel fixed point theorem**: Requires the theory of
   complete varieties and the fact that Ga/Gm orbits on
   complete varieties are points. Proof sketch provided.

3. **Jordan decomposition**: Full proof requires the
   decomposition of matrices over algebraically closed fields.
   Statement and properties formalized.

4. **Classification of reductive groups**: Chevalley's
   classification theorem is stated as axiom.

5. **Lang's theorem**: Proof requires etale cohomology
   and the Lang map being an etale covering.

6. **Deligne-Lusztig theory**: Full theory requires
   etale cohomology of algebraic varieties over finite fields.

7. **Springer correspondence**: Full proof requires
   perverse sheaves and intersection cohomology.

## Missing Lean Formalizations

1. **Full polynomial ring implementation**: The current
   polynomial ring is a placeholder. A full implementation
   with evaluation on matrices would require substantial code.

2. **Determinant for general n**: Only det1, det2, det3
   are defined. The general Leibniz formula would require
   permutation group implementation.

3. **Matrix inverse**: Defined axiomatically as identity
   (placeholder). Full implementation requires the adjugate formula.

4. **Algebraic variety structure**: The precise definition
   of algebraic varieties as ringed spaces with sheaf of
   regular functions is abstracted away.

## Priority Improvements

| Priority | Item | Effort |
|----------|------|--------|
| High | Implement general determinant for n×n matrices | Medium |
| High | Implement matrix inverse via adjugate | Medium |
| Medium | Proper polynomial evaluation on matrix entries | High |
| Medium | Full algebraic set zero-locus definition | High |
| Low | Etale cohomology for Lang/Deligne-Lusztig proofs | Very High |
