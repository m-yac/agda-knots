# Agda Knots

An experimental formalization of Knot Theory in Agda, with specific attention paid to Legendrian Knot Theory.

### Structure

- `Knot.Prelude`: Basic definitions and imports from `standard-library`. 
- `Knot.FrontDiagram`: The definition of the front diagram of a tangle, the general case of a diagram of a knot/link. More examples coming soon.
- `Knot.FrontDiagram.Properties`: Facts that show front diagrams behave as we'd expect -- in categorial language, that they form a pre-monoidal category.
- `Knot.Isotopy`: The definition of Legendrian and smooth isotopy of tangles -- i.e. defining when two diagrams represent the same knot (the usual notion being smooth isotopy).
- `Knot.Isotopy.Properties`: Coming soon. Facts that show tangles mod isotopy form a monoidal category -- i.e. behave like tangles.
- `Knot.Invariant`: Coming soon. Proving that a function on tangles respects isotopy.

#### Other Files	

- `Category.Monoidal`: A formalization of the basic theory of monoidal categories, parameterized by some notion of equality. In the style of `standard-library`'s `Algebra`.
- `Relation.Binary.Dependent`: The notion of equality of morphisms used in the above -- tries to capture the notion of an equality that respects an equality, and is likely not the best way to do so.
- `Data.IntMod`: A definitions of the integers mod n, using `standard-library`'s `Data.Nat.DivMod`.

## TODO

- Re-prove invariance of tb, etc. w/ the new definition of Isotopy
- Definitions (in terms of stabilizations, etc.) of (some?) remaining *smooth* Reidemeister moves
- Prove that more invariants are actually invariant
- Define equality of objects in monoidal categories in the 'right' way? (*What would that be?*)
- More documentation, explanation, references throughout
- Some of the Legendrian Knot Atlas as examples
- Independence of `--rewriting`?