module net.cruhland.axioms.Sets where

open import Level using (Setω)

-- Export names from child modules
open import net.cruhland.axioms.Sets.Base public using (SetAxioms)
open import net.cruhland.axioms.Sets.Comprehension public using (Comprehension)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Difference as Difference
open import net.cruhland.axioms.Sets.Empty public using (EmptySet)
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.Finite as Finite
open import net.cruhland.axioms.Sets.Intersection public using
  (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Pair public using (PairSet)
import net.cruhland.axioms.Sets.Properties as Properties
open import net.cruhland.axioms.Sets.Singleton public using (SingletonSet)
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.axioms.Sets.Union public using (PairwiseUnion)

-- Bundle all child modules together for convenience
record SetTheory : Setω where
  field
    SA : SetAxioms
    SC : Comprehension SA
    ES : EmptySet SA
    PS : PairSet SA
    PI : PairwiseIntersection SA
    PU : PairwiseUnion SA ES
    SS : SingletonSet SA

  open import net.cruhland.axioms.Sets.Base public using (El; Setoid)
  open Comprehension SC public
  open Decidable SA public
  open Difference SA SC public
  open EmptySet ES public
  open Equality SA public
  open Finite SA ES PI PU SS public
  open PairSet PS public
  open PairwiseIntersection PI public
  open PairwiseUnion PU public
  open Properties SA ES PI PU public
  open SetAxioms SA public
  open SingletonSet SS public
  open Subset SA public
