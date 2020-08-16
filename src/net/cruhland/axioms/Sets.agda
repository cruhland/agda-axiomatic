module net.cruhland.axioms.Sets where

open import Level using (Setω)

-- Export names from child modules
open import net.cruhland.axioms.Sets.Base public using (SetAxioms)
open import net.cruhland.axioms.Sets.Complement public using (Complement)
open import net.cruhland.axioms.Sets.Comprehension public using (Comprehension)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.axioms.Sets.Difference public using (Difference)
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
    CM : Complement SA
    SC : Comprehension SA
    ES : EmptySet SA
    PS : PairSet SA
    PI : PairwiseIntersection SA
    PU : PairwiseUnion SA ES
    SD : Difference SA
    SS : SingletonSet SA

  open import net.cruhland.axioms.Sets.Base public using (El; Setoid)
  open Complement CM public
  open Comprehension SC public
  open Decidable SA public
  open Difference SD public
  open EmptySet ES public
  open Equality SA public
  open Finite SA CM ES PI PU SD SS public
  open PairSet PS public
  open PairwiseIntersection PI public
  open PairwiseUnion PU public
  open Properties SA CM ES PI PU SD public
  open SetAxioms SA public
  open SingletonSet SS public
  open Subset SA public
