module net.cruhland.axioms.Sets where

open import Level using (Setω)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.Finite as Finite
import net.cruhland.axioms.Sets.Properties as Properties
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)

-- Bundle all child modules together for convenience
record SetTheory : Setω where
  field
    SA : SetAxioms
    ES : EmptySet SA
    PU : PairwiseUnion SA
    SS : SingletonSet SA

  open import net.cruhland.axioms.Sets.Base public using (El; Setoid)
  open EmptySet ES public
  open Equality SA public
  open Finite SA ES PU SS public
  open PairwiseUnion PU public
  open Properties SA public
  open SetAxioms SA public
  open SingletonSet SS public
  open Subset SA public
