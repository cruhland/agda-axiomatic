module net.cruhland.axiomatic.Sets where

open import Level using (Setω)
open import net.cruhland.axiomatic.Sets.Base using (SetAxioms)
open import net.cruhland.axiomatic.Sets.Empty using (EmptySet)
import net.cruhland.axiomatic.Sets.Equality as Equality
open import net.cruhland.axiomatic.Sets.Singleton using (SingletonSet)
open import net.cruhland.axiomatic.Sets.Union using (PairwiseUnion)

-- Bundle all child modules together for convenience
record SetTheory : Setω where
  field
    SA : SetAxioms
    ES : EmptySet SA
    PU : PairwiseUnion SA
    SS : SingletonSet SA

  open import net.cruhland.axiomatic.Sets.Base public using (El; Setoid)
  open EmptySet ES public
  open Equality SA public
  open PairwiseUnion PU public
  open SetAxioms SA public
  open SingletonSet SS public
