module net.cruhland.axiomatic.Sets where

open import Level using (Setω)
open import net.cruhland.axiomatic.Sets.Base using (SetAxioms)
import net.cruhland.axiomatic.Sets.Equality as Equality

-- Bundle all child modules together for convenience
record SetTheory : Setω where
  field
    SA : SetAxioms

  open import net.cruhland.axiomatic.Sets.Base public using (El; Setoid)
  open Equality SA public
  open SetAxioms SA public
