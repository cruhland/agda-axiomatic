module net.cruhland.models.Function where

-- Export standard library definitions
open import Function public
  using (_∘_; const; flip; id) renaming (Morphism to _⟨→⟩_)
open import Function.Equivalence public using (Equivalence)
