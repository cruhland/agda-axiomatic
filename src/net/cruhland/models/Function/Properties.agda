module net.cruhland.models.Function.Properties where

import net.cruhland.axioms.Eq as Eq
open import net.cruhland.models.Function using (_∘′_; _⟨→⟩_; flip)

instance
  ⟨→⟩-transitive : ∀ {β} → Eq.Transitive {β = β} _⟨→⟩_
  ⟨→⟩-transitive = Eq.transitive (flip _∘′_)
