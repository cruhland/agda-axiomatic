open import Data.List.Base using ([]; _∷_; List)
open import net.cruhland.models.Logic using (Dec; no; yes)
open import net.cruhland.models.Setoid using (Setoid; Setoid₀)

-- Replacement for some standard library list functions that require a Setoid
module net.cruhland.models.Sets.List (S : Setoid₀) where

open Setoid S using () renaming (Carrier to A)

private
  variable
    P : A → Set

filter : (∀ x → Dec (P x)) → List A → List A
filter P? [] = []
filter P? (x ∷ xs) with P? x
... | (no _) = filter P? xs
... | (yes _)  = x ∷ filter P? xs
