module net.cruhland.axiomatic.Logic.Disjunction where

open import Function using (id; _∘_)

-- Export standard library definitions
open import Data.Sum public using () renaming
  (_⊎_ to _∨_
  ; inj₁ to ∨-introᴸ
  ; inj₂ to ∨-introᴿ
  ; [_,_] to ∨-elim
  ; [_,_]′ to ∨-rec
  ; fromInj₁ to ∨-recᴸ
  ; fromInj₂ to ∨-recᴿ
  ; swap to ∨-comm
  ; map to ∨-map
  ; map₁ to ∨-mapᴸ
  ; map₂ to ∨-mapᴿ
  )

∨-merge : ∀ {α} {A : Set α} → A ∨ A → A
∨-merge = ∨-rec id id

∨-assocᴸᴿ :
  ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨-assocᴸᴿ [A∨B]∨C = ∨-rec (∨-rec use-A use-B) use-C [A∨B]∨C
  where
    use-A = ∨-introᴸ
    use-B = ∨-introᴿ ∘ ∨-introᴸ
    use-C = ∨-introᴿ ∘ ∨-introᴿ

∨-assocᴿᴸ :
  ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
∨-assocᴿᴸ A∨[B∨C] = ∨-rec use-A (∨-rec use-B use-C) A∨[B∨C]
  where
    use-A = ∨-introᴸ ∘ ∨-introᴸ
    use-B = ∨-introᴸ ∘ ∨-introᴿ
    use-C = ∨-introᴿ
