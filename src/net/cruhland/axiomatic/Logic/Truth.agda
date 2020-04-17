module net.cruhland.axiomatic.Logic.Truth where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Truth (⊤ : Set) : Set₁ where
  field
    ⊤-intro : ⊤
    ⊤-elim : {A : Set} → A → ⊤ → A

    ⊤-β : ∀ {A} {a : A} → ⊤-elim a ⊤-intro ≡ a

    ⊤-η : {t : ⊤} → ⊤-elim ⊤-intro t ≡ t
