module net.cruhland.axiomatic.Logic.Decidable where

open import Function using (id)
open import net.cruhland.axiomatic.Logic.Conjunction using (_∧_; ∧-intro)
open import net.cruhland.axiomatic.Logic.Disjunction
  using (_∨_; ∨-rec; ∨-introᴸ; ∨-introᴿ)
open import net.cruhland.axiomatic.Logic.Falsity using (⊥-elim; ¬_)

Decidable : Set → Set
Decidable A = A ∨ ¬ A

¬¬-elim : {A : Set} → Decidable A → ¬ (¬ A) → A
¬¬-elim a∨¬a ¬¬a = ∨-rec a→a ¬a→a a∨¬a
  where
    a→a = id
    ¬a→a = λ ¬a → ⊥-elim (¬¬a ¬a)

¬[¬a∨¬b]→a∧b :
  {A B : Set} → Decidable A → Decidable B → ¬ (¬ A ∨ ¬ B) → A ∧ B
¬[¬a∨¬b]→a∧b a∨¬a b∨¬b ¬[¬a∨¬b] = ∨-rec a→a∧b ¬a→a∧b a∨¬a
  where
    ¬a→a∧b = λ ¬a → ⊥-elim (¬[¬a∨¬b] (∨-introᴸ ¬a))
    ¬b→a∧b = λ ¬b → ⊥-elim (¬[¬a∨¬b] (∨-introᴿ ¬b))
    a→a∧b = λ a → ∨-rec (∧-intro a) ¬b→a∧b b∨¬b
