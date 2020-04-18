open import Function using (id)
open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.axiomatic.Logic.Decidable (LB : LogicBundle) where
  open LogicBundle LB

  Decidable : Set → Set
  Decidable A = A ∨ ¬ A

  ¬¬-elim : {A : Set} → Decidable A → ¬ (¬ A) → A
  ¬¬-elim a∨¬a ¬¬a = ∨-elim a→a ¬a→a a∨¬a
    where
      a→a = id
      ¬a→a = λ ¬a → ⊥-elim (¬¬a ¬a)

  ¬[¬a∨¬b]→a∧b :
    {A B : Set} → Decidable A → Decidable B → ¬ (¬ A ∨ ¬ B) → A ∧ B
  ¬[¬a∨¬b]→a∧b a∨¬a b∨¬b ¬[¬a∨¬b] = ∨-elim a→a∧b ¬a→a∧b a∨¬a
    where
      ¬a→a∧b = λ ¬a → ⊥-elim (¬[¬a∨¬b] (∨-introᴸ ¬a))
      ¬b→a∧b = λ ¬b → ⊥-elim (¬[¬a∨¬b] (∨-introᴿ ¬b))
      a→a∧b = λ a → ∨-elim (∧-intro a) ¬b→a∧b b∨¬b
