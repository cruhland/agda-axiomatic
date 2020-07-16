module net.cruhland.models.Logic.Decidable where

open import Function using (id)
open import net.cruhland.models.Logic.Conjunction using (_∧_; ∧-intro)
open import net.cruhland.models.Logic.Disjunction
  using (_∨_; ∨-rec; ∨-introᴸ; ∨-introᴿ)
open import net.cruhland.models.Logic.Falsity using (⊥-elim; ¬_)

-- Export standard library definitions
open import Relation.Nullary public using (no; yes) renaming (Dec to Decidable)

¬¬-elim : {A : Set} → Decidable A → ¬ (¬ A) → A
¬¬-elim (yes a) ¬¬a = a
¬¬-elim (no ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

¬[¬a∨¬b]→a∧b :
  {A B : Set} → Decidable A → Decidable B → ¬ (¬ A ∨ ¬ B) → A ∧ B
¬[¬a∨¬b]→a∧b (yes a) (yes b) ¬[¬a∨¬b] = ∧-intro a b
¬[¬a∨¬b]→a∧b (yes a) (no ¬b) ¬[¬a∨¬b] = ⊥-elim (¬[¬a∨¬b] (∨-introᴿ ¬b))
¬[¬a∨¬b]→a∧b (no ¬a) _ ¬[¬a∨¬b] = ⊥-elim (¬[¬a∨¬b] (∨-introᴸ ¬a))
