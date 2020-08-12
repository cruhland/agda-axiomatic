module net.cruhland.models.Logic.Decidable where

open import Function using (id)
open import net.cruhland.models.Logic.Conjunction using (_∧_; ∧-intro)
open import net.cruhland.models.Logic.Disjunction
  using (_∨_; ∨-rec; ∨-introᴸ; ∨-introᴿ)
open import net.cruhland.models.Logic.Falsity using (⊥-elim; ¬_)

-- Export standard library definitions
open import Relation.Nullary public using
  (_because_; Dec; does; ofⁿ; ofʸ; no; yes)
open import Relation.Nullary.Decidable public
  using () renaming (map′ to dec-map)

¬¬-elim : {A : Set} → Dec A → ¬ (¬ A) → A
¬¬-elim (yes a) ¬¬a = a
¬¬-elim (no ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

¬[¬a∨¬b]→a∧b :
  {A B : Set} → Dec A → Dec B → ¬ (¬ A ∨ ¬ B) → A ∧ B
¬[¬a∨¬b]→a∧b (yes a) (yes b) ¬[¬a∨¬b] = ∧-intro a b
¬[¬a∨¬b]→a∧b (yes a) (no ¬b) ¬[¬a∨¬b] = ⊥-elim (¬[¬a∨¬b] (∨-introᴿ ¬b))
¬[¬a∨¬b]→a∧b (no ¬a) _ ¬[¬a∨¬b] = ⊥-elim (¬[¬a∨¬b] (∨-introᴸ ¬a))

∨-dec : ∀ {α β} {A : Set α} {B : Set β} → Dec A → Dec B → Dec (A ∨ B)
∨-dec (yes a) db = yes (∨-introᴸ a)
∨-dec (no ¬a) (yes b) = yes (∨-introᴿ b)
∨-dec (no ¬a) (no ¬b) = no (∨-rec ¬a ¬b)
