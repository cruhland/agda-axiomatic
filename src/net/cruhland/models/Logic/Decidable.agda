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
open import Relation.Nullary.Negation public using (¬?)
open import Relation.Nullary.Product public
  using () renaming (_×-dec_ to _∧?_)
open import Relation.Nullary.Sum public
  using () renaming (_⊎-dec_ to _∨?_)

¬¬-elim : {A : Set} → Dec A → ¬ (¬ A) → A
¬¬-elim (yes a) ¬¬a = a
¬¬-elim (no ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

¬[¬a∨¬b]→a∧b :
  {A B : Set} → Dec A → Dec B → ¬ (¬ A ∨ ¬ B) → A ∧ B
¬[¬a∨¬b]→a∧b (yes a) (yes b) ¬[¬a∨¬b] = ∧-intro a b
¬[¬a∨¬b]→a∧b (yes a) (no ¬b) ¬[¬a∨¬b] = ⊥-elim (¬[¬a∨¬b] (∨-introᴿ ¬b))
¬[¬a∨¬b]→a∧b (no ¬a) _ ¬[¬a∨¬b] = ⊥-elim (¬[¬a∨¬b] (∨-introᴸ ¬a))
