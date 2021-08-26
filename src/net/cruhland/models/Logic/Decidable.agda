open import net.cruhland.models.Logic.Conjunction using (_∧_; ∧-intro)
open import net.cruhland.models.Logic.Disjunction
  using (_∨_; ∨-introᴸ; ∨-introᴿ; ¬[a∨b]-from-¬a∧¬b)
open import net.cruhland.models.Logic.Falsity
  using (⊥; ¬_; ¬-intro; contrapositive; _↯_)
open import net.cruhland.models.Logic.Truth using (⊤)

module net.cruhland.models.Logic.Decidable where

-- Some definitions adapted from standard library
data Dec {α} (A : Set α) : Set α where
  yes : A → Dec A
  no : ¬ A → Dec A

module _ {α} {A : Set α} where

  True : Dec A → Set
  True (yes _) = ⊤
  True (no _) = ⊥

  False : Dec A → Set
  False (no _) = ⊤
  False (yes _) = ⊥

  toWitness : {Q : Dec A} → True Q → A
  toWitness {Q = yes a} _ = a
  toWitness {Q = no ¬a} ()

  toWitnessFalse : {Q : Dec A} → False Q → ¬ A
  toWitnessFalse {Q = yes a} ()
  toWitnessFalse {Q = no ¬a} _ = ¬a

  dec-map : ∀ {β} {B : Set β} → (A → B) → (B → A) → Dec A → Dec B
  dec-map fwd rev (yes a) = yes (fwd a)
  dec-map fwd rev (no ¬a) = no (contrapositive rev ¬a)

¬? : {A : Set} → Dec A → Dec (¬ A)
¬? (yes a) = let ¬¬a = ¬-intro λ ¬a → a ↯ ¬a in no ¬¬a
¬? (no ¬a) = yes ¬a

infixr 2 _∧?_
_∧?_ : {A B : Set} → Dec A → Dec B → Dec (A ∧ B)
(yes a) ∧? (yes b) = yes (∧-intro a b)
(yes a) ∧? (no ¬b) = no (¬-intro λ { (∧-intro a b) → b ↯ ¬b })
(no ¬a) ∧? _ = no (¬-intro λ { (∧-intro a b) → a ↯ ¬a })

infixr 1 _∨?_
_∨?_ : {A B : Set} → Dec A → Dec B → Dec (A ∨ B)
(yes a) ∨? _ = yes (∨-introᴸ a)
(no ¬a) ∨? (yes b) = yes (∨-introᴿ b)
(no ¬a) ∨? (no ¬b) = no (¬[a∨b]-from-¬a∧¬b ¬a ¬b)

¬¬-elim : {A : Set} → Dec A → ¬ (¬ A) → A
¬¬-elim (yes a) ¬¬a = a
¬¬-elim (no ¬a) ¬¬a = ¬a ↯ ¬¬a

¬[¬a∨¬b]→a∧b :
  {A B : Set} → Dec A → Dec B → ¬ (¬ A ∨ ¬ B) → A ∧ B
¬[¬a∨¬b]→a∧b (yes a) (yes b) ¬[¬a∨¬b] =
  ∧-intro a b
¬[¬a∨¬b]→a∧b (yes a) (no ¬b) ¬[¬a∨¬b] =
  let ¬a∨¬b = ∨-introᴿ ¬b in ¬a∨¬b ↯ ¬[¬a∨¬b]
¬[¬a∨¬b]→a∧b (no ¬a) _ ¬[¬a∨¬b] =
  let ¬a∨¬b = ∨-introᴸ ¬a in ¬a∨¬b ↯ ¬[¬a∨¬b]
