open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; refl; sym; trans)
open import net.cruhland.axiomatic.Logic using (⊥-elim; Decidable; no; yes)
open import net.cruhland.axiomatic.Peano.Base
  using () renaming (Peano to PeanoBase)

module net.cruhland.axiomatic.Peano.Inspect (PB : PeanoBase) where
  open PeanoBase PB using (ℕ; ind; step; step-case; step-inj; step≢zero; zero)

  _IsPred_ : ℕ → ℕ → Set
  m IsPred n = n ≡ step m

  record Pred (n : ℕ) : Set where
    constructor pred-intro
    field
      pred-value : ℕ
      pred-proof : pred-value IsPred n

  data Case (n : ℕ) : Set where
    case-zero : (n≡z : n ≡ zero) → Case n
    case-step : (n≡s : Pred n) → Case n

  case : ∀ n → Case n
  case = ind Case Cz Cs
    where
      Cz = case-zero refl

      Cs : step-case Case
      Cs {k} _ = case-step (pred-intro k refl)

  pred : ∀ {n} → n ≢ zero → Pred n
  pred {n} n≢z with case n
  ... | case-zero n≡z = ⊥-elim (n≢z n≡z)
  ... | case-step n≡s = n≡s

  _≡?_ : (n m : ℕ) → Decidable (n ≡ m)
  n ≡? m = ind P Pz Ps n m
    where
      P = λ x → ∀ y → Decidable (x ≡ y)

      Pz : P zero
      Pz y with case y
      ... | case-zero y≡z = yes z≡y
        where z≡y = sym y≡z
      ... | case-step (pred-intro p y≡sp) = no z≢y
        where z≢y = λ z≡y → step≢zero (sym (trans z≡y y≡sp))

      Ps : step-case P
      Ps {k} y→dec[k≡y] y with case y
      ... | case-zero y≡z = no sk≢y
        where sk≢y = λ sk≡y → step≢zero (trans sk≡y y≡z)
      ... | case-step (pred-intro j y≡sj) with y→dec[k≡y] j
      ...   | yes k≡j = yes sk≡sj
              where sk≡sj = trans (cong step k≡j) (sym y≡sj)
      ...   | no k≢j = no sk≢sj
              where sk≢sj = λ sk≡y → k≢j (step-inj (trans sk≡y y≡sj))
