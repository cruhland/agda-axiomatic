import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_; refl; sym; trans)
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Sign using (Positivity)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤; contra; Dec; no; yes)

module net.cruhland.axioms.Peano.Inspect (PB : PeanoBase) where
  open PeanoBase PB using (ℕ; ind; step; step-case; step≄zero)
  import net.cruhland.axioms.Peano.Literals PB as ℕLit

  non-zero-positivity : Positivity 0
  non-zero-positivity = record { Positive = Pos ; pos≄0 = id }
    where
      Pos = _≄ 0

      Pos-subst : ∀ {n₁ n₂} → n₁ ≃ n₂ → Pos n₁ → Pos n₂
      Pos-subst n₁≃n₂ n₁≄0 n₂≃0 = contra (trans n₁≃n₂ n₂≃0) n₁≄0

      instance
        Pos-substitutive : AA.Substitutive₁ Pos _≃_ _⟨→⟩_
        Pos-substitutive = AA.substitutive₁ Pos-subst

  _IsPred_ : ℕ → ℕ → Set
  m IsPred n = n ≃ step m

  record Pred (n : ℕ) : Set where
    constructor pred-intro
    field
      pred-value : ℕ
      pred-proof : pred-value IsPred n

  data Case (n : ℕ) : Set where
    case-zero : (n≃0 : n ≃ 0) → Case n
    case-step : (n≃s : Pred n) → Case n

  case : ∀ n → Case n
  case = ind Case C0 Cs
    where
      C0 = case-zero refl

      Cs : step-case Case
      Cs {k} _ = case-step (pred-intro k refl)

  pred : ∀ {n} → n ≄ 0 → Pred n
  pred {n} n≄0 with case n
  ... | case-zero n≃0 = contra n≃0 n≄0
  ... | case-step n≃s = n≃s

  instance
    decEq : DecEq ℕ
    decEq = record { Constraint = λ _ _ → ⊤ ; _≃?_ = _≃?_ }
      where
        _≃?_ : (n m : ℕ) {{_ : ⊤}} → Dec (n ≃ m)
        n ≃? m = ind P P0 Ps n m
          where
            P = λ x → ∀ y → Dec (x ≃ y)

            P0 : P 0
            P0 y with case y
            ... | case-zero y≃0 = yes 0≃y
              where 0≃y = sym y≃0
            ... | case-step (pred-intro p y≃sp) = no 0≄y
              where 0≄y = λ 0≃y → step≄zero (sym (trans 0≃y y≃sp))

            Ps : step-case P
            Ps {k} y→dec[k≃y] y with case y
            ... | case-zero y≃0 = no sk≄y
              where sk≄y = λ sk≃y → step≄zero (trans sk≃y y≃0)
            ... | case-step (pred-intro j y≃sj) with y→dec[k≃y] j
            ...   | yes k≃j = yes sk≃sj
                    where sk≃sj = trans (AA.subst₁ k≃j) (sym y≃sj)
            ...   | no k≄j = no sk≄sj
                    where sk≄sj = λ sk≃y → k≄j (AA.inject (trans sk≃y y≃sj))
