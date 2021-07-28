import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (DecEq; DecEq-intro)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Sign using (Positivity)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤; _↯_; Dec; no; yes)

module net.cruhland.axioms.Peano.Inspect (PB : PeanoBase) where

private module ℕ where
  open PeanoBase PB public
  open import net.cruhland.axioms.Peano.Literals PB public

open ℕ using (ℕ; step)

non-zero-positivity : Positivity 0
non-zero-positivity = record { Positive = Pos ; pos≄0 = id }
  where
    Pos = _≄ 0

    Pos-subst : ∀ {n₁ n₂} → n₁ ≃ n₂ → Pos n₁ → Pos n₂
    Pos-subst n₁≃n₂ n₁≄0 = AA.substᴸ n₁≃n₂ n₁≄0

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
case = ℕ.ind Case C0 Cs
  where
    C0 = case-zero Eq.refl

    Cs : ℕ.step-case Case
    Cs {k} _ = case-step (pred-intro k Eq.refl)

pred : ∀ {n} → n ≄ 0 → Pred n
pred {n} n≄0 with case n
... | case-zero n≃0 = n≃0 ↯ n≄0
... | case-step n≃s = n≃s

instance
  decEq : DecEq ℕ
  decEq = DecEq-intro _≃?_
    where
      _≃?_ : (n m : ℕ) {{_ : ⊤}} → Dec (n ≃ m)
      n ≃? m = ℕ.ind P P0 Ps n m
        where
          P = λ x → ∀ y → Dec (x ≃ y)

          P0 : P 0
          P0 y with case y
          P0 y | case-zero y≃0 =
            let 0≃y = Eq.sym y≃0
             in yes 0≃y
          P0 y | case-step (pred-intro p y≃sp) =
            let 0≄sp = Eq.sym ℕ.step≄zero
                0≄y = AA.substᴿ (Eq.sym y≃sp) 0≄sp
             in no 0≄y

          Ps : ℕ.step-case P
          Ps {k} y→dec[k≃y] y with case y
          Ps {k} y→dec[k≃y] y | case-zero y≃0 =
            let sk≄0 = ℕ.step≄zero
                sk≄y = AA.substᴿ (Eq.sym y≃0) sk≄0
             in no sk≄y
          Ps {k} y→dec[k≃y] y | case-step (pred-intro j y≃sj)
            with y→dec[k≃y] j
          Ps {k} y→dec[k≃y] y | case-step (pred-intro j y≃sj) | yes k≃j =
            let sk≃sj = AA.subst₁ k≃j
                sk≃y = Eq.trans sk≃sj (Eq.sym y≃sj)
             in yes sk≃y
          Ps {k} y→dec[k≃y] y | case-step (pred-intro j y≃sj) | no k≄j =
            let sk≄sj = AA.subst₁ k≄j
                sk≄y = AA.substᴿ (Eq.sym y≃sj) sk≄sj
             in no sk≄y
