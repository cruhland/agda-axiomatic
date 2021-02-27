import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contra)

module net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.Base
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where
private open module ℕ = PeanoBase PB using (ℕ; step)
private module ℕ+ = Addition PA
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕLit

infix 4 _+d≃_
record _+d≃_ (n m : ℕ) : Set where
  constructor +d≃-intro
  field
    {d} : ℕ
    n+d≃m : n + d ≃ m

record LteBase : Set₁ where
  field
    {{lessThanOrEqual}} : LessThanOrEqual ℕ
    {{substitutive-≃}} : AA.Substitutive₂² _≤_ _≃_ _⟨→⟩_
    {{reflexive}} : Eq.Reflexive _≤_

    ≤-intro-+d≃ : ∀ {n m} → n +d≃ m → n ≤ m
    ≤-elim-+d≃ : ∀ {n m} → n ≤ m → n +d≃ m

    {{substitutive-step}} : AA.Substitutive₁ step _≤_ _≤_
    0≤n : ∀ {n : ℕ} → 0 ≤ n
    ≤-step : ∀ {n m} → n ≤ m → n ≤ step m

open LteBase {{...}} public using (≤-intro-+d≃; ≤-elim-+d≃; 0≤n; ≤-step)

private
  instance
    lessThanOrEqual-+d≃ : LessThanOrEqual ℕ
    lessThanOrEqual-+d≃ = record { _≤_ = _+d≃_ }

    substitutive-+d≃-≃ᴸ : AA.Substitutive₂ AA.handᴸ _+d≃_ _≃_ _⟨→⟩_
    substitutive-+d≃-≃ᴸ = AA.substitutive₂ +d≃-substᴸ
      where
        +d≃-substᴸ : ∀ {n₁ n₂ m} → n₁ ≃ n₂ → n₁ +d≃ m → n₂ +d≃ m
        +d≃-substᴸ n₁≃n₂ (+d≃-intro n₁+d≃m) =
          +d≃-intro (Eq.trans (AA.subst₂ (Eq.sym n₁≃n₂)) n₁+d≃m)

    substitutive-+d≃-≃ᴿ : AA.Substitutive₂ AA.handᴿ _+d≃_ _≃_ _⟨→⟩_
    substitutive-+d≃-≃ᴿ = AA.substitutive₂ +d≃-substᴿ
      where
        +d≃-substᴿ : ∀ {n₁ n₂ m} → n₁ ≃ n₂ → m +d≃ n₁ → m +d≃ n₂
        +d≃-substᴿ n₁≃n₂ (+d≃-intro {d} m+d≃n₁) =
          +d≃-intro (Eq.trans m+d≃n₁ n₁≃n₂)

    substitutive-+d≃-≃ : AA.Substitutive₂² _+d≃_ _≃_ _⟨→⟩_
    substitutive-+d≃-≃ = AA.substitutive₂²

    reflexive-+d≃ : Eq.Reflexive _+d≃_
    reflexive-+d≃ = Eq.reflexive (+d≃-intro AA.ident)

    substitutive-+d≃-step : AA.Substitutive₁ step _+d≃_ _+d≃_
    substitutive-+d≃-step = AA.substitutive₁ +d≃-subst-step
      where
        +d≃-subst-step : ∀ {n m} → n +d≃ m → step n +d≃ step m
        +d≃-subst-step {n} {m} (+d≃-intro {d} n+d≃m) =
          let sn+d≃sm =
                begin
                  step n + d
                ≃˘⟨ AA.fnOpComm ⟩
                  step (n + d)
                ≃⟨ AA.subst₁ n+d≃m ⟩
                  step m
                ∎
           in +d≃-intro sn+d≃sm

0+d≃n : ∀ {n} → 0 +d≃ n
0+d≃n = +d≃-intro AA.ident

+d≃-step : ∀ {n m} → n +d≃ m → n +d≃ step m
+d≃-step {n} {m} (+d≃-intro {d} n+d≃m) = +d≃-intro n+sd≃sm
  where
    n+sd≃sm =
      begin
        n + step d
      ≃˘⟨ AA.fnOpComm ⟩
        step (n + d)
      ≃⟨ AA.subst₁ n+d≃m ⟩
        step m
      ∎

≤-base-+d≃ : LteBase
≤-base-+d≃ = record
  { ≤-intro-+d≃ = id
  ; ≤-elim-+d≃ = id
  ; 0≤n = 0+d≃n
  ; ≤-step = +d≃-step
  }
