import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq; DecEq-intro)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄ⁱ_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤; Dec; dec-map)

module net.cruhland.models.Rationals.IntPair.BaseImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open Integers Z using (ℤ)

infix 8 _//_
record ℚ : Set where
  constructor _//_
  field
    numerator denominator : ℤ
    {{denominator≄ⁱ0}} : denominator ≄ⁱ 0

record _≃₀_ (p q : ℚ) : Set where
  constructor ≃₀-intro

  open ℚ p using () renaming (numerator to p↑; denominator to p↓)
  open ℚ q using () renaming (numerator to q↑; denominator to q↓)

  field
    elim : p↑ * q↓ ≃ q↑ * p↓

instance
  ≃₀-reflexive : Eq.Reflexive _≃₀_
  ≃₀-reflexive = Eq.reflexive ≃₀-refl
    where
      ≃₀-refl : ∀ {q} → q ≃₀ q
      ≃₀-refl q@{q↑ // q↓} =
        let q↑q↓≃q↑q↓ = Eq.refl
         in ≃₀-intro q↑q↓≃q↑q↓

  ≃₀-symmetric : Eq.Symmetric _≃₀_
  ≃₀-symmetric = Eq.symmetric ≃₀-sym
    where
      ≃₀-sym : ∀ {p q} → p ≃₀ q → q ≃₀ p
      ≃₀-sym p@{p↑ // p↓} q@{q↑ // q↓} (≃₀-intro p↑q↓≃q↑p↓) =
        let q↑p↓≃p↑q↓ = Eq.sym p↑q↓≃q↑p↓
         in ≃₀-intro q↑p↓≃p↑q↓

  ≃₀-transitive : Eq.Transitive _≃₀_
  ≃₀-transitive = Eq.transitive ≃₀-trans
    where
      ≃₀-trans : ∀ {p q r} → p ≃₀ q → q ≃₀ r → p ≃₀ r
      ≃₀-trans
          p@{p↑ // p↓} q@{q↑ // q↓} r@{r↑ // r↓}
          (≃₀-intro p↑q↓≃q↑p↓) (≃₀-intro q↑r↓≃r↑q↓) =
        let [p↑r↓]q↓≃[r↑p↓]q↓ =
              begin
                (p↑ * r↓) * q↓
              ≃⟨ AA.assoc ⟩
                p↑ * (r↓ * q↓)
              ≃⟨ AA.subst₂ AA.comm ⟩
                p↑ * (q↓ * r↓)
              ≃˘⟨ AA.assoc ⟩
                (p↑ * q↓) * r↓
              ≃⟨ AA.subst₂ p↑q↓≃q↑p↓ ⟩
                (q↑ * p↓) * r↓
              ≃⟨ AA.subst₂ AA.comm ⟩
                (p↓ * q↑) * r↓
              ≃⟨ AA.assoc ⟩
                p↓ * (q↑ * r↓)
              ≃⟨ AA.subst₂ q↑r↓≃r↑q↓ ⟩
                p↓ * (r↑ * q↓)
              ≃˘⟨ AA.assoc ⟩
                (p↓ * r↑) * q↓
              ≃⟨ AA.subst₂ AA.comm  ⟩
                (r↑ * p↓) * q↓
              ∎
            p↑r↓≃r↑p↓ = AA.cancel [p↑r↓]q↓≃[r↑p↓]q↓
         in ≃₀-intro p↑r↓≃r↑p↓

  eq : Eq ℚ
  eq = Eq.equivalence _≃₀_

  decEq : DecEq ℚ
  decEq = DecEq-intro _≃?₀_
    where
      _≃?₀_ : (p q : ℚ) {{_ : ⊤}} → Dec (p ≃ q)
      (p↑ // p↓) ≃?₀ (q↑ // q↓) =
        dec-map ≃₀-intro _≃₀_.elim (p↑ * q↓ ≃? q↑ * p↓)

  from-ℤ : ℤ As ℚ
  from-ℤ = Cast.As-intro (_// 1)

  from-ℕ : ℕ As ℚ
  from-ℕ = Cast.via ℤ

  from-Nat : Nat As ℚ
  from-Nat = Cast.via ℕ

  from-literal : FromNatLiteral ℚ
  from-literal = nat-literal-from-cast

  //-substitutiveᴸ : AA.Substitutive₂ᶜ AA.handᴸ _//_ _≃_ _≃_
  //-substitutiveᴸ = AA.substitutive₂ //-substᴸ
    where
      //-substᴸ :
        {a₁ a₂ b : ℤ} {{c₁ : b ≄ⁱ 0}} {{c₂ : b ≄ⁱ 0}} →
        a₁ ≃ a₂ → (a₁ // b) {{c₁}} ≃ (a₂ // b) {{c₂}}
      //-substᴸ {a₁} {a₂} {b} a₁≃a₂ =
        let componentEq =
              begin
                a₁ * b
              ≃⟨ AA.subst₂ a₁≃a₂ ⟩
                a₂ * b
              ∎
         in ≃₀-intro componentEq

  //-substitutiveᴿ : AA.Substitutive₂ᶜ AA.handᴿ _//_ _≃_ _≃_
  //-substitutiveᴿ = AA.substitutive₂ //-substᴿ
    where
      //-substᴿ :
        {a₁ a₂ b : ℤ} {{_ : a₁ ≄ⁱ 0}} {{_ : a₂ ≄ⁱ 0}} →
        a₁ ≃ a₂ → b // a₁ ≃ b // a₂
      //-substᴿ {a₁} {a₂} {b} a₁≃a₂ =
        let componentEq =
              begin
                b * a₂
              ≃˘⟨ AA.subst₂ a₁≃a₂ ⟩
                b * a₁
              ∎
         in ≃₀-intro componentEq

  //-substitutive : AA.Substitutive²ᶜ _//_ _≃_ _≃_
  //-substitutive = AA.substitutive²
