import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.IntPair.DivisionImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.MultiplicationDefn PA Z
  using (QM)
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)
open import net.cruhland.models.Rationals.IntPair.ReciprocalDefn PA Z using (QR)

private module ℤ = Integers Z
private module ℚ where
  open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
  open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
  open import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z
    public
  open import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z public

open ℤ using (ℤ)
open ℚ using (ℚ; _//_)

-- Get definitions from partial impls
import net.cruhland.axioms.Rationals.DivisionPartialImplBase
  as DivisionPartialImplBase
open DivisionPartialImplBase PA Z QB QA QN QM QR public

private
  open import net.cruhland.axioms.Rationals.DivisionPartialImplProperties PA Z
    using (DivisionProperties)

  divisionProperties : DivisionProperties QB QA QN QM QR
  divisionProperties = record { div-ℚ-defn = div-ℚ-defn }

open DivisionProperties divisionProperties public hiding (div-ℚ; div-ℚ-defn)

a/b≃a//b : {a b : ℤ} {{b≄0 : b ≄ 0}} → a / b ≃ a // b
a/b≃a//b {a} {b} {{b≄0}} =
  let instance
        b:ℚ≄0:ℚ = AA.subst₁ b≄0
        1*b≄0 = AA.nonzero-prod {{a≄0 = ℤ.1≄0}} {{b≄0}}
   in begin
        a / b
      ≃⟨⟩
        (a as ℚ) / (b as ℚ)
      ≃⟨⟩
        (a // 1) / (b // 1)
      ≃⟨⟩
        (a // 1) * (b // 1) ⁻¹
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        (a // 1) * (1 // b)
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        (a * 1) // (1 * b)
      ≃⟨ AA.subst₂ AA.ident ⟩
        a // (1 * b)
      ≃⟨ AA.subst₂ AA.ident ⟩
        a // b
      ∎

a≃0-from-a/b≃0 : {a b : ℤ} {{_ : b ≄ 0}} → a / b ≃ 0 → a ≃ 0
a≃0-from-a/b≃0 {a} {b} a/b≃0 =
  let a//b≃0 =
        begin
          a // b
        ≃˘⟨ a/b≃a//b ⟩
          a / b
        ≃⟨ a/b≃0 ⟩
          0
        ∎
   in ℚ.q↑≃0-from-q≃0 a//b≃0
