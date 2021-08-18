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

import net.cruhland.axioms.Rationals.DivisionDecl PA Z as DivisionDecl
open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.MultiplicationDefn PA Z
  using (QM)
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)
open import net.cruhland.models.Rationals.IntPair.ReciprocalDefn PA Z using (QR)

private module ℤ = Integers Z
private module ℚ where
  open DivisionDecl.DivisionPredefs QB QA QN QM QR public
  open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
  open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
  open import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z
    public
  open import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z public

open ℤ using (ℤ)
open ℚ using (ℚ; _//_)

-- Get definitions from partial impls
import net.cruhland.axioms.Rationals.DivisionPartialImplBaseQ
  as DivisionPartialImplBaseQ
open DivisionPartialImplBaseQ PA Z QB QA QN QM QR public

div-ℚ-subst-proof :
  {p q : ℚ} {{q≄0₁ q≄0₂ : q ≄ 0}} → (p / q) {{q≄0₁}} ≃ (p / q) {{q≄0₂}}
div-ℚ-subst-proof = ℚ.≃₀-intro Eq.refl

private
  open import net.cruhland.axioms.Rationals.DivisionPartialImplPropertiesQ PA Z
    using (DivisionPropertiesQ)

  divisionPropertiesQ : DivisionPropertiesQ QB QA QN QM QR
  divisionPropertiesQ = record
    { div-ℚ-defn = div-ℚ-defn
    ; div-ℚ-subst-proof = div-ℚ-subst-proof
    ; q/q≃1 = q/q≃1
    ; *-div-ℚ = *-div-ℚ
    }

open DivisionPropertiesQ divisionPropertiesQ public
  hiding (div-ℚ; div-ℚ-defn; div-ℚ-subst-proof; *-div-ℚ; q/q≃1)

private
  open import net.cruhland.axioms.Rationals.DivisionPartialImplDerivedQ PA Z
    using (DivisionDerivedQ)

  divisionDerivedQ : DivisionDerivedQ QB QA QN QM QR
  divisionDerivedQ = record
    { div-ℚ-subst-proof = div-ℚ-subst-proof
    ; q/q≃1 = q/q≃1
    ; *-div-ℚ = *-div-ℚ
    }

open DivisionDerivedQ divisionDerivedQ public
  hiding ( div-ℚ; div-ℚ-distributive-+ᴿ; div-ℚ-subst-proof; div-ℚ-substitutive
         ; *-div-ℚ; q/q≃1)

private
  open import net.cruhland.axioms.Rationals.DivisionPartialImplBaseZ PA Z
    using (DivisionBaseZ)

  divisionBaseZ : DivisionBaseZ QB QA QN QM
  divisionBaseZ =
    record { +-div-ℚ = +-div-ℚ ; *-div-ℚ = *-div-ℚ ; q/q≃1 = q/q≃1  }

open DivisionBaseZ divisionBaseZ public
  hiding (div-ℚ; div-ℚ-substitutive; +-div-ℚ; *-div-ℚ; q/q≃1)

div-ℤ-subst-proof :
  {a b : ℤ} {{b≄0₁ b≄0₂ : b ≄ 0}} → (a / b) {{b≄0₁}} ≃ (a / b) {{b≄0₂}}
div-ℤ-subst-proof = ℚ.≃₀-intro Eq.refl

private
  open import net.cruhland.axioms.Rationals.DivisionPartialImplPropertiesZ PA Z
    using (DivisionPropertiesZ)

  divisionPropertiesZ : DivisionPropertiesZ QB QA QN QM
  divisionPropertiesZ = record { div-ℤ-defn = div-ℤ-defn }

open DivisionPropertiesZ divisionPropertiesZ public
  hiding ( div-ℚ; div-ℚ-absorptiveᴸ; div-ℚ-cancellative-*; div-ℚ-comm-with-neg
         ; div-ℚ-substitutive; div-ℤ; div-ℤ-defn)

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

fraction : (q : ℚ) → ℚ.Fraction q
fraction (q↑ // q↓) = ℚ.fraction-intro (Eq.sym a/b≃a//b)
