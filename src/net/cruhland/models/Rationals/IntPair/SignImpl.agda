import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_)

module net.cruhland.models.Rationals.IntPair.SignImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

private module ℤ = Integers Z
private module ℚ where
  open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
  open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
  open import net.cruhland.models.Rationals.IntPair.ReciprocalImpl PA Z public

open ℤ using (ℤ)
open ℚ using (ℚ; _//_)

record Positive₀ (q : ℚ) : Set where
  constructor Positive₀-intro
  field
    {a b} : ℤ
    pos[a] : S.Positive a
    pos[b] : S.Positive b
    q≃a/b :
      let b≄0 = S.pos≄0 pos[b]
          instance b:ℚ≄0:ℚ = AA.subst₁ b≄0
       in q ≃ (a as ℚ) / (b as ℚ)

q≄0-from-pos[q] : {q : ℚ} → Positive₀ q → q ≄ 0
q≄0-from-pos[q] {q} (Positive₀-intro {a} {b} pos[a] pos[b] q≃a/b) =
  Eq.≄-intro λ q≃0 →
    let instance
          b≄0 = S.pos≄0 pos[b]
          b:ℚ≄0:ℚ = AA.subst₁ b≄0
        a//b≃0 =
          begin
            a // b
          ≃˘⟨ ℚ.a:ℚ/b:ℚ≃a//b ⟩
            (a as ℚ) / (b as ℚ)
          ≃˘⟨ q≃a/b ⟩
            q
          ≃⟨ q≃0 ⟩
            0
          ∎
        a≃0 = ℚ.q↑≃0-from-q≃0 a//b≃0
        a≄0 = S.pos≄0 pos[a]
     in a≃0 ↯ a≄0

instance
  Positive₀-substitutive : AA.Substitutive₁ Positive₀ _≃_ _⟨→⟩_
  Positive₀-substitutive = AA.substitutive₁ pos-subst
    where
      pos-subst : {p q : ℚ} → p ≃ q → Positive₀ p → Positive₀ q
      pos-subst p≃q (Positive₀-intro pos[a] pos[b] p≃a/b) =
        Positive₀-intro pos[a] pos[b] (Eq.trans (Eq.sym p≃q) p≃a/b)

  positivity : S.Positivity 0
  positivity = record { Positive = Positive₀ ; pos≄0 = q≄0-from-pos[q] }
