import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Ordering using (_<_; _≮_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl using
  (LteBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.PropertiesImplBase
  as LteProps
open import net.cruhland.axioms.Peano.Sign using (Sign)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (∧-intro; ⊥; _↯_; ¬-intro)

module net.cruhland.axioms.Peano.Ordering.LessThan.PropertiesImplBase
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTB : LtBase PB PS PA LTEB) where

module ℕ+ = Addition PA
open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL
module ℕ< = LtBase LTB
module ℕ≤ = LteBase LTEB
module ℕ≤P = LteProps PB PS PA LTEB

instance
  <-transitive : Eq.Transitive _<_
  <-transitive = Eq.transitive <-trans
    where
      <-trans : {n m k : ℕ} → n < m → m < k → n < k
      <-trans n<m m<k =
        let n≤m = ℕ<.<-elim-≤ n<m
            m≤k = ℕ<.<-elim-≤ m<k
            n≤k = Eq.trans n≤m m≤k
            pos[d[n<m]] = ℕ<.<-diff-pos n<m
            pos[d[n≤m]] = AA.subst₁ (ℕ<.<-diff-from-≤-diff n<m) pos[d[n<m]]
            pos[d[n≤m]+d[m≤k]] = ℕ+.+-positive pos[d[n≤m]]
            d[n≤m]+d[m≤k]≃d[n≤k] = Eq.sym (ℕ≤P.diff-trans n≤m m≤k)
            pos[d[n≤k]] = AA.subst₁ d[n≤m]+d[m≤k]≃d[n≤k] pos[d[n≤m]+d[m≤k]]
         in ℕ<.<-intro-≤pd n≤k pos[d[n≤k]]

  <-substitutive-≃ᴸ : AA.Substitutive₂ AA.handᴸ _<_ _≃_ _⟨→⟩_
  <-substitutive-≃ᴸ = AA.substitutive₂ <-substᴸ
    where
      <-substᴸ : {n₁ n₂ m : ℕ} → n₁ ≃ n₂ → n₁ < m → n₂ < m
      <-substᴸ n₁≃n₂ n₁<m =
        let n₁≤m = ℕ<.<-elim-≤ n₁<m
            n₂≤m = AA.subst₂ n₁≃n₂ n₁≤m
            n₁≄m = ℕ<.<-elim-≄ n₁<m
            n₂≄m = AA.substᴸ n₁≃n₂ n₁≄m
         in ℕ<.<-intro-≤≄ n₂≤m n₂≄m

  <-substitutive-≃ᴿ : AA.Substitutive₂ AA.handᴿ _<_ _≃_ _⟨→⟩_
  <-substitutive-≃ᴿ = AA.substitutive₂ <-substᴿ
    where
      <-substᴿ : {n₁ n₂ m : ℕ} → n₁ ≃ n₂ → m < n₁ → m < n₂
      <-substᴿ n₁≃n₂ m<n₁ =
        let m≤n₁ = ℕ<.<-elim-≤ m<n₁
            m≤n₂ = AA.subst₂ n₁≃n₂ m≤n₁
            m≄n₁ = ℕ<.<-elim-≄ m<n₁
            m≄n₂ = AA.substᴿ n₁≃n₂ m≄n₁
         in ℕ<.<-intro-≤≄ m≤n₂ m≄n₂

  <-substitutive-≃ : AA.Substitutive² _<_ _≃_ _⟨→⟩_
  <-substitutive-≃ = AA.substitutive²

  <-substitutive-+ᴸ : AA.Substitutive₂ AA.handᴸ _+_ _<_ _<_
  <-substitutive-+ᴸ = AA.substitutive₂ <-substᴸ
    where
      <-substᴸ : {a₁ a₂ b : ℕ} → a₁ < a₂ → a₁ + b < a₂ + b
      <-substᴸ a₁<a₂ =
        let a₁≤a₂ = ℕ<.<-elim-≤ a₁<a₂
            a₁≄a₂ = ℕ<.<-elim-≄ a₁<a₂
            a₁+b≤a₂+b = AA.subst₂ a₁≤a₂
            a₁+b≄a₂+b = AA.subst₂ a₁≄a₂
         in ℕ<.<-intro-≤≄ a₁+b≤a₂+b a₁+b≄a₂+b

  <-substitutive-+ᴿ : AA.Substitutive₂ AA.handᴿ _+_ _<_ _<_
  <-substitutive-+ᴿ = AA.substᴿ-from-substᴸ-comm₂

  <-substitutive-+ : AA.Substitutive² _+_ _<_ _<_
  <-substitutive-+ = AA.substitutive²

<-compatible-+ : {n₁ n₂ m₁ m₂ : ℕ} → n₁ < n₂ → m₁ < m₂ → n₁ + m₁ < n₂ + m₂
<-compatible-+ n₁<n₂ m₁<m₂ =
  let n₁+m₁<n₂+m₁ = AA.subst₂ n₁<n₂
      n₂+m₁<n₂+m₂ = AA.subst₂ m₁<m₂
   in Eq.trans n₁+m₁<n₂+m₁ n₂+m₁<n₂+m₂

n<sn : {n : ℕ} → n < step n
n<sn = ℕ<.<-intro-≤≄ ℕ≤P.n≤sn ℕ+.n≄sn

n≮0 : {n : ℕ} → n ≮ 0
n≮0 = ¬-intro λ n<0 →
  let n≤0 = ℕ<.<-elim-≤ n<0
      n≄0 = ℕ<.<-elim-≄ n<0
      n+d≃0 = ℕ≤.≤-elim-diff n≤0
      ∧-intro n≃0 _ = ℕ+.+-both-zero n+d≃0
   in n≃0 ↯ n≄0

<-from-pos : {n : ℕ} → S.Positive n → 0 < n
<-from-pos pos[n] = ℕ<.<-intro-≤≄ ℕ≤.≤-zeroᴸ (Eq.sym (S.pos≄0 pos[n]))

<-asymmetric : {n m : ℕ} → n < m → m < n → ⊥
<-asymmetric n<m m<n =
  let n≤m = ℕ<.<-elim-≤ n<m
      m≤n = ℕ<.<-elim-≤ m<n
      n≄m = ℕ<.<-elim-≄ n<m
      n≃m = AA.antisym n≤m m≤n
   in n≃m ↯ n≄m
