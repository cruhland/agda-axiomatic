import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Ordering as Ord using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl using (LtBase)
open import net.cruhland.axioms.Peano.Ordering.LessThan.PropertiesDecl
  using (LtProperties)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  using (LteBase)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∨_; ∨-comm; ∨-introᴸ; ∨-introᴿ; ∨-mapᴸ; ∨-mapᴿ
  ; ¬_; ¬-intro; _↯_; contrapositive; Dec; dec-map)

module net.cruhland.axioms.Peano.Ordering.PropertiesImpl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTEP : LteProperties PB PS PA LTEB)
  (LTB : LtBase PB PS PA LTEB)
  (LTP : LtProperties PB PS PA LTEB LTB)
  where

private
  module ℕ where
    open Addition PA public
    open LtBase LTB public
    open LteBase LTEB public
    open LteProperties LTEP public
    open LtProperties LTP public
    open PeanoBase PB public
    open import net.cruhland.axioms.Peano.Inspect PB public
    open import net.cruhland.axioms.Peano.Literals PB public

open ℕ using (_≤?_; ℕ; step)

≤-dec-≃ : {n m : ℕ} → n ≤ m → n ≃ m ∨ n ≄ m
≤-dec-≃ {n} {m} n≤m with ℕ.case (ℕ.≤-diff n≤m)
... | ℕ.case-zero d≃0 = ∨-introᴸ (ℕ.zero-diff n≤m d≃0)
... | ℕ.case-step (ℕ.pred-intro d′ d≃sd′) = ∨-introᴿ n≄m
  where
    n≄m = Eq.≄-intro λ n≃m →
      let n+d≃n+0 =
            begin
              n + ℕ.≤-diff n≤m
            ≃⟨ ℕ.≤-elim-diff n≤m ⟩
              m
            ≃˘⟨ n≃m ⟩
              n
            ≃˘⟨ AA.ident ⟩
              n + 0
            ∎
          d≃0 = AA.cancel n+d≃n+0
          sd′≃0 = Eq.trans (Eq.sym d≃sd′) d≃0
       in sd′≃0 ↯ ℕ.step≄zero

≤-split : {n m : ℕ} → n ≤ m → n < m ∨ n ≃ m
≤-split n≤m = ∨-comm (∨-mapᴿ (ℕ.<-intro-≤≄ n≤m) (≤-dec-≃ n≤m))

s≤-from-< : {n m : ℕ} → n < m → step n ≤ m
s≤-from-< {n} {m} n<m =
  let n≤m = ℕ.<-elim-≤ n<m
      n≄m = ℕ.<-elim-≄ n<m
      d≄0 = contrapositive (ℕ.zero-diff n≤m) n≄m
      ℕ.pred-intro pd d≃spd = ℕ.pred d≄0
      sn+pd≃m =
        begin
          step n + pd
        ≃⟨ AA.fnOpCommSwap ⟩
          n + step pd
        ≃˘⟨ AA.subst₂ d≃spd ⟩
          n + ℕ.≤-diff n≤m
        ≃⟨ ℕ.≤-elim-diff n≤m ⟩
          m
        ∎
   in ℕ.≤-intro-diff sn+pd≃m

<-from-s≤ : {n m : ℕ} → step n ≤ m → n < m
<-from-s≤ {n} {m} sn≤m =
  let n≤m = Eq.trans ℕ.n≤sn sn≤m
      n≄m = Eq.≄-intro λ n≃m →
        let n+sd≃n+0 =
              begin
                n + step (ℕ.≤-diff sn≤m)
              ≃˘⟨ AA.fnOpCommSwap ⟩
                step n + ℕ.≤-diff sn≤m
              ≃⟨ ℕ.≤-elim-diff sn≤m ⟩
                m
              ≃˘⟨ n≃m ⟩
                n
              ≃˘⟨ AA.ident ⟩
                n + 0
              ∎
            sd≃0 = AA.cancel n+sd≃n+0
         in sd≃0 ↯ ℕ.step≄zero
   in ℕ.<-intro-≤≄ n≤m n≄m

order-trichotomy : (n m : ℕ) → AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)
order-trichotomy n m = AA.exactlyOneOfThree 1of3 ¬2of3
  where
    1of3 : AA.OneOfThree (n < m) (n ≃ m) (n > m)
    1of3 = ℕ.ind P P0 Ps n
      where
        P = λ x → AA.OneOfThree (x < m) (x ≃ m) (x > m)

        P0 : P 0
        P0 with ℕ.case m
        ... | ℕ.case-zero m≃0 =
          AA.2nd (Eq.sym m≃0)
        ... | ℕ.case-step (ℕ.pred-intro p m≃sp) =
          let 0≄sp = Eq.sym ℕ.step≄zero
              0≄m = AA.substᴿ (Eq.sym m≃sp) 0≄sp
           in AA.1st (ℕ.<-intro-≤≄ ℕ.≤-zeroᴸ 0≄m)

        Ps : ℕ.step-case P
        Ps {k} (AA.1st k<m) with ≤-split (s≤-from-< k<m)
        ... | ∨-introᴸ sk<m = AA.1st sk<m
        ... | ∨-introᴿ sk≃m = AA.2nd sk≃m
        Ps {k} (AA.2nd k≃m) =
          let sm≃sk = AA.subst₁ (Eq.sym k≃m)
              sm≤sk = ℕ.≤-intro-≃ sm≃sk
              m<sk = <-from-s≤ sm≤sk
              sk>m = Ord.<-flip m<sk
           in AA.3rd sk>m
        Ps (AA.3rd k>m) =
          let sk>k = Ord.<-flip ℕ.n<sn
              sk>m = Eq.trans sk>k k>m
           in AA.3rd sk>m

    ¬2of3 : ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    ¬2of3 = ¬-intro λ
      { (AA.1∧2 n<m n≃m) →
          let n≄m = ℕ.<-elim-≄ n<m
           in n≃m ↯ n≄m
      ; (AA.1∧3 n<m n>m) →
          ℕ.<-asymmetric n<m (Ord.>-flip n>m)
      ; (AA.2∧3 n≃m n>m) →
          let m≃n = Eq.sym n≃m
              m<n = Ord.>-flip n>m
              m≄n = ℕ.<-elim-≄ m<n
           in m≃n ↯ m≄n
      }

≤s-split : ∀ {n m} → n ≤ step m → n ≤ m ∨ n ≃ step m
≤s-split {n} {m} n≤sm = ∨-mapᴸ (AA.inject ∘ s≤-from-<) (≤-split n≤sm)

<s-split : ∀ {n m} → n < step m → n < m ∨ n ≃ m
<s-split {n} {m} = ≤-split ∘ AA.inject ∘ s≤-from-<

_<?_ : ∀ n m → Dec (n < m)
n <? m = dec-map <-from-s≤ s≤-from-< (step n ≤? m)

strong-ind :
  (P : ℕ → Set) (b : ℕ) →
  (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) → ∀ n → b ≤ n → P n
strong-ind P b Pm n b≤n = Pm n b≤n (ℕ.ind Q Q0 Qs n)
  where
    Q = λ x → ∀ j → b ≤ j → j < x → P j
    Q0 = λ j b≤j j<0 → j<0 ↯ ℕ.n≮0

    Q-subst : ∀ {x₁ x₂} → x₁ ≃ x₂ → Q x₁ → Q x₂
    Q-subst x₁≃x₂ Qx₁ j b≤j j<x₂ = Qx₁ j b≤j (AA.subst₂ (Eq.sym x₁≃x₂) j<x₂)

    Qs : ℕ.step-case Q
    Qs Qk j b≤j j<sk with <s-split j<sk
    ... | ∨-introᴸ j<k = Qk j b≤j j<k
    ... | ∨-introᴿ j≃k = Pm j b≤j (Q-subst (Eq.sym j≃k) Qk)
