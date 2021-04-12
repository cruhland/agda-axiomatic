import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_; As-intro)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Literals as Literals
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_; flip)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-mapᴸ; ¬_; contra; Dec; dec-map; no; yes)

module net.cruhland.axioms.Peano.Ordering.LessThan
  (PB : PeanoBase) (PS : Sign PB) (PA : PeanoAddition PB PS) where

private module ℕ+ = PeanoAddition PA
private open module ℕ = PeanoBase PB using (ℕ; step)
private open module ℕI = PeanoInspect PB using (pred; pred-intro)
private module ℕLit = Literals PB

open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual PB PS PA as ℕ≤
  using (_≤_; _≤?_; ≤-intro)

infix 4 _<_ _>_ _<⁺_ _>⁺_ _≮_ _≯_ _≮⁺_ _≯⁺_

record _<_ (n m : ℕ) : Set where
  constructor <-intro
  field
    n≤m : n ≤ m
    n≄m : n ≄ m

record _<⁺_ (n m : ℕ) : Set where
  constructor <⁺-intro
  field
    n≤m : n ≤ m
    d≄0 : _≤_.d n≤m ≄ 0

_≮_ : ℕ → ℕ → Set
n ≮ m = ¬ (n < m)

_≮⁺_ : ℕ → ℕ → Set
n ≮⁺ m = ¬ (n <⁺ m)

_>_ = flip _<_
_≯_ = flip _≮_
_>⁺_ = flip _<⁺_
_≯⁺_ = flip _≮⁺_

≤-split : ∀ {n m} → n ≤ m → n < m ∨ n ≃ m
≤-split {n} {m} n≤m with n ≃? m
... | yes n≃m = ∨-introᴿ n≃m
... | no n≄m = ∨-introᴸ (<-intro n≤m n≄m)

n<sn : ∀ {n} → n < step n
n<sn = record { n≤m = ℕ≤.n≤sn ; n≄m = ℕ+.n≄sn }

n≮0 : ∀ {n} → n ≮ 0
n≮0 (<-intro (≤-intro d n+d≃0) n≄0) =
  let ∧-intro n≃0 _ = ℕ+.+-both-zero n+d≃0
   in contra n≃0 n≄0

instance
  <-as-s≤ : ∀ {a b} → (a < b) As (step a ≤ b)
  <-as-s≤ {a} {b} = As-intro <→s≤
    where
      <→s≤ : a < b → step a ≤ b
      <→s≤ (<-intro (≤-intro d a+d≃b) a≄b) =
        let d≄0 = λ d≃0 →
              let a≃b =
                    begin
                      a
                    ≃˘⟨ AA.ident ⟩
                      a + 0
                    ≃˘⟨ AA.subst₂ d≃0 ⟩
                      a + d
                    ≃⟨ a+d≃b ⟩
                      b
                    ∎
               in contra a≃b a≄b
            pred-intro pd d≃spd = pred d≄0
            sa+pd≃b =
              begin
                step a + pd
              ≃⟨ AA.fnOpCommSwap ⟩
                a + step pd
              ≃˘⟨ AA.subst₂ d≃spd ⟩
                a + d
              ≃⟨ a+d≃b ⟩
                b
              ∎
         in record { d = pd ; n+d≃m = sa+pd≃b }

  s≤-as-< : ∀ {a b} → (step a ≤ b) As (a < b)
  s≤-as-< {a} {b} = As-intro s≤→<
    where
      s≤→< : step a ≤ b → a < b
      s≤→< sa≤b@(≤-intro d sa+d≃b) = <-intro a≤b a≄b
        where
          a≤b = Eq.trans ℕ≤.n≤sn sa≤b

          a≄b : a ≄ b
          a≄b a≃b = ℕ.step≄zero (AA.cancel a+sd≃a+z)
            where
              a+sd≃a+z =
                begin
                  a + step d
                ≃˘⟨ AA.fnOpCommSwap ⟩
                  step a + d
                ≃⟨ sa+d≃b ⟩
                  b
                ≃˘⟨ a≃b ⟩
                  a
                ≃˘⟨ AA.ident ⟩
                  a + 0
                ∎

  <-as-<⁺ : ∀ {a b} → (a < b) As (a <⁺ b)
  <-as-<⁺ {a} {b} = As-intro <→<⁺
    where
      <→<⁺ : a < b → a <⁺ b
      <→<⁺ (<-intro a≤b@(≤-intro d a+d≃b) a≄b) =
        record { n≤m = a≤b ; d≄0 = λ d≃0 → contra (AA.idᴿ→eq a+d≃b d≃0) a≄b }

  <⁺-as-< : ∀ {a b} → (a <⁺ b) As (a < b)
  <⁺-as-< {a} {b} = As-intro <⁺→<
    where
      <⁺→< : a <⁺ b → a < b
      <⁺→< (<⁺-intro a≤b@(≤-intro d a+d≃b) d≄0) =
        record { n≤m = a≤b ; n≄m = λ a≃b → contra (AA.eq→idᴿ a+d≃b a≃b) d≄0 }

  <⁺-transitive : Eq.Transitive _<⁺_
  <⁺-transitive = Eq.transitive <⁺-trans
    where
      <⁺-trans : ∀ {n m p} → n <⁺ m → m <⁺ p → n <⁺ p
      <⁺-trans (<⁺-intro n≤m d₁≄0) (<⁺-intro m≤p d₂≄0) =
        <⁺-intro (Eq.trans n≤m m≤p) (ℕ+.+-nonzero d₁≄0)

  <-transitive : Eq.Transitive _<_
  <-transitive = Eq.transitive (Cast.delegate₂ (Eq.trans {_~_ = _<⁺_}))

  <-substitutiveᴸ : ∀ {n} → AA.Substitutive₁ (_< n) _≃_ _⟨→⟩_
  <-substitutiveᴸ {n} = AA.substitutive₁ <-substᴸ
    where
      <-substᴸ : ∀ {m₁ m₂} → m₁ ≃ m₂ → m₁ < n → m₂ < n
      <-substᴸ m₁≃m₂ (<-intro m₁≤n m₁≄n) = <-intro (AA.subst₁ m₁≃m₂ m₁≤n) m₂≄n
        where
          m₂≄n = λ m₂≃n → contra (Eq.trans m₁≃m₂ m₂≃n) m₁≄n

  <-substitutiveᴿ : ∀ {n} → AA.Substitutive₁ (n <_) _≃_ _⟨→⟩_
  <-substitutiveᴿ {n} = AA.substitutive₁ <-substᴿ
    where
      <-substᴿ : ∀ {m₁ m₂} → m₁ ≃ m₂ → n < m₁ → n < m₂
      <-substᴿ m₁≃m₂ (<-intro n≤m₁ n≄m₁) = <-intro (AA.subst₁ m₁≃m₂ n≤m₁) n≄m₂
        where
          n≄m₂ = λ n≃m₂ → contra (Eq.trans n≃m₂ (Eq.sym m₁≃m₂)) n≄m₁

order-trichotomy : ∀ {n m} → AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)
order-trichotomy = record { at-least-one = 1≤ ; at-most-one = ≤1 }
  where
    1≤ : ∀ {n m} → AA.OneOfThree (n < m) (n ≃ m) (n > m)
    1≤ {n} {m} = ℕ.ind P P0 Ps n
      where
        P = λ x → AA.OneOfThree (x < m) (x ≃ m) (x > m)

        P0 : P 0
        P0 with ℕI.case m
        ... | ℕI.case-zero m≃0 = AA.2nd (Eq.sym m≃0)
        ... | ℕI.case-step (pred-intro p m≃sp) = AA.1st (<-intro ℕ≤.0≤n 0≄m)
          where 0≄m = λ 0≃m → ℕ.step≄zero (Eq.sym (Eq.trans 0≃m m≃sp))

        Ps : ℕ.step-case P
        Ps {k} (AA.1st k<m) with ≤-split (k<m as step k ≤ m)
        ... | ∨-introᴸ sk<m = AA.1st sk<m
        ... | ∨-introᴿ sk≃m = AA.2nd sk≃m
        Ps {k} (AA.2nd k≃m) =
          let sm≃sk = AA.subst₁ {f = step} (Eq.sym k≃m)
           in AA.3rd (sm≃sk as step m ≤ step k as m < step k)
        Ps (AA.3rd k>m) =
          AA.3rd (Eq.trans k>m n<sn)

    ≤1 : ∀ {n m} → ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    ≤1 (AA.1∧2 (<-intro n≤m n≄m) n≃m) =
      contra n≃m n≄m
    ≤1 (AA.1∧3 (<-intro n≤m n≄m) (<-intro m≤n m≄n)) =
      contra (AA.antisym n≤m m≤n) n≄m
    ≤1 (AA.2∧3 n≃m (<-intro m≤n m≄n)) =
      contra (Eq.sym n≃m) m≄n

≤s-split : ∀ {n m} → n ≤ step m → n ≤ m ∨ n ≃ step m
≤s-split {n} {m} n≤sm =
  ∨-mapᴸ (AA.inject ∘ (_as step n ≤ step m)) (≤-split n≤sm)

<s-split : ∀ {n m} → n < step m → n < m ∨ n ≃ m
<s-split {n} {m} = ≤-split ∘ AA.inject ∘ (_as step n ≤ step m)

strong-ind :
  (P : ℕ → Set) (b : ℕ) →
  (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
  ∀ n → b ≤ n → P n
strong-ind P b Pm n b≤n = Pm n b≤n (ℕ.ind Q Q0 Qs n)
  where
    Q = λ x → ∀ j → b ≤ j → j < x → P j
    Q0 = λ j b≤j j<0 → contra j<0 n≮0

    Q-subst : ∀ {x₁ x₂} → x₁ ≃ x₂ → Q x₁ → Q x₂
    Q-subst x₁≃x₂ Qx₁ j b≤j j<x₂ = Qx₁ j b≤j (AA.subst₁ (Eq.sym x₁≃x₂) j<x₂)

    Qs : ℕ.step-case Q
    Qs Qk j b≤j j<sk with <s-split j<sk
    ... | ∨-introᴸ j<k = Qk j b≤j j<k
    ... | ∨-introᴿ j≃k = Pm j b≤j (Q-subst (Eq.sym j≃k) Qk)

_<?_ : ∀ n m → Dec (n < m)
n <? m = dec-map (_as n < m) (_as step n ≤ m) (step n ≤? m)
