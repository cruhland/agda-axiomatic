import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; As-intro)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_; const; flip)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (⊤; ∧-intro; ¬_; contra; Dec; dec-map; no; yes)

module net.cruhland.axioms.Peano.Ordering.LessThanOrEqual
  (PB : PeanoBase) (PA : PeanoAddition PB) (PS : Sign PB PA) where

private module ℕ+ = PeanoAddition PA
private module ℕ = PeanoBase PB
private module ℕ± = Sign PS
open ℕ using (ℕ; ind; step; step-case)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕLit

infix 4 _≤_ _≥_ _≰_ _≱_

record _≤_ (n m : ℕ) : Set where
  constructor ≤-intro
  field
    d : ℕ
    n+d≃m : n + d ≃ m

_≰_ : ℕ → ℕ → Set
n ≰ m = ¬ (n ≤ m)

_≥_ = flip _≤_
_≱_ = flip _≰_

n≤sn : ∀ {n} → n ≤ step n
n≤sn = record { d = 1 ; n+d≃m = Eq.sym ℕ+.sn≃n+1 }

instance
  ≤-reflexive : Eq.Reflexive _≤_
  ≤-reflexive = Eq.reflexive record { d = 0 ; n+d≃m = AA.ident }

  ≤-transitive : Eq.Transitive _≤_
  ≤-transitive = Eq.transitive ≤-trans
    where
      ≤-trans : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
      ≤-trans (≤-intro a n+a≃m) (≤-intro b m+b≃p) =
        ≤-intro (a + b) (AA.a[bc]-chain n+a≃m m+b≃p)

  ≤-antisymmetric : AA.Antisymmetric _≤_
  ≤-antisymmetric = record { antisym = ≤-antisym }
    where
      ≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n ≃ m
      ≤-antisym {n} {m} (≤-intro a n+a≃m) (≤-intro b m+b≃n) =
        let n+a+b≃n+0 =
              begin
                n + (a + b)
              ≃⟨ AA.a[bc]-chain n+a≃m m+b≃n ⟩
                n
              ≃˘⟨ AA.ident ⟩
                n + 0
              ∎
            ∧-intro a≃0 _ = ℕ±.+-both-zero (AA.cancel n+a+b≃n+0)
         in begin
              n
            ≃˘⟨ AA.ident ⟩
              n + 0
            ≃˘⟨ AA.subst₂ a≃0 ⟩
              n + a
            ≃⟨ n+a≃m ⟩
              m
            ∎

  ≤-substitutiveᴸ : ∀ {n} → AA.Substitutive₁ (_≤ n) _≃_ _⟨→⟩_
  ≤-substitutiveᴸ {n} = AA.substitutive₁ ≤-substᴸ
    where
      ≤-substᴸ : ∀ {m₁ m₂} → m₁ ≃ m₂ → m₁ ≤ n → m₂ ≤ n
      ≤-substᴸ {m₁} {m₂} m₁≃m₂ (≤-intro d m₁+d≃n) = ≤-intro d m₂+d≃n
        where
          m₂+d≃n =
            begin
              m₂ + d
            ≃˘⟨ AA.subst₂ m₁≃m₂ ⟩
              m₁ + d
            ≃⟨ m₁+d≃n ⟩
              n
            ∎

  ≤-substitutiveᴿ : ∀ {n} → AA.Substitutive₁ (n ≤_) _≃_ _⟨→⟩_
  ≤-substitutiveᴿ {n} = AA.substitutive₁ ≤-substᴿ
    where
      ≤-substᴿ : ∀ {m₁ m₂} → m₁ ≃ m₂ → n ≤ m₁ → n ≤ m₂
      ≤-substᴿ m₁≃m₂ (≤-intro d n+d≃m₁) = ≤-intro d (Eq.trans n+d≃m₁ m₁≃m₂)

  ≤-substitutive-step : AA.Substitutive₁ step _≤_ _≤_
  ≤-substitutive-step = AA.substitutive₁ s≤s
    where
      s≤s : ∀ {n m} → n ≤ m → step n ≤ step m
      s≤s {n} {m} (≤-intro d n+d≃m) = ≤-intro d sn+d≃sm
        where
          sn+d≃sm =
            begin
              step n + d
            ≃˘⟨ AA.fnOpComm ⟩
              step (n + d)
            ≃⟨ AA.subst₁ n+d≃m ⟩
              step m
            ∎

  ≤-injective-step : AA.Injective step _≤_ _≤_
  ≤-injective-step = AA.injective s≤s→≤
    where
      s≤s→≤ : ∀ {n m} → step n ≤ step m → n ≤ m
      s≤s→≤ {n} {m} (≤-intro d sn+d≃sm) = ≤-intro d (AA.inject s[n+d]≃sm)
        where
          s[n+d]≃sm =
            begin
              step (n + d)
            ≃⟨ AA.fnOpComm ⟩
              step n + d
            ≃⟨ sn+d≃sm ⟩
              step m
            ∎

  ≤-substitutive-+ᴸ : ∀ {c} → AA.Substitutive₁ (_+ c) _≤_ _≤_
  ≤-substitutive-+ᴸ {c} = AA.substitutive₁ ≤-subst-+ᴸ
    where
      ≤-subst-+ᴸ : ∀ {a b} → a ≤ b → a + c ≤ b + c
      ≤-subst-+ᴸ {a} {b} (≤-intro d a+d≃b) = ≤-intro d a+c+d≃b+c
        where
          a+c+d≃b+c =
            begin
              a + c + d
            ≃⟨ AA.substᴿ-with-assoc AA.comm ⟩
              a + d + c
            ≃⟨ AA.subst₂ a+d≃b ⟩
              b + c
            ∎

  ≤-cancellative-+ᴿ : AA.Cancellative AA.handᴿ _+_ _≤_
  ≤-cancellative-+ᴿ = AA.cancellative λ {a b c} → ≤-cancel-+ᴿ
    where
      ≤-cancel-+ᴿ : ∀ {a b c} → a + c ≤ b + c → a ≤ b
      ≤-cancel-+ᴿ {a} {b} {c} (≤-intro d a+c+d≃b+c) = ≤-intro d a+d≃b
        where
          a+d+c≃b+c =
            begin
              a + d + c
            ≃⟨ AA.substᴿ-with-assoc AA.comm ⟩
              a + c + d
            ≃⟨ a+c+d≃b+c ⟩
              b + c
            ∎
          a+d≃b = AA.cancel a+d+c≃b+c

  ≃-as-≤ : ∀ {n m} → (n ≃ m) As (n ≤ m)
  ≃-as-≤ = As-intro λ n≃m → ≤-intro 0 (Eq.trans AA.ident n≃m)

0≤n : ∀ {n} → 0 ≤ n
0≤n {n} = ind P P0 Ps n
  where
    P = λ x → 0 ≤ x
    P0 = Eq.refl

    Ps : step-case P
    Ps 0≤k = Eq.trans 0≤k n≤sn

_≤?_ : ∀ n m → Dec (n ≤ m)
n ≤? m = ind P P0 Ps n m
  where
    P = λ x → ∀ y → Dec (x ≤ y)
    P0 = λ y → yes 0≤n

    Ps : step-case P
    Ps {k} k≤?y y with ℕI.case y
    ... | ℕI.case-zero y≃0 = no sk≰y
      where
        sk≰y : step k ≰ y
        sk≰y (≤-intro d sk+d≃y) =
          let s[k+d]≃0 =
                begin
                  step (k + d)
                ≃⟨ AA.fnOpComm ⟩
                  step k + d
                ≃⟨ sk+d≃y ⟩
                  y
                ≃⟨ y≃0 ⟩
                  0
                ∎
           in contra s[k+d]≃0 ℕ.step≄zero
    ... | ℕI.case-step (ℕI.pred-intro j y≃sj) =
      let k≤j→sk≤y = AA.subst₁ (Eq.sym y≃sj) ∘ AA.subst₁ {f = step}
          sk≤y→k≤j = AA.inject ∘ AA.subst₁ y≃sj
       in dec-map k≤j→sk≤y sk≤y→k≤j (k≤?y j)
