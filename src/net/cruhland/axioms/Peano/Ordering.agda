open import Function using (_∘_; flip)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
open import net.cruhland.models.Logic using
  ( _∧_; ∧-elimᴸ; ∧-intro
  ; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-mapᴸ
  ; ⊥; ⊥-elim; ¬_
  ; Dec; dec-map; no; yes
  )

module net.cruhland.axioms.Peano.Ordering
    (PB : PeanoBase) (PA : PeanoAddition PB) where
  private module Add = PeanoAddition PA
  open Add using
    ( _+_; n≄sn; +-stepᴸ; +-stepᴸ⃗ᴿ; +-stepᴿ⃗ᴸ
    ; step≃+; +-zeroᴿ; +-assoc; +-cancelᴸ; +-cancelᴿ; with-+-assoc
    ; Positive; +-both-zero; +-positive; +-unchanged
    )
  open PeanoBase PB using (ℕ; ind; step; step-case; step-inj; step≄zero; zero)
  open PeanoInspect PB using
    (Case; case; case-step; case-zero; decEq; pred-intro; pred)

  infix 4 _≤_ _<_ _≰_ _≮_ _≥_ _>_ _≱_ _≯_

  record _≤_ (n m : ℕ) : Set where
    constructor ≤-intro
    field
      d : ℕ
      n+d≃m : n + d ≃ m

  record _<_ (n m : ℕ) : Set where
    constructor <-intro
    field
      <→≤ : n ≤ m
      <→≄ : n ≄ m

  open _<_ public using (<→≤; <→≄)

  _≰_ : ℕ → ℕ → Set
  n ≰ m = ¬ (n ≤ m)

  _≮_ : ℕ → ℕ → Set
  n ≮ m = ¬ (n < m)

  _≥_ = flip _≤_
  _>_ = flip _<_
  _≱_ = flip _≰_
  _≯_ = flip _≮_

  ≤-refl : ∀ {n} → n ≤ n
  ≤-refl = ≤-intro zero +-zeroᴿ

  n≤sn : ∀ {n} → n ≤ step n
  n≤sn = ≤-intro (step zero) (sym step≃+)

  a+b+c-reduce : ∀ {a b c d e} → a + b ≃ d → d + c ≃ e → a + (b + c) ≃ e
  a+b+c-reduce {a} {b} {c} {d} {e} a+b≃d d+c≃e =
    begin
      a + (b + c)
    ≃⟨ sym +-assoc ⟩
      (a + b) + c
    ≃⟨ AA.substᴸ a+b≃d ⟩
      d + c
    ≃⟨ d+c≃e ⟩
      e
    ∎

  ≤-trans : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
  ≤-trans (≤-intro a n+a≃m) (≤-intro b m+b≃p) =
    ≤-intro (a + b) (a+b+c-reduce n+a≃m m+b≃p)

  ≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n ≃ m
  ≤-antisym {n} {m} (≤-intro a n+a≃m) (≤-intro b m+b≃n) = n≃m
    where
      n+a+b≃n = a+b+c-reduce n+a≃m m+b≃n
      a≃z = ∧-elimᴸ (+-both-zero (+-unchanged n+a+b≃n))
      n≃m =
        begin
          n
        ≃˘⟨ +-zeroᴿ ⟩
          n + zero
        ≃˘⟨ AA.substᴿ a≃z ⟩
          n + a
        ≃⟨ n+a≃m ⟩
          m
        ∎

  ≤-compat-+ᵁᴿ : ∀ {a b c} → a ≤ b → a + c ≤ b + c
  ≤-compat-+ᵁᴿ {a} {b} {c} (≤-intro d a+d≃b) = ≤-intro d a+c+d≃b+c
    where
      a+c+d≃b+c =
        begin
          a + c + d
        ≃⟨ with-+-assoc AA.comm ⟩
          a + d + c
        ≃⟨ AA.substᴸ a+d≃b ⟩
          b + c
        ∎

  ≤-compat-+ᴰᴿ : ∀ {a b c} → a + c ≤ b + c → a ≤ b
  ≤-compat-+ᴰᴿ {a} {b} {c} (≤-intro d a+c+d≃b+c) = ≤-intro d a+d≃b
    where
      a+d+c≃b+c =
        begin
          a + d + c
        ≃⟨ with-+-assoc AA.comm ⟩
          a + c + d
        ≃⟨ a+c+d≃b+c ⟩
          b + c
        ∎
      a+d≃b = +-cancelᴿ a+d+c≃b+c

  <→s≤ : ∀ {a b} → a < b → step a ≤ b
  <→s≤ {a} {b} (<-intro (≤-intro d a+d≃b) a≄b) with pred d≄z
    where
      d≄z : d ≄ zero
      d≄z d≃z = a≄b a≃b
        where
          a≃b =
            begin
              a
            ≃˘⟨ +-zeroᴿ ⟩
              a + zero
            ≃˘⟨ AA.substᴿ d≃z ⟩
              a + d
            ≃⟨ a+d≃b ⟩
              b
            ∎
  ... | pred-intro e d≃se = ≤-intro e sa+e≃b
    where
      sa+e≃b =
        begin
          step a + e
        ≃⟨ +-stepᴸ⃗ᴿ ⟩
          a + step e
        ≃˘⟨ AA.substᴿ d≃se ⟩
          a + d
        ≃⟨ a+d≃b ⟩
          b
        ∎

  s≤→< : ∀ {a b} → step a ≤ b → a < b
  s≤→< {a} {b} sa≤b@(≤-intro d sa+d≃b) = <-intro a≤b a≄b
    where
      a≤b = ≤-trans n≤sn sa≤b

      a≄b : a ≄ b
      a≄b a≃b = step≄zero (+-cancelᴸ a+sd≃a+z)
        where
          a+sd≃a+z =
            begin
              a + step d
            ≃⟨ +-stepᴿ⃗ᴸ ⟩
              step a + d
            ≃⟨ sa+d≃b ⟩
              b
            ≃⟨ sym a≃b ⟩
              a
            ≃⟨ sym +-zeroᴿ ⟩
              a + zero
            ∎

  record _<⁺_ (n m : ℕ) : Set where
    constructor <⁺-intro
    field
      d : ℕ
      d≄z : Positive d
      n+d≃m : n + d ≃ m

  <→<⁺ : ∀ {a b} → a < b → a <⁺ b
  <→<⁺ a<b with <→s≤ a<b
  ... | ≤-intro c sa+c≃b = <⁺-intro (step c) step≄zero (trans +-stepᴿ⃗ᴸ sa+c≃b)

  <⁺→< : ∀ {a b} → a <⁺ b → a < b
  <⁺→< {a} {b} (<⁺-intro d d≄z a+d≃b) with pred d≄z
  ... | pred-intro p d≃sp = s≤→< (≤-intro p sa+p≃b)
    where
      sa+p≃b =
        begin
          step a + p
        ≃⟨ +-stepᴸ⃗ᴿ ⟩
          a + step p
        ≃˘⟨ AA.substᴿ d≃sp ⟩
          a + d
        ≃⟨ a+d≃b ⟩
          b
        ∎

  ≤-zero : ∀ {n} → zero ≤ n
  ≤-zero {n} = ind P Pz Ps n
    where
      P = λ x → zero ≤ x
      Pz = ≤-refl

      Ps : step-case P
      Ps z≤k = ≤-trans z≤k n≤sn

  ≤-step : ∀ {n m} → n ≤ m → step n ≤ step m
  ≤-step (≤-intro d n+d≃m) = ≤-intro d (trans +-stepᴸ (AA.subst n+d≃m))

  ≃→≤ : ∀ {n m} → n ≃ m → n ≤ m
  ≃→≤ n≃m = ≤-intro zero (trans +-zeroᴿ n≃m)

  ≤→<∨≃ : ∀ {n m} → n ≤ m → n < m ∨ n ≃ m
  ≤→<∨≃ {n} {m} n≤m with n ≃? m
  ... | yes n≃m = ∨-introᴿ n≃m
  ... | no n≄m = ∨-introᴸ (<-intro n≤m n≄m)

  n<sn : ∀ {n} → n < step n
  n<sn = <-intro n≤sn n≄sn

  <-trans : ∀ {n m p} → n < m → m < p → n < p
  <-trans n<m m<p with <→<⁺ n<m | <→<⁺ m<p
  ... | <⁺-intro d d≄z n+d≃m | <⁺-intro e e≄z m+e≃p = <⁺→< n<⁺p
    where
      n<⁺p = <⁺-intro (d + e) (+-positive d≄z) (a+b+c-reduce n+d≃m m+e≃p)

  data Trichotomy (n m : ℕ) : Set where
    tri-< : n < m → Trichotomy n m
    tri-≃ : n ≃ m → Trichotomy n m
    tri-> : n > m → Trichotomy n m

  trichotomy : ∀ {n m} → Trichotomy n m
  trichotomy {n} {m} = ind P Pz Ps n
    where
      P = λ x → Trichotomy x m

      Pz : P zero
      Pz with case m
      ... | case-zero m≃z = tri-≃ (sym m≃z)
      ... | case-step (pred-intro p m≃sp) = tri-< (<-intro ≤-zero z≄m)
        where z≄m = λ z≃m → step≄zero (sym (trans z≃m m≃sp))

      Ps : step-case P
      Ps (tri-< k<m) with ≤→<∨≃ (<→s≤ k<m)
      ... | ∨-introᴸ sk<m = tri-< sk<m
      ... | ∨-introᴿ sk≃m = tri-≃ sk≃m
      Ps (tri-≃ k≃m) = tri-> (s≤→< (≃→≤ (AA.subst (sym k≃m))))
      Ps (tri-> k>m) = tri-> (<-trans k>m n<sn)

  <-zero : ∀ {n} → n ≮ zero
  <-zero (<-intro (≤-intro d n+d≃z) n≄z) = n≄z (∧-elimᴸ (+-both-zero n+d≃z))

  s≤s→≤ : ∀ {n m} → step n ≤ step m → n ≤ m
  s≤s→≤ (≤-intro d sn+d≃sm) =
    ≤-intro d (step-inj (trans (sym +-stepᴸ) sn+d≃sm))

  ≤s→≤∨≃s : ∀ {n m} → n ≤ step m → n ≤ m ∨ n ≃ step m
  ≤s→≤∨≃s n≤sm = ∨-mapᴸ (s≤s→≤ ∘ <→s≤) (≤→<∨≃ n≤sm)

  <s→<∨≃ : ∀ {n m} → n < step m → n < m ∨ n ≃ m
  <s→<∨≃ = ≤→<∨≃ ∘ s≤s→≤ ∘ <→s≤

  ≤-substᴿ : ∀ {n m₁ m₂} → m₁ ≃ m₂ → n ≤ m₁ → n ≤ m₂
  ≤-substᴿ m₁≃m₂ (≤-intro d n+d≃m₁) = ≤-intro d (trans n+d≃m₁ m₁≃m₂)

  <-substᴿ : ∀ {n m₁ m₂} → m₁ ≃ m₂ → n < m₁ → n < m₂
  <-substᴿ m₁≃m₂ (<-intro n≤m₁ n≄m₁) =
    <-intro (≤-substᴿ m₁≃m₂ n≤m₁) λ n≃m₂ → n≄m₁ (trans n≃m₂ (sym m₁≃m₂))

  strong-ind :
    (P : ℕ → Set) (b : ℕ) →
    (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
    ∀ n → b ≤ n → P n
  strong-ind P b Pm n b≤n = Pm n b≤n (ind Q Qz Qs n)
    where
      Q = λ x → ∀ j → b ≤ j → j < x → P j
      Qz = λ j b≤j j<z → ⊥-elim (<-zero j<z)

      Q-subst : ∀ {x₁ x₂} → x₁ ≃ x₂ → Q x₁ → Q x₂
      Q-subst x₁≃x₂ Qx₁ j b≤j j<x₂ = Qx₁ j b≤j (<-substᴿ (sym x₁≃x₂) j<x₂)

      Qs : step-case Q
      Qs Qk j b≤j j<sk with <s→<∨≃ j<sk
      ... | ∨-introᴸ j<k = Qk j b≤j j<k
      ... | ∨-introᴿ j≃k = Pm j b≤j (Q-subst (sym j≃k) Qk)

  _≤?_ : ∀ n m → Dec (n ≤ m)
  n ≤? m = ind P Pz Ps n m
    where
      P = λ x → ∀ y → Dec (x ≤ y)

      Pz : P zero
      Pz y = yes ≤-zero

      Ps : step-case P
      Ps {k} k≤?y y with case y
      ... | case-zero y≃z =
        no λ { (≤-intro d sk+d≃y) →
                 step≄zero (trans (sym +-stepᴸ) (trans sk+d≃y y≃z)) }
      ... | case-step (pred-intro j y≃sj) =
         dec-map (≤-substᴿ (sym y≃sj) ∘ ≤-step) (s≤s→≤ ∘ ≤-substᴿ y≃sj) (k≤?y j)

  _<?_ : ∀ n m → Dec (n < m)
  n <? m = dec-map s≤→< <→s≤ (step n ≤? m)
