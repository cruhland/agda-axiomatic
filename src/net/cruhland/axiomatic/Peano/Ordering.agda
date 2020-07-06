open import Function using (_∘_; flip)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; sym; cong; trans; subst)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using
  ( _∧_; ∧-elimᴸ; ∧-intro
  ; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-mapᴸ
  ; ⊥; ⊥-elim; ¬_
  ; Σ; Σ-intro; Σ-map-snd; Σ-rec
  ; no; yes
  )
open import net.cruhland.axiomatic.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axiomatic.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axiomatic.Peano.Inspect as PeanoInspect

module net.cruhland.axiomatic.Peano.Ordering
    (PB : PeanoBase) (PA : PeanoAddition PB) where
  open PeanoAddition PA using
    ( _+_; n≢sn; +-stepᴸ; +-stepᴸ⃗ᴿ; +-stepᴿ⃗ᴸ; step≡+; +-zeroᴿ
    ; +-assoc; +-cancelᴸ; +-cancelᴿ; +-comm; with-+-assoc
    ; Positive; +-both-zero; +-positive; +-unchanged
    )
  open PeanoBase PB using (ℕ; ind; step; step-case; step-inj; step≢zero; zero)
  open PeanoInspect PB using
    (_≡?_; Case; case; Case-step; Case-zero; Pred-intro; pred)

  infix 4 _≤_ _<_ _≰_ _≮_ _≥_ _>_ _≱_ _≯_

  record _≤_ (n m : ℕ) : Set where
    constructor ≤-intro
    field
      d : ℕ
      n+d≡m : n + d ≡ m

  record _<_ (n m : ℕ) : Set where
    constructor <-intro
    field
      <→≤ : n ≤ m
      <→≢ : n ≢ m

  open _<_ public using (<→≤; <→≢)

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
  n≤sn = ≤-intro (step zero) (sym step≡+)

  a+b+c-reduce : ∀ {a b c d e} → a + b ≡ d → d + c ≡ e → a + (b + c) ≡ e
  a+b+c-reduce {a} {b} {c} {d} {e} a+b≡d d+c≡e =
    begin
      a + (b + c)
    ≡⟨ sym +-assoc ⟩
      (a + b) + c
    ≡⟨ cong (_+ c) a+b≡d ⟩
      d + c
    ≡⟨ d+c≡e ⟩
      e
    ∎

  ≤-trans : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
  ≤-trans (≤-intro a n+a≡m) (≤-intro b m+b≡p) =
    ≤-intro (a + b) (a+b+c-reduce n+a≡m m+b≡p)

  ≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n ≡ m
  ≤-antisym {n} {m} (≤-intro a n+a≡m) (≤-intro b m+b≡n) = n≡m
    where
      n+a+b≡n = a+b+c-reduce n+a≡m m+b≡n
      a≡z = ∧-elimᴸ (+-both-zero (+-unchanged n+a+b≡n))
      n≡m =
        begin
          n
        ≡⟨ sym +-zeroᴿ ⟩
          n + zero
        ≡⟨ cong (n +_) (sym a≡z) ⟩
          n + a
        ≡⟨ n+a≡m ⟩
          m
        ∎

  ≤-compat-+ᵁᴿ : ∀ {a b c} → a ≤ b → a + c ≤ b + c
  ≤-compat-+ᵁᴿ {a} {b} {c} (≤-intro d a+d≡b) = ≤-intro d a+c+d≡b+c
    where
      a+c+d≡b+c =
        begin
          a + c + d
        ≡⟨ with-+-assoc +-comm ⟩
          a + d + c
        ≡⟨ cong (_+ c) a+d≡b ⟩
          b + c
        ∎

  ≤-compat-+ᴰᴿ : ∀ {a b c} → a + c ≤ b + c → a ≤ b
  ≤-compat-+ᴰᴿ {a} {b} {c} (≤-intro d a+c+d≡b+c) = ≤-intro d a+d≡b
    where
      a+d+c≡b+c =
        begin
          a + d + c
        ≡⟨ with-+-assoc +-comm ⟩
          a + c + d
        ≡⟨ a+c+d≡b+c ⟩
          b + c
        ∎
      a+d≡b = +-cancelᴿ a+d+c≡b+c

  <→s≤ : ∀ {a b} → a < b → step a ≤ b
  <→s≤ {a} {b} (<-intro (≤-intro d a+d≡b) a≢b) with pred d≢z
    where
      d≢z : d ≢ zero
      d≢z d≡z = a≢b a≡b
        where
          a≡b =
            begin
              a
            ≡⟨ sym +-zeroᴿ ⟩
              a + zero
            ≡⟨ cong (a +_) (sym d≡z) ⟩
              a + d
            ≡⟨ a+d≡b ⟩
              b
            ∎
  ... | Pred-intro e d≡se = ≤-intro e sa+e≡b
    where
      sa+e≡b =
        begin
          step a + e
        ≡⟨ +-stepᴸ⃗ᴿ ⟩
          a + step e
        ≡⟨ cong (a +_) (sym d≡se) ⟩
          a + d
        ≡⟨ a+d≡b ⟩
          b
        ∎

  s≤→< : ∀ {a b} → step a ≤ b → a < b
  s≤→< {a} {b} sa≤b@(≤-intro d sa+d≡b) = <-intro a≤b a≢b
    where
      a≤b = ≤-trans n≤sn sa≤b

      a≢b : a ≢ b
      a≢b a≡b = step≢zero (+-cancelᴸ a+sd≡a+z)
        where
          a+sd≡a+z =
            begin
              a + step d
            ≡⟨ +-stepᴿ⃗ᴸ ⟩
              step a + d
            ≡⟨ sa+d≡b ⟩
              b
            ≡⟨ sym a≡b ⟩
              a
            ≡⟨ sym +-zeroᴿ ⟩
              a + zero
            ∎

  record _<⁺_ (n m : ℕ) : Set where
    constructor <⁺-intro
    field
      d : ℕ
      d≢z : Positive d
      n+d≡m : n + d ≡ m

  <→<⁺ : ∀ {a b} → a < b → a <⁺ b
  <→<⁺ a<b with <→s≤ a<b
  ... | ≤-intro c sa+c≡b = <⁺-intro (step c) step≢zero (trans +-stepᴿ⃗ᴸ sa+c≡b)

  <⁺→< : ∀ {a b} → a <⁺ b → a < b
  <⁺→< {a} {b} (<⁺-intro d d≢z a+d≡b) with pred d≢z
  ... | Pred-intro p d≡sp = s≤→< (≤-intro p sa+p≡b)
    where
      sa+p≡b =
        begin
          step a + p
        ≡⟨ +-stepᴸ⃗ᴿ ⟩
          a + step p
        ≡⟨ cong (a +_) (sym d≡sp) ⟩
          a + d
        ≡⟨ a+d≡b ⟩
          b
        ∎

  ≤-zero : ∀ {n} → zero ≤ n
  ≤-zero {n} = ind P Pz Ps n
    where
      P = λ x → zero ≤ x
      Pz = ≤-refl

      Ps : step-case P
      Ps z≤k = ≤-trans z≤k n≤sn

  ≡→≤ : ∀ {n m} → n ≡ m → n ≤ m
  ≡→≤ n≡m = ≤-intro zero (trans +-zeroᴿ n≡m)

  ≤→<∨≡ : ∀ {n m} → n ≤ m → n < m ∨ n ≡ m
  ≤→<∨≡ {n} {m} n≤m with n ≡? m
  ... | yes n≡m = ∨-introᴿ n≡m
  ... | no n≢m = ∨-introᴸ (<-intro n≤m n≢m)

  n<sn : ∀ {n} → n < step n
  n<sn = <-intro n≤sn n≢sn

  <-trans : ∀ {n m p} → n < m → m < p → n < p
  <-trans n<m m<p with <→<⁺ n<m | <→<⁺ m<p
  ... | <⁺-intro d d≢z n+d≡m | <⁺-intro e e≢z m+e≡p = <⁺→< n<⁺p
    where
      n<⁺p = <⁺-intro (d + e) (+-positive d≢z) (a+b+c-reduce n+d≡m m+e≡p)

  data Trichotomy (n m : ℕ) : Set where
    tri-< : n < m → Trichotomy n m
    tri-≡ : n ≡ m → Trichotomy n m
    tri-> : n > m → Trichotomy n m

  trichotomy : ∀ {n m} → Trichotomy n m
  trichotomy {n} {m} = ind P Pz Ps n
    where
      P = λ x → Trichotomy x m

      Pz : P zero
      Pz with case m
      ... | Case-zero m≡z = tri-≡ (sym m≡z)
      ... | Case-step (Pred-intro p m≡sp) = tri-< (<-intro ≤-zero z≢m)
        where z≢m = λ z≡m → step≢zero (sym (trans z≡m m≡sp))

      Ps : step-case P
      Ps (tri-< k<m) with ≤→<∨≡ (<→s≤ k<m)
      ... | ∨-introᴸ sk<m = tri-< sk<m
      ... | ∨-introᴿ sk≡m = tri-≡ sk≡m
      Ps (tri-≡ k≡m) = tri-> (s≤→< (≡→≤ (cong step (sym k≡m))))
      Ps (tri-> k>m) = tri-> (<-trans k>m n<sn)

  <-zero : ∀ {n} → n ≮ zero
  <-zero (<-intro (≤-intro d n+d≡z) n≢z) = n≢z (∧-elimᴸ (+-both-zero n+d≡z))

  s≤s→≤ : ∀ {n m} → step n ≤ step m → n ≤ m
  s≤s→≤ (≤-intro d sn+d≡sm) =
    ≤-intro d (step-inj (trans (sym +-stepᴸ) sn+d≡sm))

  ≤s→≤∨≡s : ∀ {n m} → n ≤ step m → n ≤ m ∨ n ≡ step m
  ≤s→≤∨≡s n≤sm = ∨-mapᴸ (s≤s→≤ ∘ <→s≤) (≤→<∨≡ n≤sm)

  <s→<∨≡ : ∀ {n m} → n < step m → n < m ∨ n ≡ m
  <s→<∨≡ = ≤→<∨≡ ∘ s≤s→≤ ∘ <→s≤

  strong-ind :
    (P : ℕ → Set) (b : ℕ) →
    (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
    ∀ n → b ≤ n → P n
  strong-ind P b Pm n b≤n = Pm n b≤n (ind Q Qz Qs n)
    where
      Q = λ x → ∀ j → b ≤ j → j < x → P j
      Qz = λ j b≤j j<z → ⊥-elim (<-zero j<z)

      Qs : step-case Q
      Qs Qk j b≤j j<sk with <s→<∨≡ j<sk
      ... | ∨-introᴸ j<k = Qk j b≤j j<k
      ... | ∨-introᴿ j≡k = Pm j b≤j (subst Q (sym j≡k) Qk)
