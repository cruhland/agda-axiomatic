open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; sym; cong; trans; subst)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using
  ( _∧_; ∧-elimᴸ; ∧-elimᴿ; ∧-intro
  ; _∨_; ∨-introᴸ; ∨-introᴿ; ∨-mapᴸ; ∨-rec
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

  _≤_ : ℕ → ℕ → Set
  n ≤ m = Σ ℕ (λ a → n + a ≡ m)

  _<_ : ℕ → ℕ → Set
  n < m = n ≤ m ∧ n ≢ m

  _≥_ : ℕ → ℕ → Set
  m ≥ n = n ≤ m

  _>_ : ℕ → ℕ → Set
  m > n = n < m

  infix 4 _≤_ _≥_ _<_ _>_

  ≤-refl : ∀ {n} → n ≤ n
  ≤-refl {n} = Σ-intro zero +-zeroᴿ

  n≤sn : ∀ {n} → n ≤ step n
  n≤sn = Σ-intro (step zero) (sym step≡+)

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
  ≤-trans {n} {m} {p} n≤m m≤p = Σ-rec use-n≤m n≤m
    where
      use-n≤m : ∀ a → n + a ≡ m → n ≤ p
      use-n≤m a n+a≡m = Σ-rec use-m≤p m≤p
        where
          use-m≤p : ∀ b → m + b ≡ p → n ≤ p
          use-m≤p b m+b≡p = Σ-intro (a + b) (a+b+c-reduce n+a≡m m+b≡p)

  ≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n ≡ m
  ≤-antisym {n} {m} n≤m m≤n = Σ-rec use-n≤m n≤m
    where
      use-n≤m : ∀ a → n + a ≡ m → n ≡ m
      use-n≤m a n+a≡m = Σ-rec use-m≤n m≤n
        where
          use-m≤n : ∀ b → m + b ≡ n → n ≡ m
          use-m≤n b m+b≡n = trans n≡n+a n+a≡m
            where
              n+a+b≡n = a+b+c-reduce n+a≡m m+b≡n
              a≡z = ∧-elimᴸ (+-both-zero (+-unchanged n+a+b≡n))
              n≡n+a = sym (trans (cong (n +_) a≡z) +-zeroᴿ)

  ≤-compat-+ᵁᴿ : ∀ {a b c} → a ≤ b → a + c ≤ b + c
  ≤-compat-+ᵁᴿ {a} {b} {c} a≤b = Σ-rec a≤b→a+c≤b+c a≤b
    where
      a≤b→a+c≤b+c : (d : ℕ) → a + d ≡ b → a + c ≤ b + c
      a≤b→a+c≤b+c d a+d≡b = Σ-intro d a+c+d≡b+c
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
  ≤-compat-+ᴰᴿ {a} {b} {c} a+c≤b+c = Σ-rec a+c≤b+c→a≤b a+c≤b+c
    where
      a+c≤b+c→a≤b : (d : ℕ) → a + c + d ≡ b + c → a ≤ b
      a+c≤b+c→a≤b d a+c+d≡b+c = Σ-intro d (+-cancelᴿ a+d+c≡b+c)
        where
          a+d+c≡b+c =
            begin
              a + d + c
            ≡⟨ with-+-assoc +-comm ⟩
              a + c + d
            ≡⟨ a+c+d≡b+c ⟩
              b + c
            ∎

  <→≤ : ∀ {a b} → a < b → step a ≤ b
  <→≤ {a} {b} a<b = Σ-rec use-a≤b a≤b
    where
      a≤b = ∧-elimᴸ a<b
      a≢b = ∧-elimᴿ a<b

      use-a≤b : (d : ℕ) → a + d ≡ b → step a ≤ b
      use-a≤b d a+d≡b with pred d≢z
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
      ... | Pred-intro e d≡se = Σ-intro e sa+e≡b
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

  ≤→< : ∀ {a b} → step a ≤ b → a < b
  ≤→< {a} {b} sa≤b = ∧-intro a≤b a≢b
    where
      a≤b = ≤-trans n≤sn sa≤b

      use-sa≤b : (d : ℕ) → step a + d ≡ b → a ≢ b
      use-sa≤b d sa+d≡b a≡b = step≢zero (+-cancelᴸ a+sd≡a+z)
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

      a≢b = Σ-rec use-sa≤b sa≤b

  <→positive-diff : ∀ {a b} → a < b → Σ ℕ λ d → Positive d ∧ b ≡ a + d
  <→positive-diff {a} {b} a<b = Σ-rec use-sa≤b (<→≤ a<b)
    where
      use-sa≤b :
        (c : ℕ) → step a + c ≡ b → Σ ℕ λ d → Positive d ∧ b ≡ a + d
      use-sa≤b c sa+c≡b = Σ-intro (step c) (∧-intro step≢zero b≡a+sc)
        where
          b≡a+sc = trans (sym sa+c≡b) +-stepᴸ⃗ᴿ

  positive-diff→< : ∀ {a b} → Σ ℕ (λ d → Positive d ∧ b ≡ a + d) → a < b
  positive-diff→< {a} {b} Σpd = ≤→< (Σ-rec use-Σpd Σpd)
    where
      use-Σpd : (d : ℕ) → Positive d ∧ b ≡ a + d → step a ≤ b
      use-Σpd d d≢0∧b≡a+d with pred (∧-elimᴸ d≢0∧b≡a+d)
      ... | Pred-intro p d≡sp = Σ-intro p sa+p≡b
        where
          b≡a+d = ∧-elimᴿ d≢0∧b≡a+d

          sa+p≡b =
            begin
              step a + p
            ≡⟨ +-stepᴸ⃗ᴿ ⟩
              a + step p
            ≡⟨ cong (a +_) (sym d≡sp) ⟩
              a + d
            ≡⟨ sym b≡a+d ⟩
              b
            ∎

  ≤-zero : ∀ {n} → zero ≤ n
  ≤-zero {n} = ind P Pz Ps n
    where
      P = λ x → zero ≤ x
      Pz = ≤-refl

      Ps : step-case P
      Ps z≤k = ≤-trans z≤k n≤sn

  ≤-≡ : ∀ {n m} → n ≡ m → n ≤ m
  ≤-≡ n≡m = Σ-intro zero (trans +-zeroᴿ n≡m)

  ≤→<∨≡ : ∀ {n m} → n ≤ m → n < m ∨ n ≡ m
  ≤→<∨≡ {n} {m} n≤m with n ≡? m
  ... | yes n≡m = ∨-introᴿ n≡m
  ... | no n≢m = ∨-introᴸ (∧-intro n≤m n≢m)

  n<sn : ∀ {n} → n < step n
  n<sn = ∧-intro n≤sn n≢sn

  <-trans : ∀ {n m p} → n < m → m < p → n < p
  <-trans {n} {m} {p} n<m m<p = Σ-rec use-Σd Σd
    where
      Σd = <→positive-diff n<m
      Σe = <→positive-diff m<p

      use-Σd : ∀ d → Positive d ∧ m ≡ n + d → n < p
      use-Σd d pd∧m≡n+d = Σ-rec use-Σe Σe
        where
          pd = ∧-elimᴸ pd∧m≡n+d
          m≡n+d = ∧-elimᴿ pd∧m≡n+d

          use-Σe : ∀ e → Positive e ∧ p ≡ m + e → n < p
          use-Σe e pe∧p≡m+e = positive-diff→< Σd+e
            where
              p≡m+e = ∧-elimᴿ pe∧p≡m+e
              p[d+e] = +-positive pd
              p≡n+[d+e] = sym (a+b+c-reduce (sym m≡n+d) (sym p≡m+e))
              Σd+e = Σ-intro (d + e) (∧-intro p[d+e] p≡n+[d+e])

  trichotomy : ∀ {n m} → n < m ∨ (n ≡ m ∨ n > m)
  trichotomy {n} {m} = ind P Pz Ps n
    where
      P = λ x → x < m ∨ (x ≡ m ∨ x > m)

      Pz : P zero
      Pz with case m
      ... | Case-zero m≡z = ∨-introᴿ (∨-introᴸ (sym m≡z))
      ... | Case-step (Pred-intro p m≡sp) = ∨-introᴸ (∧-intro ≤-zero z≢m)
        where z≢m = λ z≡m → step≢zero (sym (trans z≡m m≡sp))

      Ps : step-case P
      Ps tri-k = ∨-rec use-< (∨-rec use-≡ use->) tri-k
        where
          sk<m = λ sk<m → ∨-introᴸ sk<m
          sk≡m = λ sk≡m → ∨-introᴿ (∨-introᴸ sk≡m)
          use-< = λ k<m → ∨-rec sk<m sk≡m (≤→<∨≡ (<→≤ k<m))
          use-≡ = λ k≡m → ∨-introᴿ (∨-introᴿ (≤→< (≤-≡ (cong step (sym k≡m)))))
          use-> = λ k>m → ∨-introᴿ (∨-introᴿ (<-trans k>m n<sn))

  <-zero : ∀ {n} → ¬ (n < zero)
  <-zero {n} n<z = n≢z (Σ-rec use-n≤z n≤z)
    where
      n≤z = ∧-elimᴸ n<z
      n≢z = ∧-elimᴿ n<z

      use-n≤z : ∀ d → n + d ≡ zero → n ≡ zero
      use-n≤z d n+d≡zero = ∧-elimᴸ (+-both-zero n+d≡zero)

  s≤s→≤ : ∀ {n m} → step n ≤ step m → n ≤ m
  s≤s→≤ {n} {m} sn≤sm = Σ-map-snd use-sn≤sm sn≤sm
    where
      use-sn≤sm : ∀ {d} → step n + d ≡ step m → n + d ≡ m
      use-sn≤sm {d} sn+d≡sm = step-inj (trans (sym +-stepᴸ) sn+d≡sm)

  ≤s→≤∨≡s : ∀ {n m} → n ≤ step m → n ≤ m ∨ n ≡ step m
  ≤s→≤∨≡s n≤sm = ∨-mapᴸ (s≤s→≤ ∘ <→≤) (≤→<∨≡ n≤sm)

  <s→<∨≡ : ∀ {n m} → n < step m → n < m ∨ n ≡ m
  <s→<∨≡ = ≤→<∨≡ ∘ s≤s→≤ ∘ <→≤

  strong-ind :
    (P : ℕ → Set) (b : ℕ) →
    (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
    ∀ n → b ≤ n → P n
  strong-ind P b Pm n b≤n = Pm n b≤n (ind Q Qz Qs n)
    where
      Q = λ x → ∀ j → b ≤ j → j < x → P j
      Qz = λ j b≤j j<z → ⊥-elim (<-zero j<z)

      Qs : step-case Q
      Qs Qk j b≤j j<sk = ∨-rec use-j<k use-j≡k (<s→<∨≡ j<sk)
        where
          use-j<k = λ j<k → Qk j b≤j j<k
          use-j≡k = λ j≡k → Pm j b≤j (subst Q (sym j≡k) Qk)
