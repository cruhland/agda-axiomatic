import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong; trans)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Ordering
  (LB : LogicBundle)
  (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Peano.Addition LB PB

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

  n≤sn : ∀ {n} → n ≤ succ n
  n≤sn = Σ-intro (succ zero) (sym succ≡+)

  ≤-trans : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
  ≤-trans {n} {m} {p} n≤m m≤p = Σ-rec use-n≤m n≤m
    where
      use-n≤m : ∀ a → n + a ≡ m → n ≤ p
      use-n≤m a n+a≡m = Σ-rec use-m≤p m≤p
        where
          use-m≤p : ∀ b → m + b ≡ p → n ≤ p
          use-m≤p b m+b≡p = Σ-intro (a + b) n+a+b≡p
            where
              n+a+b≡p =
                begin
                  n + (a + b)
                ≡⟨ sym +-assoc ⟩
                  (n + a) + b
                ≡⟨ cong (_+ b) n+a≡m ⟩
                  m + b
                ≡⟨ m+b≡p ⟩
                  p
                ∎

  ≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n ≡ m
  ≤-antisym {n} {m} n≤m m≤n = Σ-rec use-n≤m n≤m
    where
      use-n≤m : ∀ a → n + a ≡ m → n ≡ m
      use-n≤m a n+a≡m = Σ-rec use-m≤n m≤n
        where
          use-m≤n : ∀ b → m + b ≡ n → n ≡ m
          use-m≤n b m+b≡n = trans n≡n+a n+a≡m
            where
              n+a+b≡n =
                begin
                  n + (a + b)
                ≡⟨ sym +-assoc ⟩
                  (n + a) + b
                ≡⟨ cong (_+ b) n+a≡m ⟩
                  m + b
                ≡⟨ m+b≡n ⟩
                  n
                ∎

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
            ≡⟨ +-perm-abc→acb ⟩
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
            ≡⟨ +-perm-abc→acb ⟩
              a + c + d
            ≡⟨ a+c+d≡b+c ⟩
              b + c
            ∎

  <→≤ : ∀ {a b} → a < b → succ a ≤ b
  <→≤ {a} {b} a<b = Σ-rec use-a≤b a≤b
    where
      a≤b = ∧-elimᴸ a<b
      a≢b = ∧-elimᴿ a<b

      use-a≤b : (d : ℕ) → a + d ≡ b → succ a ≤ b
      use-a≤b d a+d≡b = Σ-map-snd use-d≡succ d≡succ
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

          d≡succ = ∨-forceᴿ d≢z (case d)

          use-d≡succ : ∀ {e} → d ≡ succ e → succ a + e ≡ b
          use-d≡succ {e} d≡se =
            begin
              succ a + e
            ≡⟨ +-succᴸ⃗ᴿ ⟩
              a + succ e
            ≡⟨ cong (a +_) (sym d≡se) ⟩
              a + d
            ≡⟨ a+d≡b ⟩
              b
            ∎

  ≤→< : ∀ {a b} → succ a ≤ b → a < b
  ≤→< {a} {b} sa≤b = ∧-intro a≤b a≢b
    where
      a≤b = ≤-trans n≤sn sa≤b

      use-sa≤b : (d : ℕ) → succ a + d ≡ b → a ≢ b
      use-sa≤b d sa+d≡b a≡b = succ≢zero (+-cancelᴸ a+sd≡a+z)
        where
          a+sd≡a+z =
            begin
              a + succ d
            ≡⟨ +-succᴿ⃗ᴸ ⟩
              succ a + d
            ≡⟨ sa+d≡b ⟩
              b
            ≡⟨ sym a≡b ⟩
              a
            ≡⟨ sym +-zeroᴿ ⟩
              a + zero
            ∎

      a≢b = Σ-rec use-sa≤b sa≤b
