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
