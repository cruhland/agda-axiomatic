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
      use-a≤b d a+d≡b = Σ-map-snd use-d-pred (pred d≢z)
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

          use-d-pred : ∀ {e} → d ≡ succ e → succ a + e ≡ b
          use-d-pred {e} d≡se =
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

  <→positive-diff : ∀ {a b} → a < b → Σ ℕ λ d → Positive d ∧ b ≡ a + d
  <→positive-diff {a} {b} a<b = Σ-rec use-sa≤b (<→≤ a<b)
    where
      use-sa≤b :
        (c : ℕ) → succ a + c ≡ b → Σ ℕ λ d → Positive d ∧ b ≡ a + d
      use-sa≤b c sa+c≡b = Σ-intro (succ c) (∧-intro succ≢zero b≡a+sc)
        where
          b≡a+sc = trans (sym sa+c≡b) +-succᴸ⃗ᴿ

  positive-diff→< : ∀ {a b} → Σ ℕ (λ d → Positive d ∧ b ≡ a + d) → a < b
  positive-diff→< {a} {b} Σpd = ≤→< (Σ-rec use-Σpd Σpd)
    where
      use-Σpd : (d : ℕ) → Positive d ∧ b ≡ a + d → succ a ≤ b
      use-Σpd d d≢0∧b≡a+d = Σ-rec use-pred (pred d≢0)
        where
          d≢0 = ∧-elimᴸ d≢0∧b≡a+d
          b≡a+d = ∧-elimᴿ d≢0∧b≡a+d

          use-pred : (p : ℕ) → d ≡ succ p → succ a ≤ b
          use-pred p d≡sp = Σ-intro p sa+p≡b
            where
              sa+p≡b =
                begin
                  succ a + p
                ≡⟨ +-succᴸ⃗ᴿ ⟩
                  a + succ p
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

      Ps : succProp P
      Ps z≤k = ≤-trans z≤k n≤sn

  ≤-≡ : ∀ {n m} → n ≡ m → n ≤ m
  ≤-≡ n≡m = Σ-intro zero (trans +-zeroᴿ n≡m)

  ≤→<∨≡ : ∀ {n m} → n ≤ m → n < m ∨ n ≡ m
  ≤→<∨≡ {n} {m} n≤m = ∨-rec use-≡ use-≢ (n ≡? m)
    where
      use-≡ = ∨-introᴿ
      use-≢ = λ n≢m → ∨-introᴸ (∧-intro n≤m n≢m)

  n<sn : ∀ {n} → n < succ n
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

              p≡n+[d+e] =
                begin
                  p
                ≡⟨ p≡m+e ⟩
                  m + e
                ≡⟨ cong (_+ e) m≡n+d ⟩
                  n + d + e
                ≡⟨ +-assoc ⟩
                  n + (d + e)
                ∎
              Σd+e = Σ-intro (d + e) (∧-intro p[d+e] p≡n+[d+e])

  trichotomy : ∀ {n m} → n < m ∨ n ≡ m ∨ n > m
  trichotomy {n} {m} = ind P Pz Ps n
    where
      P = λ x → x < m ∨ x ≡ m ∨ x > m
      Pz = ∨-rec use-zero use-pred (case m)
        where
          use-zero = λ m≡z → ∨-introᴿ (∨-introᴸ (sym m≡z))
          use-pred = λ Σp → ∨-introᴸ (∧-intro ≤-zero (Σ-rec use-Σp Σp))
            where
              use-Σp : ∀ p → m ≡ succ p → zero ≢ m
              use-Σp p m≡sp z≡m = succ≢zero (sym (trans z≡m m≡sp))

      Ps : succProp P
      Ps tri-k = ∨-rec use-< (∨-rec use-≡ use->) tri-k
        where
          sk<m = λ sk<m → ∨-introᴸ sk<m
          sk≡m = λ sk≡m → ∨-introᴿ (∨-introᴸ sk≡m)
          use-< = λ k<m → ∨-rec sk<m sk≡m (≤→<∨≡ (<→≤ k<m))
          use-≡ = λ k≡m → ∨-introᴿ (∨-introᴿ (≤→< (≤-≡ (cong succ (sym k≡m)))))
          use-> = λ k>m → ∨-introᴿ (∨-introᴿ (<-trans k>m n<sn))
