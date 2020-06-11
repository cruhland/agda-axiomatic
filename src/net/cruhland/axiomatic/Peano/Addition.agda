open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; trans; cong; subst)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Addition
  (LB : LogicBundle)
  (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Logic.Decidable LB

  _+_ : ℕ → ℕ → ℕ
  n + m = rec m step n

  +-zeroᴸ : ∀ {m} → zero + m ≡ m
  +-zeroᴸ = rec-zero

  +-stepᴸ : ∀ {n m} → step n + m ≡ step (n + m)
  +-stepᴸ = rec-step

  +-zeroᴿ : ∀ {n} → n + zero ≡ n
  +-zeroᴿ {n} = ind P Pz Ps n
    where
      P = λ x → x + zero ≡ x
      Pz = +-zeroᴸ

      Ps : step-case P
      Ps {k} k+z≡k =
        begin
          step k + zero
        ≡⟨ +-stepᴸ ⟩
          step (k + zero)
        ≡⟨ cong step k+z≡k ⟩
          step k
        ∎

  +-stepᴿ : ∀ {n m} → n + step m ≡ step (n + m)
  +-stepᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + step m ≡ step (x + m)

      Pz =
        begin
          zero + step m
        ≡⟨ +-zeroᴸ ⟩
          step m
        ≡⟨ cong step (sym +-zeroᴸ) ⟩
          step (zero + m)
        ∎

      Ps : step-case P
      Ps {k} k+sm≡s[k+m] =
        begin
          step k + step m
        ≡⟨ +-stepᴸ ⟩
          step (k + step m)
        ≡⟨ cong step k+sm≡s[k+m] ⟩
          step (step (k + m))
        ≡⟨ cong step (sym +-stepᴸ) ⟩
          step (step k + m)
        ∎

  +-stepᴸ⃗ᴿ : ∀ {n m} → step n + m ≡ n + step m
  +-stepᴸ⃗ᴿ = trans +-stepᴸ (sym +-stepᴿ)

  +-stepᴿ⃗ᴸ : ∀ {n m} → n + step m ≡ step n + m
  +-stepᴿ⃗ᴸ = sym +-stepᴸ⃗ᴿ

  step≡+ : ∀ {n} → step n ≡ n + step zero
  step≡+ {n} =
    begin
      step n
    ≡⟨ cong step (sym +-zeroᴿ) ⟩
      step (n + zero)
    ≡⟨ sym +-stepᴿ ⟩
      n + step zero
    ∎

  +-comm : ∀ {n m} → n + m ≡ m + n
  +-comm {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + m ≡ m + x
      Pz = trans +-zeroᴸ (sym +-zeroᴿ)

      Ps : step-case P
      Ps {k} k+m≡m+k =
        begin
          step k + m
        ≡⟨ +-stepᴸ ⟩
          step (k + m)
        ≡⟨ cong step k+m≡m+k ⟩
          step (m + k)
        ≡⟨ sym +-stepᴿ ⟩
          m + step k
        ∎

  +-assoc : ∀ {n m p} → (n + m) + p ≡ n + (m + p)
  +-assoc {n} {m} {p} = ind P Pz Ps n
    where
      P = λ x → (x + m) + p ≡ x + (m + p)

      Pz =
        begin
          (zero + m) + p
        ≡⟨ cong (_+ p) +-zeroᴸ ⟩
          m + p
        ≡⟨ sym +-zeroᴸ ⟩
          zero + (m + p)
        ∎

      Ps : step-case P
      Ps {k} [k+m]+p≡k+[m+p] =
        begin
          (step k + m) + p
        ≡⟨ cong (_+ p) +-stepᴸ ⟩
          step (k + m) + p
        ≡⟨ +-stepᴸ ⟩
          step ((k + m) + p)
        ≡⟨ cong step [k+m]+p≡k+[m+p] ⟩
          step (k + (m + p))
        ≡⟨ sym +-stepᴸ ⟩
          step k + (m + p)
        ∎

  infixl 6 _+_

  with-+-assoc : ∀ {a b c d e} → b + c ≡ d + e → a + b + c ≡ a + d + e
  with-+-assoc {a} {b} {c} {d} {e} b+c≡d+e =
    begin
      a + b + c
    ≡⟨ +-assoc ⟩
      a + (b + c)
    ≡⟨ cong (a +_) b+c≡d+e ⟩
      a + (d + e)
    ≡⟨ sym +-assoc ⟩
      a + d + e
    ∎

  +-cancelᴸ : ∀ {n m p} → n + m ≡ n + p → m ≡ p
  +-cancelᴸ {n} {m} {p} = ind P Pz Ps n
    where
      P = λ x → x + m ≡ x + p → m ≡ p

      Pz : P zero
      Pz z+m≡z+p =
        begin
          m
        ≡⟨ sym +-zeroᴸ ⟩
          zero + m
        ≡⟨ z+m≡z+p ⟩
          zero + p
        ≡⟨ +-zeroᴸ ⟩
          p
        ∎

      Ps : step-case P
      Ps {k} k+m≡k+p→m≡p sk+m≡sk+p = k+m≡k+p→m≡p (step-inj s[k+m]≡s[k+p])
        where
          s[k+m]≡s[k+p] =
            begin
              step (k + m)
            ≡⟨ sym +-stepᴸ ⟩
              step k + m
            ≡⟨ sk+m≡sk+p ⟩
              step k + p
            ≡⟨ +-stepᴸ ⟩
              step (k + p)
            ∎

  +-cancelᴿ : ∀ {n m p} → n + p ≡ m + p → n ≡ m
  +-cancelᴿ {n} {m} {p} n+p≡m+p = +-cancelᴸ p+n≡p+m
    where
      p+n≡p+m =
        begin
          p + n
        ≡⟨ +-comm ⟩
          n + p
        ≡⟨ n+p≡m+p ⟩
          m + p
        ≡⟨ +-comm ⟩
          p + m
        ∎

  n≢sn : ∀ {n} → n ≢ step n
  n≢sn {n} n≡sn = step≢zero (+-cancelᴸ n+sz≡n+z)
    where
      n+sz≡n+z =
        begin
          n + step zero
        ≡⟨ +-stepᴿ⃗ᴸ ⟩
          step n + zero
        ≡⟨ cong (_+ zero) (sym n≡sn) ⟩
          n + zero
        ∎

  Positive : ℕ → Set
  Positive n = n ≢ zero

  +-positive : ∀ {a b} → Positive a → Positive (a + b)
  +-positive {a} {b} pos-a = ind P Pz Ps b
    where
      P = λ x → Positive (a + x)

      Pz : P zero
      Pz = subst Positive (sym +-zeroᴿ) pos-a

      Ps : step-case P
      Ps {k} _ = λ a+sk≡z → step≢zero (trans (sym +-stepᴿ) a+sk≡z)

  +-both-zero : ∀ {a b} → a + b ≡ zero → a ≡ zero ∧ b ≡ zero
  +-both-zero {a} {b} a+b≡z = ¬[¬a∨¬b]→a∧b (a ≡? zero) (b ≡? zero) ¬[a≢z∨b≢z]
    where
      a≢z→⊥ = λ a≢z → +-positive a≢z a+b≡z
      b≢z→⊥ = λ b≢z → +-positive b≢z (trans +-comm a+b≡z)
      ¬[a≢z∨b≢z] = ∨-rec a≢z→⊥ b≢z→⊥

  +-unchanged : ∀ {n m} → n + m ≡ n → m ≡ zero
  +-unchanged {n} {m} n+m≡n = +-cancelᴸ (trans n+m≡n (sym +-zeroᴿ))
