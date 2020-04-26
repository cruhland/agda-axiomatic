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
  n + m = rec m succ n

  +-zeroᴸ : ∀ {m} → zero + m ≡ m
  +-zeroᴸ = rec-zero

  +-succᴸ : ∀ {n m} → succ n + m ≡ succ (n + m)
  +-succᴸ = rec-succ

  +-zeroᴿ : ∀ {n} → n + zero ≡ n
  +-zeroᴿ {n} = ind P Pz Ps n
    where
      P = λ x → x + zero ≡ x
      Pz = +-zeroᴸ

      Ps : succProp P
      Ps {k} k+z≡k =
        begin
          succ k + zero
        ≡⟨ +-succᴸ ⟩
          succ (k + zero)
        ≡⟨ cong succ k+z≡k ⟩
          succ k
        ∎

  +-succᴿ : ∀ {n m} → n + succ m ≡ succ (n + m)
  +-succᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + succ m ≡ succ (x + m)

      Pz =
        begin
          zero + succ m
        ≡⟨ +-zeroᴸ ⟩
          succ m
        ≡⟨ cong succ (sym +-zeroᴸ) ⟩
          succ (zero + m)
        ∎

      Ps : succProp P
      Ps {k} k+sm≡s[k+m] =
        begin
          succ k + succ m
        ≡⟨ +-succᴸ ⟩
          succ (k + succ m)
        ≡⟨ cong succ k+sm≡s[k+m] ⟩
          succ (succ (k + m))
        ≡⟨ cong succ (sym +-succᴸ) ⟩
          succ (succ k + m)
        ∎

  +-succᴸ⃗ᴿ : ∀ {n m} → succ n + m ≡ n + succ m
  +-succᴸ⃗ᴿ = trans +-succᴸ (sym +-succᴿ)

  +-succᴿ⃗ᴸ : ∀ {n m} → n + succ m ≡ succ n + m
  +-succᴿ⃗ᴸ = sym +-succᴸ⃗ᴿ

  succ≡+ : ∀ {n} → succ n ≡ n + succ zero
  succ≡+ {n} =
    begin
      succ n
    ≡⟨ cong succ (sym +-zeroᴿ) ⟩
      succ (n + zero)
    ≡⟨ sym +-succᴿ ⟩
      n + succ zero
    ∎

  +-comm : ∀ {n m} → n + m ≡ m + n
  +-comm {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + m ≡ m + x
      Pz = trans +-zeroᴸ (sym +-zeroᴿ)

      Ps : succProp P
      Ps {k} k+m≡m+k =
        begin
          succ k + m
        ≡⟨ +-succᴸ ⟩
          succ (k + m)
        ≡⟨ cong succ k+m≡m+k ⟩
          succ (m + k)
        ≡⟨ sym +-succᴿ ⟩
          m + succ k
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

      Ps : succProp P
      Ps {k} [k+m]+p≡k+[m+p] =
        begin
          (succ k + m) + p
        ≡⟨ cong (_+ p) +-succᴸ ⟩
          succ (k + m) + p
        ≡⟨ +-succᴸ ⟩
          succ ((k + m) + p)
        ≡⟨ cong succ [k+m]+p≡k+[m+p] ⟩
          succ (k + (m + p))
        ≡⟨ sym +-succᴸ ⟩
          succ k + (m + p)
        ∎

  infixl 6 _+_

  +-perm-abc→acb : ∀ {a b c} → a + b + c ≡ a + c + b
  +-perm-abc→acb {a} {b} {c} =
    begin
      a + b + c
    ≡⟨ +-assoc ⟩
      a + (b + c)
    ≡⟨ cong (a +_) +-comm ⟩
      a + (c + b)
    ≡⟨ sym +-assoc ⟩
      a + c + b
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

      Ps : succProp P
      Ps {k} k+m≡k+p→m≡p sk+m≡sk+p = k+m≡k+p→m≡p (succ-inj s[k+m]≡s[k+p])
        where
          s[k+m]≡s[k+p] =
            begin
              succ (k + m)
            ≡⟨ sym +-succᴸ ⟩
              succ k + m
            ≡⟨ sk+m≡sk+p ⟩
              succ k + p
            ≡⟨ +-succᴸ ⟩
              succ (k + p)
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

  n≢sn : ∀ {n} → n ≢ succ n
  n≢sn {n} n≡sn = succ≢zero (+-cancelᴸ n+sz≡n+z)
    where
      n+sz≡n+z =
        begin
          n + succ zero
        ≡⟨ +-succᴿ⃗ᴸ ⟩
          succ n + zero
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

      Ps : succProp P
      Ps {k} _ = λ a+sk≡z → succ≢zero (trans (sym +-succᴿ) a+sk≡z)

  +-both-zero : ∀ {a b} → a + b ≡ zero → a ≡ zero ∧ b ≡ zero
  +-both-zero {a} {b} a+b≡z = ¬[¬a∨¬b]→a∧b (a ≡? zero) (b ≡? zero) ¬[a≢z∨b≢z]
    where
      a≢z→⊥ = λ a≢z → +-positive a≢z a+b≡z
      b≢z→⊥ = λ b≢z → +-positive b≢z (trans +-comm a+b≡z)
      ¬[a≢z∨b≢z] = ∨-rec a≢z→⊥ b≢z→⊥

  +-unchanged : ∀ {n m} → n + m ≡ n → m ≡ zero
  +-unchanged {n} {m} n+m≡n = +-cancelᴸ (trans n+m≡n (sym +-zeroᴿ))
