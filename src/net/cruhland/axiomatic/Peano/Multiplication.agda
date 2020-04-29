import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; trans; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Multiplication
  (LB : LogicBundle)
  (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Peano.Addition LB PB

  _*_ : ℕ → ℕ → ℕ
  n * m = rec zero (_+ m) n

  infixl 7 _*_

  *-zeroᴸ : ∀ {m} → zero * m ≡ zero
  *-zeroᴸ = rec-zero

  *-succᴸ : ∀ {n m} → succ n * m ≡ n * m + m
  *-succᴸ = rec-succ

  *-zeroᴿ : ∀ {n} → n * zero ≡ zero
  *-zeroᴿ {n} = ind P Pz Ps n
    where
      P = λ x → x * zero ≡ zero
      Pz = *-zeroᴸ

      Ps : succProp P
      Ps {k} Pk =
        begin
          succ k * zero
        ≡⟨ *-succᴸ ⟩
          k * zero + zero
        ≡⟨ +-zeroᴿ ⟩
          k * zero
        ≡⟨ Pk ⟩
          zero
        ∎

  *-succᴿ : ∀ {n m} → n * succ m ≡ n * m + n
  *-succᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x * succ m ≡ x * m + x

      Pz =
        begin
          zero * succ m
        ≡⟨ *-zeroᴸ ⟩
          zero
        ≡⟨ sym *-zeroᴸ ⟩
          zero * m
        ≡⟨ sym +-zeroᴿ ⟩
          zero * m + zero
        ∎

      Ps : succProp P
      Ps {k} Pk =
        begin
          succ k * succ m
        ≡⟨ *-succᴸ ⟩
          k * succ m + succ m
        ≡⟨ cong (_+ succ m) Pk ⟩
          k * m + k + succ m
        ≡⟨ +-assoc ⟩
          k * m + (k + succ m)
        ≡⟨ cong (k * m +_) +-comm ⟩
          k * m + (succ m + k)
        ≡⟨ cong (k * m +_) +-succᴸ⃗ᴿ ⟩
          k * m + (m + succ k)
        ≡⟨ sym +-assoc ⟩
          k * m + m + succ k
        ≡⟨ cong (_+ succ k) (sym *-succᴸ) ⟩
          succ k * m + succ k
        ∎

  *-comm : ∀ {n m} → n * m ≡ m * n
  *-comm {n} {m} = ind P Pz Ps n
    where
      P = λ x → x * m ≡ m * x
      Pz = trans *-zeroᴸ (sym *-zeroᴿ)

      Ps : succProp P
      Ps {k} Pk =
        begin
          succ k * m
        ≡⟨ *-succᴸ ⟩
          k * m + m
        ≡⟨ cong (_+ m) Pk ⟩
          m * k + m
        ≡⟨ sym *-succᴿ ⟩
          m * succ k
        ∎
