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
        ≡⟨ with-+-assoc (trans +-comm +-succᴸ⃗ᴿ) ⟩
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

  *-either-zero : ∀{n m} → n * m ≡ zero → n ≡ zero ∨ m ≡ zero
  *-either-zero {n} {m} n*m≡z = ∨-mapᴿ (Σ-rec use-pred) (case n)
    where
      use-pred : ∀ p → n ≡ succ p → m ≡ zero
      use-pred p n≡sp = ∧-elimᴿ (+-both-zero p*m+m≡z)
        where
          p*m+m≡z =
            begin
              p * m + m
            ≡⟨ sym *-succᴸ ⟩
              succ p * m
            ≡⟨ cong (_* m) (sym n≡sp) ⟩
              n * m
            ≡⟨ n*m≡z ⟩
              zero
            ∎

  *-distrib-+ᴸ : ∀ {a b c} → a * (b + c) ≡ a * b + a * c
  *-distrib-+ᴸ {a} {b} {c} = ind P Pz Ps c
    where
      P = λ x → a * (b + x) ≡ a * b + a * x
      Pz =
        begin
          a * (b + zero)
        ≡⟨ cong (a *_) +-zeroᴿ ⟩
          a * b
        ≡⟨ sym +-zeroᴿ ⟩
          a * b + zero
        ≡⟨ cong (a * b +_) (sym *-zeroᴿ) ⟩
          a * b + a * zero
        ∎

      Ps : succProp P
      Ps {k} a[b+k]≡ab+ak =
        begin
          a * (b + succ k)
        ≡⟨ cong (a *_) +-succᴿ ⟩
          a * succ (b + k)
        ≡⟨ *-succᴿ ⟩
          a * (b + k) + a
        ≡⟨ cong (_+ a) a[b+k]≡ab+ak ⟩
          a * b + a * k + a
        ≡⟨ +-assoc ⟩
          a * b + (a * k + a)
        ≡⟨ cong (a * b +_) (sym *-succᴿ) ⟩
          a * b + a * succ k
        ∎

  *-distrib-+ᴿ : ∀ {a b c} → (a + b) * c ≡ a * c + b * c
  *-distrib-+ᴿ {a} {b} {c} =
    begin
      (a + b) * c
    ≡⟨ *-comm ⟩
      c * (a + b)
    ≡⟨ *-distrib-+ᴸ ⟩
      c * a + c * b
    ≡⟨ cong (_+ c * b) *-comm ⟩
      a * c + c * b
    ≡⟨ cong (a * c +_) *-comm ⟩
      a * c + b * c
    ∎

  *-assoc : ∀ {a b c} → (a * b) * c ≡ a * (b * c)
  *-assoc {a} {b} {c} = sym (ind P Pz Ps b)
    where
      P = λ x → a * (x * c) ≡ (a * x) * c
      Pz =
        begin
          a * (zero * c)
        ≡⟨ cong (a *_) *-zeroᴸ ⟩
          a * zero
        ≡⟨ *-zeroᴿ ⟩
          zero
        ≡⟨ sym *-zeroᴸ ⟩
          zero * c
        ≡⟨ cong (_* c) (sym *-zeroᴿ) ⟩
          (a * zero) * c
        ∎

      Ps : succProp P
      Ps {k} a[kc]≡[ak]c =
        begin
          a * (succ k * c)
        ≡⟨ cong (a *_) *-succᴸ ⟩
          a * (k * c + c)
        ≡⟨ *-distrib-+ᴸ ⟩
          a * (k * c) + a * c
        ≡⟨ cong (_+ a * c) a[kc]≡[ak]c ⟩
          (a * k) * c + a * c
        ≡⟨ sym *-distrib-+ᴿ ⟩
          (a * k + a) * c
        ≡⟨ cong (_* c) (sym *-succᴿ) ⟩
          (a * succ k) * c
        ∎
