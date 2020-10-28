module net.cruhland.axioms.Peano.Multiplication where

open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (StarOp)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Ordering as PeanoOrdering
open import net.cruhland.models.Logic using
  (_∧_; ∧-elimᴿ; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; ⊥-elim)

record Multiplication (PB : PeanoBase) (PA : PeanoAddition PB) : Set where
  open PeanoAddition PA using
    ( _+_; +-assoc; +-both-zero; +-comm; Positive; +-stepᴿ; +-stepᴸ⃗ᴿ
    ; +-substᴸ; +-substᴿ; with-+-assoc; +-zeroᴸ; +-zeroᴿ
    )
  open PeanoBase PB using (ℕ; ind; step; step-case; zero)
  open PeanoInspect PB using (case; case-step; case-zero; pred-intro)
  open PeanoOrdering PB PA using
    (_<_; <→≄; <⁺→<; <→<⁺; <⁺-intro; tri-<; tri-≃; tri->; trichotomy)

  field
    {{star}} : StarOp ℕ

  open StarOp star public using (_*_)

  field
    *-zeroᴸ : ∀ {m} → zero * m ≃ zero
    *-stepᴸ : ∀ {n m} → step n * m ≃ n * m + m
    *-substᴸ : ∀ {n₁ n₂ m} → n₁ ≃ n₂ → n₁ * m ≃ n₂ * m

  *-zeroᴿ : ∀ {n} → n * zero ≃ zero
  *-zeroᴿ {n} = ind P Pz Ps n
    where
      P = λ x → x * zero ≃ zero
      Pz = *-zeroᴸ

      Ps : step-case P
      Ps {k} Pk =
        begin
          step k * zero
        ≃⟨ *-stepᴸ ⟩
          k * zero + zero
        ≃⟨ +-zeroᴿ ⟩
          k * zero
        ≃⟨ Pk ⟩
          zero
        ∎

  *-stepᴿ : ∀ {n m} → n * step m ≃ n * m + n
  *-stepᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x * step m ≃ x * m + x

      Pz =
        begin
          zero * step m
        ≃⟨ *-zeroᴸ ⟩
          zero
        ≃⟨ sym *-zeroᴸ ⟩
          zero * m
        ≃⟨ sym +-zeroᴿ ⟩
          zero * m + zero
        ∎

      Ps : step-case P
      Ps {k} Pk =
        begin
          step k * step m
        ≃⟨ *-stepᴸ ⟩
          k * step m + step m
        ≃⟨ +-substᴸ Pk ⟩
          k * m + k + step m
        ≃⟨ with-+-assoc (trans +-comm +-stepᴸ⃗ᴿ) ⟩
          k * m + m + step k
        ≃˘⟨ +-substᴸ *-stepᴸ ⟩
          step k * m + step k
        ∎

  *-comm : ∀ {n m} → n * m ≃ m * n
  *-comm {n} {m} = ind P Pz Ps n
    where
      P = λ x → x * m ≃ m * x
      Pz = trans *-zeroᴸ (sym *-zeroᴿ)

      Ps : step-case P
      Ps {k} Pk =
        begin
          step k * m
        ≃⟨ *-stepᴸ ⟩
          k * m + m
        ≃⟨ +-substᴸ Pk ⟩
          m * k + m
        ≃˘⟨ *-stepᴿ ⟩
          m * step k
        ∎

  *-oneᴸ : ∀ {n} → step zero * n ≃ n
  *-oneᴸ {n} =
    begin
      step zero * n
    ≃⟨ *-stepᴸ ⟩
      zero * n + n
    ≃⟨ +-substᴸ *-zeroᴸ ⟩
      zero + n
    ≃⟨ +-zeroᴸ ⟩
      n
    ∎

  *-oneᴿ : ∀ {n} → n * step zero ≃ n
  *-oneᴿ = trans *-comm *-oneᴸ

  *-either-zero : ∀ {n m} → n * m ≃ zero → n ≃ zero ∨ m ≃ zero
  *-either-zero {n} {m} n*m≃z with case n
  ... | case-zero n≃z = ∨-introᴸ n≃z
  ... | case-step (pred-intro p n≃sp) = ∨-introᴿ m≃z
    where
      p*m+m≃z =
        begin
          p * m + m
        ≃˘⟨ *-stepᴸ ⟩
          step p * m
        ≃˘⟨ *-substᴸ n≃sp ⟩
          n * m
        ≃⟨ n*m≃z ⟩
          zero
        ∎

      m≃z = ∧-elimᴿ (+-both-zero p*m+m≃z)

  *-substᴿ : ∀ {n m₁ m₂} → m₁ ≃ m₂ → n * m₁ ≃ n * m₂
  *-substᴿ {n} {m₁} {m₂} m₁≃m₂ =
    begin
      n * m₁
    ≃⟨ *-comm ⟩
      m₁ * n
    ≃⟨ *-substᴸ m₁≃m₂ ⟩
      m₂ * n
    ≃⟨ *-comm ⟩
      n * m₂
    ∎

  *-distrib-+ᴸ : ∀ {a b c} → a * (b + c) ≃ a * b + a * c
  *-distrib-+ᴸ {a} {b} {c} = ind P Pz Ps c
    where
      P = λ x → a * (b + x) ≃ a * b + a * x
      Pz =
        begin
          a * (b + zero)
        ≃⟨ *-substᴿ +-zeroᴿ ⟩
          a * b
        ≃˘⟨ +-zeroᴿ ⟩
          a * b + zero
        ≃˘⟨ +-substᴿ *-zeroᴿ ⟩
          a * b + a * zero
        ∎

      Ps : step-case P
      Ps {k} a[b+k]≃ab+ak =
        begin
          a * (b + step k)
        ≃⟨ *-substᴿ +-stepᴿ ⟩
          a * step (b + k)
        ≃⟨ *-stepᴿ ⟩
          a * (b + k) + a
        ≃⟨ +-substᴸ a[b+k]≃ab+ak ⟩
          a * b + a * k + a
        ≃⟨ +-assoc ⟩
          a * b + (a * k + a)
        ≃˘⟨ +-substᴿ *-stepᴿ ⟩
          a * b + a * step k
        ∎

  *-distrib-+ᴿ : ∀ {a b c} → (a + b) * c ≃ a * c + b * c
  *-distrib-+ᴿ {a} {b} {c} =
    begin
      (a + b) * c
    ≃⟨ *-comm ⟩
      c * (a + b)
    ≃⟨ *-distrib-+ᴸ ⟩
      c * a + c * b
    ≃⟨ +-substᴸ *-comm ⟩
      a * c + c * b
    ≃⟨ +-substᴿ *-comm ⟩
      a * c + b * c
    ∎

  *-assoc : ∀ {a b c} → (a * b) * c ≃ a * (b * c)
  *-assoc {a} {b} {c} = sym (ind P Pz Ps b)
    where
      P = λ x → a * (x * c) ≃ (a * x) * c
      Pz =
        begin
          a * (zero * c)
        ≃⟨ *-substᴿ *-zeroᴸ ⟩
          a * zero
        ≃⟨ *-zeroᴿ ⟩
          zero
        ≃˘⟨ *-zeroᴸ ⟩
          zero * c
        ≃˘⟨ *-substᴸ *-zeroᴿ ⟩
          (a * zero) * c
        ∎

      Ps : step-case P
      Ps {k} a[kc]≃[ak]c =
        begin
          a * (step k * c)
        ≃⟨ *-substᴿ *-stepᴸ ⟩
          a * (k * c + c)
        ≃⟨ *-distrib-+ᴸ ⟩
          a * (k * c) + a * c
        ≃⟨ +-substᴸ a[kc]≃[ak]c ⟩
          (a * k) * c + a * c
        ≃˘⟨ *-distrib-+ᴿ ⟩
          (a * k + a) * c
        ≃˘⟨ *-substᴸ *-stepᴿ ⟩
          (a * step k) * c
        ∎

  *-positive : ∀ {a b} → Positive a → Positive b → Positive (a * b)
  *-positive {a} {b} a≄z b≄z ab≃z with *-either-zero ab≃z
  ... | ∨-introᴸ a≃z = a≄z a≃z
  ... | ∨-introᴿ b≃z = b≄z b≃z

  *-preserves-< : ∀ {a b c} → a < b → c ≄ zero → a * c < b * c
  *-preserves-< {a} {b} {c} a<b c≄z with <→<⁺ a<b
  ... | <⁺-intro d d≄z a+d≃b = <⁺→< (<⁺-intro (d * c) dc≄z ac+dc≃bc)
    where
      dc≄z = *-positive d≄z c≄z
      ac+dc≃bc = trans (sym *-distrib-+ᴿ) (*-substᴸ a+d≃b)

  *-cancelᴿ : ∀ {a b c} → c ≄ zero → a * c ≃ b * c → a ≃ b
  *-cancelᴿ c≄z ac≃bc with trichotomy
  ... | tri-< a<b = ⊥-elim (<→≄ (*-preserves-< a<b c≄z) ac≃bc)
  ... | tri-≃ a≃b = a≃b
  ... | tri-> a>b = ⊥-elim (<→≄ (*-preserves-< a>b c≄z) (sym ac≃bc))

  *-cancelᴸ : ∀ {a b c} → a ≄ zero → a * b ≃ a * c → b ≃ c
  *-cancelᴸ a≄z ab≃ac = *-cancelᴿ a≄z (trans *-comm (trans ab≃ac *-comm))
