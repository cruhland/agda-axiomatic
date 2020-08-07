module net.cruhland.axioms.Sets.Comprehension where

open import Level using (Setω)
open import net.cruhland.axioms.Sets.Base using
  (α; σ₁; σ₂; El; S; SetAxioms; Setoid)

record Comprehension (SA : SetAxioms) : Setω where
  open SetAxioms SA using (PSet)

  field
    ⟨_~_⟩ :
      let open Setoid S using (_≈_)
       in (P : El S → Set α) → (∀ {x y} → x ≈ y → P x → P y) → PSet S α
