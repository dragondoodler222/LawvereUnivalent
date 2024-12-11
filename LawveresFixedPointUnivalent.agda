{-# OPTIONS --cubical #-}

module LawveresFixedPointUnivalent where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; _×_)
open import Cubical.Categories.Category
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Instances.Sets
open import CartesianClosedUnivalentCategory
open import Utils

open Category
open CCCat

-- Assume we have a Cartesian Closed Univalent Category
variable
  ℓ ℓ' : Level

-- Open the category
variable
  CCUC : CCCat ℓ ℓ'

-- Lawvere's Fixed Point Theorem
LawveresFixedPoint :
  (CCUC : CCCat ℓ ℓ') → 
  ∀ {A : CCUC .ob} (f : CCUC [ A , A ] ) →
  Σ (CCUC [ terminal , A ]) (λ x → f ⋆ x ≡ x)
LawveresFixedPoint {A} f = (x , proof)
  where
    -- Define the diagonal morphism δ
    δ : CCUC [ A , (CCUC exponential A A) ]
    δ = curry proj₁

    -- Construct s = f ⋆ δ
    s : CCUC [ A , (CCUC exponential A A) ] 
    s = f ⋆ δ

    -- Define x : terminal → A
    x : Cat [ terminal , A ]
    x = eval ⋆ (s × terminate)

    -- Prove that f ⋆ x ≡ x
    proof : f ⋆ x ≡ x
    proof = finalEquality
      where
        -- First, note that f ⋆ x ≡ f ⋆ (eval ⋆ (s × terminate))
        step₁ : f ⋆ x ≡ f ⋆ (eval ⋆ (s × terminate))
        step₁ = cong (λ y → f ⋆ y) refl  -- Since x ≡ eval ⋆ (s × terminate)

        -- By associativity of composition: f ⋆ (eval ⋆ (s × terminate)) ≡ (f ⋆ eval) ⋆ (s × terminate)
        step₂ : f ⋆ (eval ⋆ (s × terminate)) ≡ (f ⋆ eval) ⋆ (s × terminate)
        step₂ = Cat ⋆Assoc f eval (s × terminate)

        -- By naturality of eval: f ⋆ eval ≡ eval ⋆ (f × id)
        step₃ : f ⋆ eval ≡ eval ⋆ (f × id {A = exponential A A})
        step₃ = eval-naturality f

        -- Therefore, (f ⋆ eval) ⋆ (s × terminate) ≡ eval ⋆ (f × id) ⋆ (s × terminate)
        step₄ : (f ⋆ eval) ⋆ (s × terminate) ≡ eval ⋆ (f × id) ⋆ (s × terminate)
        step₄ = cong (λ y → y ⋆ (s × terminate)) step₃

        -- Composition over product: (f × id) ⋆ (s × terminate) ≡ (f ⋆ s) × (id ⋆ terminate)
        step₅ : (f × id) ⋆ (s × terminate) ≡ (f ⋆ s) × (id ⋆ terminate)
        step₅ = prod-compose f id s terminate

        -- Since id ⋆ terminate ≡ terminate (because id is the identity morphism)
        step₆ : id ⋆ terminate ≡ terminate
        step₆ = Cat ⋆IdR terminate

        -- Therefore, (f × id) ⋆ (s × terminate) ≡ (f ⋆ s) × terminate
        step₇ : (f × id) ⋆ (s × terminate) ≡ (f ⋆ s) × terminate
        step₇ = cong (λ z → (f ⋆ s) × z) step₆

        c1 : (f × id) ⋆ (s × terminate) ≡ (f ⋆ s) × terminate
        c1 = 
            (f × id) ⋆ (s × terminate) 
          ≡⟨ step₅ ⟩ 
            (f ⋆ s) × (id ⋆ terminate) 
          ≡⟨ step₇ ⟩ 
            (f ⋆ s) × terminate
          ∎
        
        c2 : eval ⋆ (f × id) ⋆ (s × terminate) ≡ eval ⋆ (f ⋆ s) × terminate
        c2 = cong (eval ⋆_) c1

        c3 : f ⋆ x ≡ eval ⋆ ((f ⋆ s) × terminate)
        c3 = 
            f ⋆ x
          ≡⟨ step₁ ⟩ 
            f ⋆ (eval ⋆ (s × terminate))
          ≡⟨ step₂ ⟩ 
            (f ⋆ eval) ⋆ (s × terminate)
          ≡⟨ step₄ ⟩ 
            eval ⋆ (f × id) ⋆ (s × terminate)
          ≡⟨ c2 ⟩ 
            eval ⋆ (f ⋆ s) × terminate
          ∎

        -- Prove f ⋆ s ≡ s
        proof-f-s-eq-s : f ⋆ s ≡ s
        proof-f-s-eq-s =
          let
            step₁ : curry (proj₁ ⋆ (id × f)) ≡ curry proj₁ ⋆ f
            step₁ = curry_naturality_right f proj₁

            step₂ : proj₁ ⋆ (id × f) ≡ proj₁
            step₂ = Cat .refl _

            step₃ : curry (proj₁ ⋆ (id × f)) ≡ curry proj₁
            step₃ = cong curry step₂

            step₄ : curry proj₁ ⋆ f ≡ curry proj₁
            step₄ = curry proj₁ ⋆ f ≡⟨ step₁ ⟩ curry (proj₁ ⋆ (id × f)) ≡⟨ step₃ ⟩ curry proj₁ ∎

            s_eq_delta : s ≡ δ
            s_eq_delta = sym (Cat .refl _)

            s4_cmp_dlt : curry proj₁ ⋆ f ≡ δ
            s4_cmp_dlt = curry proj₁ ⋆ f ≡⟨ step₄ ⟩ curry proj₁ ≡⟨ s_eq_delta ⟩ δ

            finalEquality : f ⋆ s ≡ s
            finalEquality = f ⋆ δ ≡⟨ cong (f ⋆_) s_eq_delta ⟩ curry proj₁ ⋆ f ≡⟨ s4_cmp_dlt ⟩ δ
          in
          finalEquality

        -- Then, use proof-f-s-eq-s to complete the proof
        eq1 : (f ⋆ s) × terminate ≡ s × terminate
        eq1 = cong₂ _×_ proof-f-s-eq-s (Cat .refl terminate)

        eq2 : eval ⋆ ((f ⋆ s) × terminate) ≡ eval ⋆ (s × terminate)
        eq2 = cong (eval ⋆_) eq1

        eq3 : eval ⋆ (s × terminate) ≡ x
        eq3 = sym (Cat .refl x)

        finalEquality : f ⋆ x ≡ x
        finalEquality = 
          f ⋆ x
            ≡⟨ c3 ⟩
          eval ⋆ ((f ⋆ s) × terminate)
            ≡⟨ eq2 ⟩  
          eval ⋆ (s × terminate)
            ≡⟨ eq3 ⟩
          x
            ∎
