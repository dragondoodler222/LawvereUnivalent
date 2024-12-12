{-# OPTIONS --cubical #-}

module CartesianClosedUnivalentCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_)
open import Cubical.Foundations.Univalence
open import Cubical.Categories.Category
open import Cubical.Foundations.Equiv

-- Cartesian closed univalent category interface
record CCCat (ℓobj ℓhom : Level) : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where
  open Category

  field
    Cat : Category ℓobj ℓhom
    Univ : isUnivalent Cat

    terminal : Cat .ob
    terminate : ∀ {A : Cat .ob} → Cat [ A , terminal ]

    -- Binary products
    product : (A B : Cat .ob) → Cat .ob
    proj₁ : ∀ {A B : Cat .ob} → Cat [ (product A B) , A ]
    proj₂ : ∀ {A B : Cat .ob} → Cat [ (product A B) , B ]
    pair : ∀ {A B C : Cat .ob} → Cat [ C , A ] → Cat [ C , B ] → Cat [ C , (product A B) ]

    -- Universal property of products
    pair-proj₁ : ∀ {A B C : Cat .ob} {f : Cat [ C , A ]} {g : Cat [ C , B ]} →
            --    [ A x B , A ] * [ C , A x B ]
                   proj₁ ∘⟨ Cat ⟩ (pair f g) ≡ f
    pair-proj₂ : ∀ {A B C : Cat .ob} {f : Cat [ C , A ]} {g : Cat [ C , B ]} →
                    proj₂ ∘⟨ Cat ⟩  (pair f g) ≡ g
    pair-unique : ∀ {A B C : Cat .ob} {f : Cat [ C , A ]} {g : Cat [ C , B ]} {h : Cat [ C , (product A B) ]} →
                    proj₁ ∘⟨ Cat ⟩ h ≡ f → proj₂ ∘⟨ Cat ⟩ h ≡ g → h ≡ pair f g

    -- Exponential .Cat .objects
    exponential : (A B : Cat .ob) → Cat .ob
    eval : ∀ {A B : Cat .ob} → Cat [ (product (exponential A B) A) , B ]
    curry : ∀ {A B C : Cat .ob} → Cat [ (product C A) , B ] → Cat [ C , (exponential A B) ]
    uncurry : ∀ {A B C : Cat .ob} → Cat [ C , (exponential A B) ] → Cat [ (product C A) , B ]

    -- Adjunction between products and exponentials
    curry-uncurry : ∀ {A B C : Cat .ob} (f : Cat [ (product C A) , B ]) →
                      uncurry (curry f) ≡ f
    uncurry-curry : ∀ {A B C : Cat .ob} (g : Cat [ C , (exponential A B) ]) →
                      curry (uncurry g) ≡ g

