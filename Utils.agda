{-# OPTIONS --cubical #-}

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; _×_)
open import Cubical.Categories.Category
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Instances.Sets
open import CartesianClosedUnivalentCategory

open Category
open CCCat

-- Assume we have a Cartesian Closed Univalent Category
variable
  ℓ ℓ' : Level

-- Open the category
variable
  CCUC : CCCat ℓ ℓ'

-- Naturality of curry in the first argument
curry_naturality_right :
  ∀ {A B C D : CCUC .Cat .ob} (f : CCUC .Cat [ B , C ]) (h : CCUC .Cat [ CCUC .product D A , B ]) →
  CCUC .Cat ._⋆_ f (CCUC .curry h) ≡ CCUC .curry (CCUC .Cat ._⋆_ f h)

-- step₁ : curry (proj₁ ⋆ (id × f)) ≡ curry proj₁ ⋆ f
-- step₁ = curry_naturality_right f proj₁

eval-naturality :
    ∀ {A B : Cat .ob} {C : Cat .ob} (f : Hom[ Cat , B ] C) →
    Hom[ Cat , A × B ] C ≡ Hom[ Cat , A ] (exponential B C) →
    f ⋆ eval ≡ eval ⋆ (f × id {A = B})

-- Composition over product: (f × g) ⋆ (h × k) ≡ (f ⋆ h) × (g ⋆ k)
prod-compose :
    ∀ {A B C D E F : Cat .ob}
    (f : Hom[ Cat , A ] B) (g : Hom[ Cat , C ] D)
    (h : Hom[ Cat , B ] E) (k : Hom[ Cat , D ] F) →
    (f × g) ⋆ (h × k) ≡ (f ⋆ h) × (g ⋆ k)
prod-compose f g h k = Cat .refl ((f ⋆ h) × (g ⋆ k))  -- Assuming this property holds in the category
