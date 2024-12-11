{-# OPTIONS --cubical #-}

module CatSet where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; _×_)
open import Cubical.Categories.Category
open import Cubical.Categories.Category.Properties
open import Cubical.Categories.Instances.Sets
open import CartesianClosedUnivalentCategory
open import Cubical.Data.Unit

open import Utils


-- Assume we have a Cartesian Closed Univalent Category
variable
  ℓ ℓ' : Level

-- Instantiate your Cartesian Closed Univalent Category
SetsCCUC : (ℓ : Level) → CartesianClosedUnivalentCategory (lsuc ℓ) ℓ
SetsCCUC = λ ℓ → record
  { Cat = SET ℓ
  ; Univ = isUnivalentSET
  ; terminal = Unit* , isSetUnit*
  ; terminate = λ { (A , _) } → λ _ → lift tt
  ; product = λ A → λ B → (fst A × fst B) , isSet× (snd A) (snd B)
  ; proj₁ = λ { X Y } → λ (x , y) → x
  ; proj₂ = λ { X Y } → λ (x , y) → y
  ; pair = λ f g x → (f x , g x)
  ; pair-proj₁ = λ { f } { g } → refl
  ; pair-proj₂ = λ { f } { g } → refl
  ; pair-unique = λ { f } { g } { h } p₁ p₂ → funExt λ x → cong₂ (_,_) ((funExt⁻ p₁) x) ((funExt⁻ p₂) x) 
  ; exponential = λ A → λ B → (fst A → fst B) , isSetΠ (λ (x : fst A) → snd B)
  ; eval = λ { X Y } → λ (f , a) → f a
  ; curry = λ f x → λ a → f (x , a)
  ; uncurry = λ g (x , a) → g x a
  ; curry-uncurry = λ f → funExt λ (x , a) → refl
  ; uncurry-curry = λ g → funExt λ x → refl
  }