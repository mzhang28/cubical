module Cubical.Categories.Additive.Instances.AbGroup where
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Additive.Base
open import Cubical.Categories.Instances.AbGroups
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open AdditiveCategory
open AdditiveCategoryStr
open PreaddCategory
open PreaddCategoryStr
open ZeroObject
open Biproduct

private variable ℓ ℓ' : Level

module _ where
  open AbGroupStr
  AbGroupPreaddCategory : PreaddCategory (ℓ-suc ℓ) ℓ
  AbGroupPreaddCategory .cat = AbGroupCategory
  AbGroupPreaddCategory .preadd .homAbStr x y .0g = trivGroupHom
  AbGroupPreaddCategory .preadd .homAbStr x y .AbGroupStr._+_ f g = 
    (λ a → y .snd .AbGroupStr._+_ (f .fst a) (g .fst a)) , makeIsGroupHom λ a b → {!   !}
  AbGroupStr.- AbGroupPreaddCategory .preadd .homAbStr x y = {!   !}
  AbGroupPreaddCategory .preadd .homAbStr x y .isAbGroup = {!   !}
  AbGroupPreaddCategory .preadd .⋆distl+ = {!   !}
  AbGroupPreaddCategory .preadd .⋆distr+ = {!   !}

AbGroupAdditiveCategory : AdditiveCategory (ℓ-suc ℓ) ℓ
AbGroupAdditiveCategory .preaddcat = AbGroupPreaddCategory
AbGroupAdditiveCategory .addit .zero .z = trivialAbGroup
AbGroupAdditiveCategory .addit .zero .zInit y =
  let open AbGroupStr (y .snd) in
  ((λ _ → 0g) , makeIsGroupHom (λ _ _ → sym (+IdR 0g))) , 
  (λ y' → Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (λ _ → sym (y' .snd .IsGroupHom.pres1))))
AbGroupAdditiveCategory .addit .zero .zTerm y = 
  let open AbGroupStr (y .snd) in
  ((λ _ → tt*) , makeIsGroupHom λ _ _ → refl) , 
  (λ y' → Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (λ _ → refl)))
AbGroupAdditiveCategory .addit .biprod x y .x⊕y = {!   !}
AbGroupAdditiveCategory .addit .biprod x y .i₁ = {!   !}
AbGroupAdditiveCategory .addit .biprod x y .i₂ = {!   !}
AbGroupAdditiveCategory .addit .biprod x y .π₁ = {!   !}
AbGroupAdditiveCategory .addit .biprod x y .π₂ = {!   !}
AbGroupAdditiveCategory .addit .biprod x y .isBipr = {!   !}