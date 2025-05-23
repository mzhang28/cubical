module Cubical.Categories.Abelian.Instances.AbGroup where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Abelian.Base
open import Cubical.Categories.Additive.Instances.AbGroup

open AbelianCategory
open AbelianCategoryStr

private variable ℓ ℓ' : Level

AbGroupPreAbCategory : PreAbCategory (ℓ-suc ℓ) ℓ
AbGroupPreAbCategory .PreAbCategory.additive = {!   !}
AbGroupPreAbCategory .PreAbCategory.preAbStr = {!   !}

AbGroupAbelianCategory : AbelianCategory (ℓ-suc ℓ) ℓ
AbGroupAbelianCategory .preAb = AbGroupPreAbCategory
AbGroupAbelianCategory .abelianStr = {!   !}