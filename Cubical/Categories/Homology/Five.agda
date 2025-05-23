module Cubical.Categories.Homology.Five where
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Abelian as AC hiding (Kernel)

module _ {ℓ ℓ' : Level} (C : AbelianCategory ℓ ℓ') where
  open AbelianCategory C
  Kernel = AC.Kernel preaddcat
  
  record Image {x y : ob} (f : Hom[ x , y ]) : Type (ℓ-max ℓ ℓ') where
    field
      i : ob
      m : Hom[ i , y ]
      e : Hom[ x , i ]
      e' : f ≡ e ⋆ m
      e'' : (i' : ob) (e' : Hom[ x , i' ]) (m' : Hom[ i' , y ]) → f ≡ e' ⋆ m' → Σ[ v ∈ Hom[ i , i' ] ] m ≡ v ⋆ m'

  isExact : {A B C : ob} (f : Hom[ A , B ]) (g : Hom[ B , C ]) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  isExact f g = Image f ≡ Kernel g

  module _ {A B C D E A' B' C' D' E' : ob} 
           {f : Hom[ A , B ]} {g : Hom[ B , C ]} {h : Hom[ C , D ]} {j : Hom[ D , E ]}
           {l : Hom[ A , A' ]} {m : Hom[ B , B' ]} {n : Hom[ C , C' ]} {p : Hom[ D , D' ]} {q : Hom[ E , E' ]}
           {r : Hom[ A' , B' ]} {s : Hom[ B' , C' ]} {t : Hom[ C' , D' ]} {u : Hom[ D' , E' ]}
           (fg : isExact f g) (gh : isExact g h) (hj : isExact h j)
           (rs : isExact r s) (st : isExact s t) (tu : isExact t u)
           where
    

  