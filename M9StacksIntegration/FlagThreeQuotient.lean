module

public import StacksFrontier.AlgebraicGeometry.FlagTower.Tower
public import Mathlib.Tactic

/-!
# Actual rank-three quotient and three line pieces on a flag tower

On the native tower of three successive projective bundles of a finite
locally free sheaf `D`, the three actual quotient bundles have ranks one,
two, and three. The actual quotient maps `Q3 → Q2 → Q1` are epimorphisms
with locally free rank-one kernels. For the incidence application one
takes `D = E^dual`, then uses native finite-locally-free duality to regard
`Q3^dual` as a subbundle of the actual pullback of `E`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.FlagThreeQuotient

open Stacks.FlagTower

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} D]

abbrev space : Scheme.{u} := (tower 3 D).1
abbrev projection : space D ⟶ X := (tower 3 D).2

/-- The actual universal flag, obtained from the actual identity of
the native representing tower. -/
def universalFlag : Flag ((Scheme.Modules.pullback (projection D)).obj D) 3 :=
  towerEquiv 3 D (projection D) ⟨𝟙 _, by simp⟩

/-- The actual quotient of rank `j+1`, for `j=0,1,2`. -/
def quotientBundle (j : Fin 3) : (space D).Modules :=
  cokernel ((universalFlag D).sub j).arrow

def quotientMap (j : Fin 3) :
    (Scheme.Modules.pullback (projection D)).obj D ⟶ quotientBundle D j :=
  cokernel.π ((universalFlag D).sub j).arrow

instance quotientMap_epi (j : Fin 3) : Epi (quotientMap D j) :=
  inferInstanceAs (Epi (cokernel.π ((universalFlag D).sub j).arrow))

theorem quotientBundle_rank (j : Fin 3) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (quotientBundle D j) (j+1) :=
  (universalFlag D).rank j

/-- Quotient order induces an actual map between the actual quotient
sheaves. -/
def quotientStep {i j : Fin 3} (hij : i ≤ j) : quotientBundle D j ⟶ quotientBundle D i :=
  cokernel.desc ((universalFlag D).sub j).arrow (quotientMap D i) (by
    change ((universalFlag D).sub j).arrow ≫
      cokernel.π ((universalFlag D).sub i).arrow = 0
    rw [← Subobject.ofLE_arrow ((universalFlag D).antitone hij),
      Category.assoc, cokernel.condition, comp_zero])

theorem quotientMap_quotientStep {i j : Fin 3} (hij : i ≤ j) :
    quotientMap D j ≫ quotientStep D hij = quotientMap D i :=
  cokernel.π_desc _ _ _

instance quotientStep_epi {i j : Fin 3} (hij : i ≤ j) : Epi (quotientStep D hij) :=
  epi_of_epi_fac (quotientMap_quotientStep D hij)

abbrev step32 : quotientBundle D 2 ⟶ quotientBundle D 1 :=
  quotientStep D (show (1 : Fin 3) ≤ 2 by decide)

abbrev step21 : quotientBundle D 1 ⟶ quotientBundle D 0 :=
  quotientStep D (show (0 : Fin 3) ≤ 1 by decide)

def line3 : (space D).Modules := kernel (step32 D)
def line2 : (space D).Modules := kernel (step21 D)
abbrev line1 : (space D).Modules := quotientBundle D 0

/-- The actual two steps that filter the actual rank-three quotient. -/
theorem sequence32_shortExact :
    (ShortComplex.mk (kernel.ι (step32 D)) (step32 D) (kernel.condition (step32 D))).ShortExact :=
  { exact := ShortComplex.exact_kernel (step32 D) }

theorem sequence21_shortExact :
    (ShortComplex.mk (kernel.ι (step21 D)) (step21 D) (kernel.condition (step21 D))).ShortExact :=
  { exact := ShortComplex.exact_kernel (step21 D) }

/-- The first line piece is the actual rank-one quotient. -/
theorem line1_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (line1 D) 1 :=
  quotientBundle_rank D 0

/-- The middle line piece is the actual kernel of `Q2 → Q1`; its
rank is derived from exactness and native local freeness. -/
theorem line2_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (line2 D) 1 := by
  let S := ShortComplex.mk (kernel.ι (step21 D)) (step21 D) (kernel.condition (step21 D))
  have hS : S.ShortExact := sequence21_shortExact D
  have h2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ 2 :=
    quotientBundle_rank D 1
  have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ 1 :=
    quotientBundle_rank D 0
  have hk := Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact S hS
    h2.isFiniteLocallyFree h1.isFiniteLocallyFree
  exact Stacks.Conormal.isFiniteLocallyFreeOfRank_X₁_of_shortExact S hS 2 1 hk h2 h1

/-- The third line piece is the actual kernel of `Q3 → Q2`. -/
theorem line3_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (line3 D) 1 := by
  let S := ShortComplex.mk (kernel.ι (step32 D)) (step32 D) (kernel.condition (step32 D))
  have hS : S.ShortExact := sequence32_shortExact D
  have h3 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ 3 :=
    quotientBundle_rank D 2
  have h2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ 2 :=
    quotientBundle_rank D 1
  have hk := Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact S hS
    h3.isFiniteLocallyFree h2.isFiniteLocallyFree
  exact Stacks.Conormal.isFiniteLocallyFreeOfRank_X₁_of_shortExact S hS 3 2 hk h3 h2

/-- Quotient epimorphisms stay epimorphisms under arbitrary actual
scheme pullback, including the base-field points used in the incidence
emptiness argument. -/
theorem pullback_quotientMap_epi {T : Scheme.{u}} (f : T ⟶ space D) (j : Fin 3) :
    Epi ((Scheme.Modules.pullback f).map (quotientMap D j)) := by
  infer_instance

end M9Native.FlagThreeQuotient
