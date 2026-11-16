module

public import M9StacksIntegration.LagrangianPluckerQuotient
public import M9StacksIntegration.SectionZeroIdealFactorization
public import M9StacksIntegration.ChowFreeBundleChern
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear

/-! Actual projective-line incidence for an arbitrary pair of original
free-six vectors. Independence of the pair is reserved for the later
geometric regularity theorem; none of the definitions or zero-ideal
universal properties assumes symplecticity, an empty rank-zero locus,
regularity, dimension, or a Chow class calculation. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow
open scoped BigOperators
universe u

namespace M9Native.LagrangianArbitraryPlaneIncidence

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
variable (K : Type u) [Field K]

abbrev PlaneFrame := Fin 2 → (Fin 6 → K)

/-- The actual coefficient map of the original LG structure morphism. -/
def coefficient : K →+* Γ(space K,⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ (projection K).appTop).hom

/-- The original vector in the actual free-six sheaf. -/
def vectorSection (v : Fin 6 → K) : Γ(freeOn (space K) 6,⊤) :=
  ∑ j : Fin 6, coefficient K (v j) • freeBasisSection (space K) 6 j

/-- The original universal quotient applied to the actual plane vector. -/
def originalSection (w : PlaneFrame K) (i : Fin 2) : Γ((quotientOnLG K).target,⊤) :=
  Scheme.Modules.Hom.app (quotientOnLG K).map ⊤ (vectorSection K (w i))

theorem originalSection_eq_sum (w : PlaneFrame K) (i : Fin 2) :
    originalSection K w i = ∑ j : Fin 6, coefficient K (w i j) •
      Scheme.Modules.Hom.app (quotientOnLG K).map ⊤ (freeBasisSection (space K) 6 j) := by
  simp only [originalSection,vectorSection,map_sum,Scheme.Modules.Hom.app_smul]

abbrev wedgeBundle : (space K).Modules := Scheme.Modules.exteriorPower (quotientOnLG K).target 2
instance wedgeBundle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (wedgeBundle K) 3 := by
  simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (quotientOnLG K).target 3 2

def wedgeEquation (w : PlaneFrame K) : Γ(wedgeBundle K,⊤) :=
  wedgeSection (space K) (quotientOnLG K).target (originalSection K w 0) (originalSection K w 1)
def rankDropIdeal (w : PlaneFrame K) : (space K).IdealSheafData :=
  sectionZeroIdeal (space K) (wedgeBundle K) (wedgeEquation K w)
abbrev rankDrop (w : PlaneFrame K) : Scheme.{u} := (rankDropIdeal K w).subscheme
abbrev rankDropInclusion (w : PlaneFrame K) : rankDrop K w ⟶ space K :=
  (rankDropIdeal K w).subschemeι
instance rankDropInclusion_isClosedImmersion (w : PlaneFrame K) :
    IsClosedImmersion (rankDropInclusion K w) := inferInstance

theorem factors_rankDrop_iff_wedge_zero (w : PlaneFrame K) {T : Scheme.{u}} (f : T ⟶ space K) :
    (∃ g : T ⟶ rankDrop K w, g ≫ rankDropInclusion K w = f) ↔
      pullbackGlobalSections f (wedgeBundle K) (wedgeEquation K w) = 0 :=
  (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (wedgeBundle K) 3 (wedgeEquation K w) f).symm

abbrev planeSource : (space K).Modules := freeOn (space K) 2
instance planeSource_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (planeSource K) 2 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free (R := (space K).ringCatSheaf) 2
instance planeSource_isFiniteLocallyFree : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (planeSource K) :=
  (planeSource_rank K).isFiniteLocallyFree

abbrev ambient : Scheme.{u} := bundle (planeSource K)
abbrev toLG : ambient K ⟶ space K := bundleProj (planeSource K)
instance toLG_isProper : IsProper (toLG K) := inferInstance
abbrev lineBundle : (ambient K).Modules := bundleTwist (planeSource K)
instance lineBundle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (lineBundle K) 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (ambient K) (lineBundle K)
    (isInvertible_bundleTwist (planeSource K))
abbrev quotientBundle : (ambient K).Modules :=
  (Scheme.Modules.pullback (toLG K)).obj (quotientOnLG K).target
instance quotientBundle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientBundle K) 3 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (toLG K) (quotientOnLG K).target 3

def lineCoordinate (i : Fin 2) : Γ(lineBundle K,⊤) :=
  (bundleTautological (planeSource K)).app ⊤
    (pullbackGlobalSections (toLG K) (planeSource K) (freeBasisSection (space K) 2 i))
def quotientSection (w : PlaneFrame K) (i : Fin 2) : Γ(quotientBundle K,⊤) :=
  pullbackGlobalSections (toLG K) (quotientOnLG K).target (originalSection K w i)

/-- The literal Q-first tensor order required by native projective integration. -/
abbrev equationBundle : (ambient K).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (ambient K).sheaf).obj (quotientBundle K)).obj
    (lineBundle K)
instance equationBundle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle K) 3 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf
    (ambient K) (quotientBundle K) (lineBundle K) 3 1

def tensorSection (s : Γ(quotientBundle K,⊤)) (t : Γ(lineBundle K,⊤)) : Γ(equationBundle K,⊤) :=
  Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf (ambient K).sheaf)
    (Stacks.SheafOfModules.tensorSectionPairing (O := (ambient K).sheaf)
      (quotientBundle K) (lineBundle K)) (op ⊤) s t

def equationSection (w : PlaneFrame K) : Γ(equationBundle K,⊤) :=
  ∑ i : Fin 2, tensorSection K (quotientSection K w i) (lineCoordinate K i)
def incidenceIdeal (w : PlaneFrame K) : (ambient K).IdealSheafData :=
  sectionZeroIdeal (ambient K) (equationBundle K) (equationSection K w)
abbrev incidence (w : PlaneFrame K) : Scheme.{u} := (incidenceIdeal K w).subscheme
abbrev incidenceInclusion (w : PlaneFrame K) : incidence K w ⟶ ambient K :=
  (incidenceIdeal K w).subschemeι
abbrev incidenceToLG (w : PlaneFrame K) : incidence K w ⟶ space K := incidenceInclusion K w ≫ toLG K
instance incidenceInclusion_isClosedImmersion (w : PlaneFrame K) :
    IsClosedImmersion (incidenceInclusion K w) := inferInstance
instance incidenceToLG_isProper (w : PlaneFrame K) : IsProper (incidenceToLG K w) := inferInstance

theorem factors_incidence_iff_tensor_zero (w : PlaneFrame K) {T : Scheme.{u}} (f : T ⟶ ambient K) :
    (∃ g : T ⟶ incidence K w, g ≫ incidenceInclusion K w = f) ↔
      pullbackGlobalSections f (equationBundle K) (equationSection K w) = 0 :=
  (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (equationBundle K) 3 (equationSection K w) f).symm

end M9Native.LagrangianArbitraryPlaneIncidence
