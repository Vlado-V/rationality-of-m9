module

public import M9StacksIntegration.LagrangianArbitraryPlaneIncidence
public import M9StacksIntegration.LagrangianTripleNaturality
public import M9StacksIntegration.FiniteFreeBasisPullback
public import M9StacksIntegration.LagrangianSigmaInvariance

/-!
# The original arbitrary pair retains its full rank-drop ideal

The pair is a literal pair in the original six-space. The canonical
pullback of the actual universal quotient identifies its actual wedge
with the actual exterior evaluation of those same original sections.
The equality below is equality of full ideal sheaves on every native
test scheme, including nonreduced schemes; no symplecticity is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianArbitraryPairPullback
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open LagrangianUniversalSections SectionZeroIdealFactorization
open AlgebraicGeometry.Grassmannian
variable (K : Type u) [Field K]

theorem coefficient_eq_baseRingMap :
    LagrangianArbitraryPlaneIncidence.coefficient K =
      ExteriorEvaluation.baseRingMap K (projection K) := by
  unfold LagrangianArbitraryPlaneIncidence.coefficient ExteriorEvaluation.baseRingMap
  have h : (projection K).appLE ⊤ ⊤ (by simp) = (projection K).appTop :=
    (projection K).appLE_eq_app
  rw [h]

/-- The actual pullback of each original quotient section is the global
section of the actual original H0 class, with its structural coefficients. -/
theorem originalSection_pullback {X : Scheme.{u}} (l : X ⟶ space K)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) (i : Fin 2) :
    pullbackGlobalSections l (quotientOnLG K).target
      (LagrangianArbitraryPlaneIncidence.originalSection K w i) =
      (cohomologyOverFieldZeroLinearIso K (l ≫ projection K) (bundle K l)).hom
        (sectionMap K (l ≫ projection K) l (w i)) := by
  rw [LagrangianArbitraryPlaneIncidence.originalSection_eq_sum, sectionMap_sections]
  simp only [map_sum, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← FiniteFreeBasisPullback.pullbackPresentation_basis]
  change l.appTop.hom (LagrangianArbitraryPlaneIncidence.coefficient K (w i j)) •
    quotientSection K l j = _
  rw [coefficient_eq_baseRingMap]
  exact congrArg (fun a => a • quotientSection K l j)
    (RingHom.congr_fun (LagrangianTripleNaturality.baseRingMap_comp K (projection K) l)
      (w i j)).symm

/-- The actual exterior evaluation of this original pair, as an actual
global section of the original pulled-back quotient exterior power. -/
def pairSection {X : Scheme.{u}} (l : X ⟶ space K)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    Γ(Scheme.Modules.exteriorPower (bundle K l) (2 : ℤ), ⊤) :=
  (cohomologyOverFieldZeroLinearIso K (l ≫ projection K)
    (Scheme.Modules.exteriorPower (bundle K l) (2 : ℤ))).hom
      (ExteriorEvaluation.lambda K (l ≫ projection K) (bundle K l) 2
        (exteriorPower.ιMulti K 2 (fun i => sectionMap K (l ≫ projection K) l (w i))))

theorem pairSection_eq_wedge {X : Scheme.{u}} (l : X ⟶ space K)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    pairSection K l w = wedgeSection X (bundle K l)
      ((cohomologyOverFieldZeroLinearIso K (l ≫ projection K) (bundle K l)).hom
        (sectionMap K (l ≫ projection K) l (w 0)))
      ((cohomologyOverFieldZeroLinearIso K (l ≫ projection K) (bundle K l)).hom
        (sectionMap K (l ≫ projection K) l (w 1))) := by
  refine (ExteriorEvaluation.lambda_ιMulti K (l ≫ projection K) (bundle K l) 2
    (fun i => sectionMap K (l ≫ projection K) l (w i))).trans ?_
  rw [LagrangianSigmaInvariance.wedgeSection_eq_comparison]
  apply congrArg (ExteriorEvaluation.sectionComparison (bundle K l) 2 ⊤)
  apply congrArg (exteriorPower.ιMulti Γ(X, ⊤) 2)
  funext i
  fin_cases i <;> rfl

/-- The actual canonical exterior pullback comparison preserves the SAME
original pair, without changing its scalar or pair normalization. -/
theorem wedgeEquation_pullback {X : Scheme.{u}} (l : X ⟶ space K)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    (LagrangianPullback.exteriorPullbackIso l (quotientOnLG K).target 2).hom.app ⊤
      (pullbackGlobalSections l (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
        (LagrangianArbitraryPlaneIncidence.wedgeEquation K w)) = pairSection K l w := by
  rw [LagrangianArbitraryPlaneIncidence.wedgeEquation, exteriorPullback_wedgeSection,
    originalSection_pullback, originalSection_pullback, pairSection_eq_wedge]
  rfl

/-- The FULL native rank-drop ideal pulls back to the FULL zero ideal of
the actual original pair. This retains nilpotent test schemes. -/
theorem rankDropIdeal_comap_eq {X : Scheme.{u}} (l : X ⟶ space K)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    (LagrangianArbitraryPlaneIncidence.rankDropIdeal K w).comap l =
      SectionZeroIdealFactorization.sectionZeroIdeal X (Scheme.Modules.exteriorPower (bundle K l) (2 : ℤ))
        (pairSection K l w) := by
  letI := bundle_rank K l
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback l).obj (quotientOnLG K).target) 3 :=
    isFiniteLocallyFreeOfRank_pullback l (quotientOnLG K).target 3
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback l).obj (LagrangianArbitraryPlaneIncidence.wedgeBundle K)) 3 :=
    isFiniteLocallyFreeOfRank_pullback l (LagrangianArbitraryPlaneIncidence.wedgeBundle K) 3
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower (bundle K l) (2 : ℤ)) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (bundle K l) 3 2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback l).obj (quotientOnLG K).target)
        (2 : ℤ)) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      ((Scheme.Modules.pullback l).obj (quotientOnLG K).target) 3 2
  calc
    _ = SectionZeroIdealFactorization.sectionZeroIdeal X
        ((Scheme.Modules.pullback l).obj (LagrangianArbitraryPlaneIncidence.wedgeBundle K))
        (pullbackGlobalSections l (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
          (LagrangianArbitraryPlaneIncidence.wedgeEquation K w)) :=
      (sectionZeroIdeal_pullback l (LagrangianArbitraryPlaneIncidence.wedgeBundle K) 3 _).symm
    _ = SectionZeroIdealFactorization.sectionZeroIdeal X (Scheme.Modules.exteriorPower (bundle K l) (2 : ℤ))
        ((LagrangianPullback.exteriorPullbackIso l (quotientOnLG K).target 2).hom.app ⊤
          (pullbackGlobalSections l (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
            (LagrangianArbitraryPlaneIncidence.wedgeEquation K w))) :=
      sectionZeroIdeal_eq_of_iso 3
        (LagrangianPullback.exteriorPullbackIso l (quotientOnLG K).target 2) _
    _ = _ := by rw [wedgeEquation_pullback]

end M9Native.LagrangianArbitraryPairPullback
