module

public import M9StacksIntegration.LagrangianBigCellPullbackCotangent
public import M9StacksIntegration.LagrangianCotangentSymplectic
public import M9StacksIntegration.LagrangianCotangentActionQuotient
public import M9StacksIntegration.LagrangianOpenImmersionIso
public import M9StacksIntegration.LagrangianAdmissibleCharts

/-! The actual global intrinsic cotangent isomorphism of the original native LG scheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianGlobalCotangent

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianChartCotangent LagrangianIsotropicDual LagrangianIsotropicRestriction
open LagrangianCotangentMap LagrangianCotangentSections LagrangianCotangentQuotientFrame
open LagrangianBigCellPullbackCotangent LagrangianCotangentEtale
open LagrangianCotangentSymplectic LagrangianCotangentActionQuotient
open LagrangianSymplecticAction LagrangianTranslatedCharts LagrangianOpenImmersionIso
open Stacks.AlgebraicGeometry.ReflexiveModules

private theorem isIso_congr_quotient {T B : Scheme.{u}} {F : T.Modules}
    (p : T ⟶ B) (q q' : freeOn T 6 ⟶ F) (h : q=q')
    (hq : AnnihilatesSigma T q) (hq' : AnnihilatesSigma T q') :
    IsIso (cotangentMap p q hq) ↔ IsIso (cotangentMap p q' hq') := by
  cases h
  rfl

private theorem isIso_of_pullback_cover {Y : Scheme.{u}} {F G : Y.Modules}
    (φ : F ⟶ G) {I : Type*} {Z : I → Scheme.{u}} (j : ∀ i,Z i ⟶ Y)
    [∀ i,IsOpenImmersion (j i)]
    (hj : ∀ y : Y,∃ i,y ∈ Set.range (j i).base)
    (h : ∀ i,IsIso ((Scheme.Modules.pullback (j i)).map φ)) : IsIso φ := by
  apply isIso_of_openImmersion_cover φ j hj
  intro i
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (j i)) φ).mpr (h i)

variable (K : Type u) [Field K]

/-- Actual constant symplectic covariance and actual universal quotient
isomorphisms transport the proved original big-cell calculation to every
actual translated chart. -/
theorem translatedIntrinsic_isIso (g : Matrix.symplecticGroup (Fin 3) K) :
    IsIso (cotangentMap (translatedBigCell K g ≫ projection K)
      (pulledQuotient (translatedBigCell K g) (quotientOnLG K).map)
      (pulledQuotient_annihilates (translatedBigCell K g) (quotientOnLG K).map
        (LagrangianSymplecticAction.lagrangianUniversal_annihilates K))) := by
  let q₀ := pulledQuotient (bigCell K) (quotientOnLG K).map
  let qₐ := pulledQuotient (translatedBigCell K g) (quotientOnLG K).map
  have h₀ : AnnihilatesSigma (chart K) q₀ :=
    pulledQuotient_annihilates (bigCell K) (quotientOnLG K).map
      (lagrangianUniversal_annihilates K)
  have hₐ : AnnihilatesSigma (chart K) qₐ :=
    pulledQuotient_annihilates (translatedBigCell K g) (quotientOnLG K).map
      (lagrangianUniversal_annihilates K)
  obtain ⟨e,he⟩ := pulled_action_isomorphic K (bigCell K) g
  have heq : qₐ ≫ e.hom=(constantFreeIso K (bigCell K ≫ projection K) g).hom ≫ q₀ := he
  have hpost : AnnihilatesSigma (chart K) (qₐ ≫ e.hom) :=
    annihilatesSigma_postcomp qₐ e.hom hₐ
  have hG : AnnihilatesSigma (chart K)
      ((constantFreeIso K (bigCell K ≫ projection K) g).hom ≫ q₀) := heq ▸ hpost
  have hbase : IsIso (cotangentMap (bigCell K ≫ projection K) q₀ h₀) :=
    pulledIntrinsic_isIso K
  have hSp : IsIso (cotangentMap (bigCell K ≫ projection K)
      ((constantFreeIso K (bigCell K ≫ projection K) g).hom ≫ q₀) hG) :=
    (cotangentMap_constant_symplectic K (bigCell K ≫ projection K) q₀ h₀ g hG).symm ▸ hbase
  have hframe : IsIso (cotangentMap (bigCell K ≫ projection K) (qₐ ≫ e.hom) hpost) :=
    (isIso_congr_quotient (bigCell K ≫ projection K) _ _ heq hpost hG).mpr hSp
  have hacted : IsIso (cotangentMap (bigCell K ≫ projection K) qₐ hₐ) :=
    cotangentMap_isIso_of_targetIso (bigCell K ≫ projection K) qₐ hₐ e hpost hframe
  have hp : translatedBigCell K g ≫ projection K=bigCell K ≫ projection K := by
    change (bigCell K ≫ action K g) ≫ projection K=_
    rw [Category.assoc,action_projection]
  exact (cotangentMap_isIso_congr (translatedBigCell K g ≫ projection K)
    (bigCell K ≫ projection K) hp qₐ hₐ).mpr hacted

/-- The literal original universal cotangent map is invertible after
actual pullback to every translated native chart. -/
instance universalCotangentMap_translated_isIso (g : Matrix.symplecticGroup (Fin 3) K) :
    IsIso ((Scheme.Modules.pullback (translatedBigCell K g)).map (universalCotangentMap K)) :=
  pullback_cotangentMap_isIso (translatedBigCell K g) (projection K) (quotientOnLG K).map
    (lagrangianUniversal_annihilates K) (quotientOnLG K).finiteLocallyFree.isFiniteLocallyFree
      (translatedIntrinsic_isIso K g)

/-- The original eight admissible native charts cover all points over
any field. Actual restriction and stalk detection globalize the actual
intrinsic map; no isomorphism or tangent-identification premise occurs. -/
instance universalCotangentMap_isIso : IsIso (universalCotangentMap K) := by
  apply isIso_of_pullback_cover (universalCotangentMap K)
    (LagrangianAdmissibleCharts.chart K) (LagrangianAdmissibleCharts.charts_cover K)
  intro s
  exact universalCotangentMap_translated_isIso K (LagrangianAdmissibleCharts.swap K s)⁻¹

/-- The actual native cotangent sheaf is the actual native symmetric
square of the dual of the original universal rank-three quotient. -/
def cotangentIso : Scheme.Hom.relativeDifferentials (projection K) ≅
    LagrangianDualCoefficients.symmetricSquare (dualSheaf (quotientOnLG K).target) :=
  (asIso (universalCotangentMap K)).symm

end M9Native.LagrangianGlobalCotangent
