module

public import M9StacksIntegration.LagrangianAffineFamilyAutomorphism
public import M9StacksIntegration.LagrangianVariableQuotientSections
public import M9StacksIntegration.LineFramePullback

/-! The literal arbitrary-plane equation on the actual native affine
line over LG. A genuine symplectic family automorphism carries the
original first-section equation to this equation by an explicitly
constructed original quotient-bundle isomorphism. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module Opposite
open scoped BigOperators
universe u

namespace M9Native.LagrangianAffinePlaneSection

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianTransitivity
open LagrangianVariableSymplecticAction LagrangianVariableQuotientSections
open SymplecticPlaneLineNormalizer

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable (K : Type u) [Field K]

abbrev CoordinateIndex := ULift.{u} (Fin 1)
abbrev chartSpace : Scheme.{u} := LagrangianAffineFamilyAutomorphism.affineLG K CoordinateIndex
abbrev parameterSpace : Scheme.{u} := LagrangianAffineFamilyAutomorphism.affineBase K CoordinateIndex
abbrev toLG : chartSpace K ⟶ space K :=
  LagrangianAffineFamilyAutomorphism.lgProjection K CoordinateIndex
abbrev parameterMap : chartSpace K ⟶ parameterSpace K :=
  LagrangianAffineFamilyAutomorphism.parameterMap K CoordinateIndex
abbrev parameterProjection : parameterSpace K ⟶ Spec (.of K) :=
  LagrangianAffineFamilyAutomorphism.baseProjection K CoordinateIndex

def parameter : Γ(chartSpace K,⊤) := AffineSpace.coord (space K) (ULift.up (0 : Fin 1))
def baseParameter : Γ(parameterSpace K,⊤) :=
  AffineSpace.coord (Spec (.of K)) (ULift.up (0 : Fin 1))

abbrev quotientBundle : (chartSpace K).Modules :=
  (Scheme.Modules.pullback (toLG K)).obj (quotientOnLG K).target
instance quotientBundle_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientBundle K) 3 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (toLG K) (quotientOnLG K).target 3
instance quotientBundle_finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientBundle K) :=
  (quotientBundle_rank K).isFiniteLocallyFree

/-- The actual equation Q(w0)+t Q(w1), in the original pulled quotient. -/
def lineSection (w : Fin 2 → LagrangianRing.V K) : Γ(quotientBundle K,⊤) :=
  pullbackGlobalSections (toLG K) (quotientOnLG K).target
    (LagrangianArbitraryPlaneIncidence.originalSection K w 0) +
  parameter K • pullbackGlobalSections (toLG K) (quotientOnLG K).target
    (LagrangianArbitraryPlaneIncidence.originalSection K w 1)

def fixedSection : Γ(quotientBundle K,⊤) :=
  pullbackGlobalSections (toLG K) (quotientOnLG K).target
    (LagrangianCommonKernelZero.standardSection K)

/-- The original polynomial-family normalizer, over genuine affine
parameter space and its actual global functions. -/
def parameterMatrix (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    Matrix.symplecticGroup (Fin 3) Γ(parameterSpace K,⊤) :=
  normalizer K w hw (LagrangianSymplecticAction.scalarMap K (parameterProjection K))
    (baseParameter K)

def automorphism (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    chartSpace K ≅ chartSpace K :=
  LagrangianAffineFamilyAutomorphism.automorphism K CoordinateIndex (parameterMatrix K w hw)

@[reassoc] theorem automorphism_toLG (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) :
    (automorphism K w hw).hom ≫ toLG K = actPoint K (toLG K)
      (LagrangianAffineFamilyAutomorphism.matrixOnLG K CoordinateIndex (parameterMatrix K w hw)) :=
  LagrangianAffineFamilyAutomorphism.automorphism_hom_toLG K CoordinateIndex
    (parameterMatrix K w hw)

theorem parameterMatrix_column (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) (j : Fin 6) :
    matrixSix Γ(parameterSpace K,⊤) (parameterMatrix K w hw) j 0 =
      LagrangianSymplecticAction.scalarMap K (parameterProjection K) (w 0 j) +
      baseParameter K * LagrangianSymplecticAction.scalarMap K (parameterProjection K) (w 1 j) := by
  have h := congrFun (normalizer_sends_first K w hw
    (LagrangianSymplecticAction.scalarMap K (parameterProjection K)) (baseParameter K)) j
  simpa only [parameterMatrix,Matrix.mulVec_single_one,Matrix.col_apply,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,constantVector,Function.comp_apply] using h

theorem mappedMatrix_column (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) (j : Fin 6) :
    matrixSix Γ(chartSpace K,⊤)
      (LagrangianAffineFamilyAutomorphism.matrixOnLG K CoordinateIndex (parameterMatrix K w hw)) j 0 =
      LagrangianSymplecticAction.scalarMap K (toLG K ≫ projection K) (w 0 j) +
      parameter K * LagrangianSymplecticAction.scalarMap K (toLG K ≫ projection K) (w 1 j) := by
  have hρ (a : K) : (parameterMap K).appTop
      (LagrangianSymplecticAction.scalarMap K (parameterProjection K) a) =
        LagrangianSymplecticAction.scalarMap K (toLG K ≫ projection K) a := by
    change LagrangianSymplecticAction.scalarMap K
      (parameterMap K ≫ parameterProjection K) a = _
    rw [AffineSpace.map_over]
  change (parameterMap K).appTop
    (matrixSix Γ(parameterSpace K,⊤) (parameterMatrix K w hw) j 0) = _
  rw [parameterMatrix_column,map_add,map_mul,hρ,hρ]
  congr 2
  exact AffineSpace.map_appTop_coord (projection K) (ULift.up (0 : Fin 1))

/-- The original quotient-bundle comparison is built from the actual
native pullbackComp/pullbackCongr and the proved variable quotient map. -/
def sectionIso (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    (Scheme.Modules.pullback (automorphism K w hw).hom).obj (quotientBundle K) ≅ quotientBundle K :=
  (Scheme.Modules.pullbackComp (automorphism K w hw).hom (toLG K)).app (quotientOnLG K).target ≪≫
    (Scheme.Modules.pullbackCongr (automorphism_toLG K w hw)).app (quotientOnLG K).target ≪≫
    targetIso K (toLG K)
      (LagrangianAffineFamilyAutomorphism.matrixOnLG K CoordinateIndex (parameterMatrix K w hw))

/-- The actual first-section equation becomes the actual original
arbitrary-plane equation, as an equality of genuine sheaf sections. -/
theorem sectionIso_apply (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    (sectionIso K w hw).hom.app ⊤
      (pullbackGlobalSections (automorphism K w hw).hom (quotientBundle K) (fixedSection K)) =
        lineSection K w := by
  change (targetIso K (toLG K)
      (LagrangianAffineFamilyAutomorphism.matrixOnLG K CoordinateIndex (parameterMatrix K w hw))).hom.app ⊤
    (((Scheme.Modules.pullbackCongr (automorphism_toLG K w hw)).hom.app
      (quotientOnLG K).target).app ⊤
      (((Scheme.Modules.pullbackComp (automorphism K w hw).hom (toLG K)).hom.app
        (quotientOnLG K).target).app ⊤
        (pullbackGlobalSections (automorphism K w hw).hom (quotientBundle K)
          (pullbackGlobalSections (toLG K) (quotientOnLG K).target
            (LagrangianCommonKernelZero.standardSection K))))) = _
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr,
    targetIso_standardSection]
  simp_rw [mappedMatrix_column,add_smul,mul_smul]
  rw [Finset.sum_add_distrib,← Finset.smul_sum,
    ← originalSection_pullback,← originalSection_pullback]
  rfl

@[reassoc] theorem automorphism_groundProjection (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) :
    (automorphism K w hw).hom ≫ toLG K ≫ projection K = toLG K ≫ projection K :=
  LagrangianAffineFamilyAutomorphism.automorphism_hom_groundProjection K CoordinateIndex
    (parameterMatrix K w hw)

end M9Native.LagrangianAffinePlaneSection
