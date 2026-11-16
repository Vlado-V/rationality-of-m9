module

public import M9StacksIntegration.MukaiConormalOriginFrame
public import M9StacksIntegration.AffineFieldPullbackBasis
public import M9StacksIntegration.LagrangianPolynomialDifferentials

/-! Genuine cotangent functionals at the actual polynomial origin. Their
values on original universal differentials are the true dual-number jets. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiConormalPolynomialTangent

open MukaiConormalBigCellSections MukaiConormalBigCellFirstJet MukaiConormalOriginFrame

variable (K : Type u) [Field K]

local instance scalarInvPair :
    RingHomInvPair (LagrangianPolynomialDifferentials.scalarEquiv K).toRingHom
      (LagrangianPolynomialDifferentials.scalarEquiv K).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (LagrangianPolynomialDifferentials.scalarEquiv K)

local instance scalarInvPairRev :
    RingHomInvPair (LagrangianPolynomialDifferentials.scalarEquiv K).symm.toRingHom
      (LagrangianPolynomialDifferentials.scalarEquiv K).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (LagrangianPolynomialDifferentials.scalarEquiv K)

abbrev Cotangent := Scheme.Hom.relativeDifferentials (LagrangianChartCotangent.chartProjection K)
abbrev Source := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (zeroPoint K)).obj (Cotangent K))

local instance cotangent_isQuasicoherent : (Cotangent K).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (MukaiConormalBigCellSections.chart K).ringCatSheaf).prop_of_iso
    (LagrangianChartCotangent.affineCotangentIso K).symm inferInstance

def direction (B : LagrangianField.Symmetric3 K) (i : Fin 6) : K :=
  B.val (LagrangianMatrixChart.symmetricEntryEquivFinSix.{u}.symm i).down.val.1
    (LagrangianMatrixChart.symmetricEntryEquivFinSix.{u}.symm i).down.val.2

def coefficients : Source K ≃ₗ[K] (Fin 6 → K) :=
  AffineFieldPullbackBasis.coordinates K (zeroPoint K) (Cotangent K)
    (LagrangianPolynomialDifferentials.sectionsBasis K)

def jetValue (B : LagrangianField.Symmetric3 K) : Source K →ₗ[K] K :=
  ∑ i : Fin 6, direction K B i •
    ((LinearMap.proj i).comp (coefficients K).toLinearMap)

theorem jetValue_apply (B : LagrangianField.Symmetric3 K) (s : Source K) :
    jetValue K B s = ∑ i : Fin 6, direction K B i * coefficients K s i := by
  simp only [jetValue, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, smul_eq_mul, LinearEquiv.coe_coe]

theorem section_d_expansion (r : PolynomialRing K) :
    (Scheme.Hom.universalRelativeDerivation (LagrangianChartCotangent.chartProjection K)).d
        (MukaiConormalBigCellSections.scalarEquiv K r) =
      ∑ i : Fin 6, MukaiConormalBigCellSections.scalarEquiv K (MvPolynomial.pderiv i r) •
        LagrangianPolynomialDifferentials.sectionsBasis K i := by
  let b := KaehlerDifferential.mvPolynomialBasis K (Fin 6)
  let e := LagrangianPolynomialDifferentials.sectionsEquiv K
  have hb (i : Fin 6) : e (b i) = LagrangianPolynomialDifferentials.sectionsBasis K i := by
    rw [KaehlerDifferential.mvPolynomialBasis_apply,LagrangianPolynomialDifferentials.sectionsEquiv_d]
    exact (LagrangianPolynomialDifferentials.sectionsBasis_apply K i).symm
  calc
    _ = e (KaehlerDifferential.D K (PolynomialRing K) r) :=
      (LagrangianPolynomialDifferentials.sectionsEquiv_d K r).symm
    _ = e (∑ i : Fin 6, b.repr (KaehlerDifferential.D K (PolynomialRing K) r) i • b i) :=
      congrArg e (b.sum_repr _).symm
    _ = ∑ i : Fin 6, e (b.repr (KaehlerDifferential.D K (PolynomialRing K) r) i • b i) :=
      map_sum e.toAddEquiv _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearEquiv.map_smulₛₗ,hb]
      simp only [b,KaehlerDifferential.mvPolynomialBasis_repr_apply]
      rfl

theorem section_d_coordinates (r : PolynomialRing K) :
    (LagrangianPolynomialDifferentials.sectionsBasis K).equivFun
      ((Scheme.Hom.universalRelativeDerivation (LagrangianChartCotangent.chartProjection K)).d
        (MukaiConormalBigCellSections.scalarEquiv K r)) =
      fun i => MukaiConormalBigCellSections.scalarEquiv K (MvPolynomial.pderiv i r) := by
  rw [section_d_expansion]
  ext i
  simp only [map_sum,map_smul,Module.Basis.equivFun_self,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem coefficients_d (r : PolynomialRing K) :
    coefficients K (pullbackGlobalSections (zeroPoint K) (Cotangent K)
      ((Scheme.Hom.universalRelativeDerivation (LagrangianChartCotangent.chartProjection K)).d
        (MukaiConormalBigCellSections.scalarEquiv K r))) =
      fun i => originEval K (MvPolynomial.pderiv i r) := by
  rw [coefficients, AffineFieldPullbackBasis.coordinates_global, section_d_coordinates]
  ext i
  change (Scheme.ΓSpecIso (.of K)).hom
    ((zeroPoint K).appTop (MukaiConormalBigCellSections.scalarEquiv K (MvPolynomial.pderiv i r))) = _
  rw [zeroPoint_scalar]
  exact (Scheme.ΓSpecIso (.of K)).inv_hom_id_apply _

theorem tangentEval_fst (B : LagrangianField.Symmetric3 K) (r : PolynomialRing K) :
    (tangentEval K B r).fst = originEval K r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [tangentEval,originEval,TrivSqZeroExt.algebraMap_eq_inl,TrivSqZeroExt.fst_inl]
  | add p q hp hq => simp only [map_add, TrivSqZeroExt.fst_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, TrivSqZeroExt.fst_mul, hp]
    simp [tangentEval, originEval]

theorem tangentEval_snd (B : LagrangianField.Symmetric3 K) (r : PolynomialRing K) :
    (tangentEval K B r).snd =
      ∑ i : Fin 6, direction K B i * originEval K (MvPolynomial.pderiv i r) := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [tangentEval,TrivSqZeroExt.algebraMap_eq_inl,TrivSqZeroExt.snd_inl]
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add,
      mul_add, Finset.sum_add_distrib]
    rw [hp, hq]
  | mul_X p i hp =>
    have ht : tangentEval K B (MvPolynomial.X i) = (0, direction K B i) := by
      simp [tangentEval, direction]
    rw [map_mul, ht]
    simp only [TrivSqZeroExt.snd_mul, tangentEval_fst,
      TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, smul_eq_mul]
    simp [MvPolynomial.pderiv_X,originEval,mul_comm,Pi.single_apply,apply_ite]

/-- The true field-point cotangent functional applied to the original
universal differential is the original dual-number first coefficient. -/
theorem jetValue_d (B : LagrangianField.Symmetric3 K) (r : PolynomialRing K) :
    jetValue K B (pullbackGlobalSections (zeroPoint K) (Cotangent K)
      ((Scheme.Hom.universalRelativeDerivation (LagrangianChartCotangent.chartProjection K)).d
        (MukaiConormalBigCellSections.scalarEquiv K r))) = (tangentEval K B r).snd := by
  rw [jetValue_apply, coefficients_d, tangentEval_snd]

end M9Native.MukaiConormalPolynomialTangent
