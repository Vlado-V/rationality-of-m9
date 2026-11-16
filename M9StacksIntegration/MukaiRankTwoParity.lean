module

public import M9StacksIntegration.MukaiHomTensorParity
public import M9StacksIntegration.MukaiNormalizedDeterminant
public import M9StacksIntegration.MukaiLineDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant

/-!
# Actual even H0 for Mukai's rank-two tensor bundles

The original two rank-two bundles and their actual determinant relation
are the only bundle data. A genuine line filtration is constructed on
the smooth integral curve, normalized by its genuine line inverse, and
fed to the actual Ext parity theorem. Its actual tensor middle is then
identified with the original tensor bundle.

This is the even-degree case of Mukai Proposition 1.2 needed in Lemma
5.2. Native Hom--Serre duality supplies the actual pairing without the
general Ext-duality import. Its check status is recorded separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.MukaiRankTwoParity

open M9Native.MukaiCupAlternating M9Native.MukaiHomCoefficient
open M9Native.MukaiNormalizedFiltration M9Native.MukaiNormalizedDeterminant
open M9Native.MukaiHomSerreTrace

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] [Smooth f]

/-- The actual rank-two tensor has even H0 from its original
determinant relation and original even degree. The line filtration,
normalized determinant, perfect pairing and alternation are all derived. -/
theorem even_H0_tensor_of_exterior_determinant (E F : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2)
    (d : tensor (exteriorSquare E) (exteriorSquare F) ≅ curveDualizingModule k f)
    (hdeg : letI := hE
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2)) :
    Even (Module.finrank k (cohomologyOverField k f (tensor E F) 0)) := by
  obtain ⟨L,M,hL,hM,_,i,q,w,hS⟩ :=
    M9Native.CurveLineSubbundle.exists_line_subbundle_on_smooth_curve k f F hF
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := hM
  let C := tensor E M
  let N := tensor L (inverseLine M)
  let hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2 :=
    M9Native.MukaiEulerEven.rankTwoTensorLine_rank E hE M
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
    M9Native.MukaiLineDegree.normalizedLine_invertible L M
  let Z := normalizedSequence (ShortComplex.mk i q w)
  have hZ := normalizedSequence_shortExact hS
  let dN : tensor N (exteriorSquare C) ≅ curveDualizingModule k f :=
    normalizedDeterminantIso E (curveDualizingModule k f) i q w hS d
  have hCdeg : letI := hC
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le C 2) :=
    M9Native.MukaiLineDegree.even_degree_tensor_line k f E hE M hdeg
  have h := M9Native.MukaiHomTensorParity.even_H0_tensorExtension k f C N Z.X₂
    hC Z.f Z.g Z.zero hZ
      (dN ≪≫ curveDualizingModuleIso k f (IsCurve.topologicalKrullDim_eq_one f)) hCdeg
  change Even (Module.finrank k (cohomologyOverField k f
    (tensor (tensor F (inverseLine M)) (tensor E M)) 0)) at h
  rw [finrank_cohomologyOverField_eq_of_iso k f (normalizedTensorMiddleIso E F M) 0] at h
  exact h

/-- The native annihilator-determinant relation implies the actual
exterior-square relation through the proved canonical comparison. -/
theorem even_H0_tensor_of_determinant (E F : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2)
    (d : tensor (Scheme.Modules.determinant E) (Scheme.Modules.determinant F) ≅
      curveDualizingModule k f)
    (hdeg : letI := hE
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2)) :
    Even (Module.finrank k (cohomologyOverField k f (tensor E F) 0)) := by
  let := hE
  let := hF
  let T : X.Modules ⥤ X.Modules ⥤ X.Modules :=
    Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf
  let eE : exteriorSquare E ≅ Scheme.Modules.determinant E :=
    Scheme.Modules.exteriorPowerIsoDeterminant E 2
  let eF : exteriorSquare F ≅ Scheme.Modules.determinant F :=
    Scheme.Modules.exteriorPowerIsoDeterminant F 2
  exact even_H0_tensor_of_exterior_determinant k f E F hE hF
    ((T.mapIso eE).app (exteriorSquare F) ≪≫
      (T.obj (Scheme.Modules.determinant E)).mapIso eF ≪≫ d) hdeg

/-- In particular, the genuine degree-eight rank-two bundles used by
Mukai have even tensor H0 once their actual canonical determinant relation
has been proved. No H0 parity or extension class is assumed. -/
theorem even_H0_tensor_of_degree_eight (E F : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2)
    (d : tensor (Scheme.Modules.determinant E) (Scheme.Modules.determinant F) ≅
      curveDualizingModule k f)
    (hdeg : letI := hE
      curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2 = 8) :
    Even (Module.finrank k (cohomologyOverField k f (tensor E F) 0)) := by
  apply even_H0_tensor_of_determinant k f E F hE hF d
  let := hE
  rw [hdeg]
  exact ⟨4, by norm_num⟩

end M9Native.MukaiRankTwoParity
