module

public import M9StacksIntegration.MukaiEulerEven
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic

/-!
# Genuine normalized line and even tensor degree

Both inputs to normalized tensor parity are constructed: the actual
inverse-twisted coefficient is invertible, and the actual rank-two tensor
quotient has even degree whenever the original rank-two bundle does.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.MukaiLineDegree

open M9Native.MukaiHomCoefficient M9Native.MukaiNormalizedFiltration

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : Scheme.{u}}

/-- The actual normalized coefficient is a line bundle, from the actual
two original line bundles and their actual tensor inverse. -/
theorem normalizedLine_invertible (L M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensor L (inverseLine M)) := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  let hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (inverseLine M) :=
    Scheme.Modules.isInvertible_tensorInverse M
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (inverseLine M) := hM
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (inverseLine M)
  have hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor L (inverseLine M)) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X L (inverseLine M) 1 1
  exact (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    X (tensor L (inverseLine M))).mpr hr

/-- Even degree of the actual normalized quotient follows from the
native tensor-degree formula; no degree parity is assumed for that quotient. -/
theorem even_degree_tensor_line (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (E : X.Modules) (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (hdeg : letI := hE
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2)) :
    letI := M9Native.MukaiEulerEven.rankTwoTensorLine_rank E hE M
    Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le (tensor E M) 2) := by
  let := hE
  let := M9Native.MukaiEulerEven.rankTwoTensorLine_rank E hE M
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M)
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X M
  let hdim := (IsCurve.topologicalKrullDim_eq_one f).le
  have hd : curveDegree k f hdim (tensor E M) 2 =
      curveDegree k f hdim E 2 + 2 * curveDegree k f hdim M 1 := by
    have h := curveDegree_tensorSheaf_eq_add k f hdim E M 2 1
    change curveDegree k f hdim (tensor E M) 2 =
      1 * curveDegree k f hdim E 2 + 2 * curveDegree k f hdim M 1 at h
    simpa only [one_mul] using h
  obtain ⟨a,ha⟩ := hdeg
  change curveDegree k f hdim E 2 = a + a at ha
  refine ⟨a + curveDegree k f hdim M 1, ?_⟩
  omega

end M9Native.MukaiLineDegree
