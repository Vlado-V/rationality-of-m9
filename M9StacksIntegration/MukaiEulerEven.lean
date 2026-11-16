module

public import M9StacksIntegration.MukaiNormalizedFiltration
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension

/-!
# The genuine Euler parity in Mukai's normalized line filtration

Native tensor degree gives `deg(E tensor L) = deg E + 2 deg L`.
The native Euler-degree identity therefore proves even Euler
characteristic when the original rank-two bundle has even degree.
Native vanishing above curve dimension converts this to the actual
H0-minus-H1 expression. The normalized coefficient is transported back
to `E tensor L` by the already proved genuine tensor isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.MukaiEulerEven

open M9Native.MukaiHomCoefficient M9Native.MukaiNormalizedFiltration

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : Scheme.{u}}

/-- Tensoring the genuine rank-two bundle by the actual invertible
line preserves its actual rank. -/
theorem rankTwoTensorLine_rank (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor E L) 2 := by
  let := hE
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E L 2 1

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f]

include k f in
/-- The actual tensor bundle is coherent on the original curve. -/
theorem rankTwoTensorLine_coherent (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    (tensor E L).IsCoherent := by
  let := rankTwoTensorLine_rank E hE L
  exact SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f (tensor E L) 2

variable [IsProper f]

/-- Properness supplies actual finite-dimensional cohomology for the
genuine tensor bundle in every degree. -/
theorem finite_cohomology_tensor_line (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (n : ℕ) :
    Module.Finite k (cohomologyOverField k f (tensor E L) n) := by
  let := rankTwoTensorLine_coherent k f E hE L
  exact finiteDimensional_cohomologyOverField_of_isProper k f (tensor E L) n

/-- Euler parity follows from native tensor degree and the original
even degree; no cohomology parity is supplied as a premise. -/
theorem even_euler_tensor_line (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hdeg : letI := hE
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2)) :
    letI := rankTwoTensorLine_coherent k f E hE L
    Even (eulerCharacteristic k f (tensor E L)) := by
  let := hE
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  let := rankTwoTensorLine_rank E hE L
  let := rankTwoTensorLine_coherent k f E hE L
  let := SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  let : (_root_.SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  let hdim := (IsCurve.topologicalKrullDim_eq_one f).le
  have hd : curveDegree k f hdim (tensor E L) 2 =
      curveDegree k f hdim E 2 + 2 * curveDegree k f hdim L 1 := by
    have h := curveDegree_tensorSheaf_eq_add k f hdim E L 2 1
    change curveDegree k f hdim (tensor E L) 2 =
      1 * curveDegree k f hdim E 2 + 2 * curveDegree k f hdim L 1 at h
    simpa only [one_mul] using h
  have hc : curveDegree k f hdim (tensor E L) 2 =
      eulerCharacteristic k f (tensor E L) -
        2 * eulerCharacteristic k f (_root_.SheafOfModules.unit X.ringCatSheaf) :=
    curveDegree_eq_eulerCharacteristic_sub k f hdim (tensor E L) 2
  obtain ⟨a,ha⟩ := hdeg
  change curveDegree k f hdim E 2 = a + a at ha
  refine ⟨a + curveDegree k f hdim L 1 +
    eulerCharacteristic k f (_root_.SheafOfModules.unit X.ringCatSheaf), ?_⟩
  omega

/-- Actual native vanishing above curve dimension converts that Euler
parity to the original H0-minus-H1 dimensions. -/
theorem even_H0_sub_H1_tensor_line (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hdeg : letI := hE
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2)) :
    Even ((Module.finrank k (cohomologyOverField k f (tensor E L) 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k f (tensor E L) 1) : ℤ)) := by
  let := rankTwoTensorLine_coherent k f E hE L
  have h := even_euler_tensor_line k f E hE L hdeg
  rw [eulerCharacteristic_eq_sub_of_isZero k f (tensor E L) (fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f (tensor E L)
      (d := 1) (i := m) (IsCurve.topologicalKrullDim_eq_one f).le hm)] at h
  exact h

/-- The actual normalized coefficient has the same Euler parity,
transported by its genuine isomorphism to the original tensor bundle. -/
theorem even_H0_sub_H1_normalized_coefficient (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2) (L M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (hdeg : letI := hE
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2)) :
    Even ((Module.finrank k (cohomologyOverField k f
      (tensor (tensor L (inverseLine M)) (tensor E M)) 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k f
        (tensor (tensor L (inverseLine M)) (tensor E M)) 1) : ℤ)) := by
  rw [finrank_cohomologyOverField_eq_of_iso k f (normalizedTensorMiddleIso E L M) 0,
    finrank_cohomologyOverField_eq_of_iso k f (normalizedTensorMiddleIso E L M) 1]
  exact even_H0_sub_H1_tensor_line k f E hE L hdeg

end M9Native.MukaiEulerEven
