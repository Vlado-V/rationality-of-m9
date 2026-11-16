module

public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.CurveLineSubbundle
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant

/-!
# The actual degree of the dual of a bundle on a regular curve

The rank-one calculation uses the actual evaluation isomorphism. For
higher ranks the proved modification construction supplies an actual
invertible quotient; on a regular curve that modification is an
isomorphism. Dualizing its genuine kernel sequence and using native
degree additivity proves the negative-degree formula. No determinant or
dual-degree equality is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiDualDegree

variable {X : Scheme.{u}}

/-- The actual positive-length filtration has an actual invertible last
quotient. No quotient map is supplied to the theorem. -/
theorem exists_invertible_quotient_positive [IsIntegral X]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)) :
    ∃ L : X.Modules, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ∧
      ∃ q : E ⟶ L, Epi q := by
  obtain ⟨Y, π, hπ, hfil⟩ :=
    Stacks.ProjectiveBundleSplitting.exists_modification_hasInvertibleFiltration' (n+1) X E hE
  let : IsIso π := CurveLineSubbundle.isIso_modification_of_regular_dimension_le_one
    hreg hdim π hπ
  apply CurveLineSubbundle.exists_invertible_quotient_of_isIso_pullback π E
  cases hfil with
  | step i q w hS hL hF hsub => exact ⟨_, hL, q, hS.epi_g⟩

section Curve

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)

/-- The native tensor degree formula at the literal tensor spelling used
throughout the Mukai construction. -/
theorem curveDegree_tensor (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} V m] :
    @curveDegree k _ X f _ hdim (tensor E V) (n*m)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m) =
      (m : ℤ) * curveDegree k f hdim E n + (n : ℤ) * curveDegree k f hdim V m :=
  curveDegree_tensorSheaf_eq_add k f hdim E V n m

/-- Actual evaluation and actual tensor degree give the line-bundle case. -/
theorem curveDegree_dual_line (L : X.Modules)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1) :
    @curveDegree k _ X f _ hdim (dualSheaf L) 1
        (isFiniteLocallyFreeOfRank_dualSheaf L 1 hL) =
      -@curveDegree k _ X f _ hdim L 1 hL := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 := hL
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf L) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf L 1 hL
  have hInv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one X L).mpr hL
  let : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hInv
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (structureModule X) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor (dualSheaf L) L) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X (dualSheaf L) L 1 1
  let e : tensor (dualSheaf L) L ≅ structureModule X :=
    Stacks.SheafOfModules.Scheme.evaluationIso X L
  have hi := curveDegree_eq_of_iso k f hdim 1 e
  have hu : curveDegree k f hdim (structureModule X) 1 = 0 := by
    simp [curveDegree, structureModule]
  have ht := curveDegree_tensor k f hdim (dualSheaf L) L 1 1
  simp only [Nat.cast_one, one_mul] at ht
  linarith

/-- Actual vector-bundle duality negates the degree in every positive
rank on the original regular curve. -/
theorem curveDegree_dual_positive (hreg : IsRegular X) (n : ℕ) (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)) :
    @curveDegree k _ X f _ hdim (dualSheaf E) (n+1)
        (isFiniteLocallyFreeOfRank_dualSheaf E (n+1) hE) =
      -@curveDegree k _ X f _ hdim E (n+1) hE := by
  induction n generalizing E with
  | zero => exact curveDegree_dual_line k f hdim E hE
  | succ n ih =>
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+2) := hE
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf E) (n+2) :=
      isFiniteLocallyFreeOfRank_dualSheaf E (n+2) hE
    obtain ⟨L, hL, q, hq⟩ := exists_invertible_quotient_positive hreg hdim E (n+1) hE
    let : Epi q := hq
    let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
    let hLr := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 := hLr
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf L) 1 :=
      isFiniteLocallyFreeOfRank_dualSheaf L 1 hLr
    have hK : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) (n+1) :=
      Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
        q hq hL (n+1) hE
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) (n+1) := hK
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf (kernel q)) (n+1) :=
      isFiniteLocallyFreeOfRank_dualSheaf (kernel q) (n+1) hK
    have hS : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
      { exact := ShortComplex.exact_kernel q }
    obtain ⟨w, hd⟩ := exists_dualSheaf_shortExact (kernel.ι q) q (kernel.condition q)
      hS.mono_f hS.epi_g hS.exact
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hK.isFiniteLocallyFree)
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hE.isFiniteLocallyFree)
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hLr.isFiniteLocallyFree)
    have hdeg : curveDegree k f hdim E (n+2) =
        curveDegree k f hdim (kernel q) (n+1) + curveDegree k f hdim L 1 :=
      curveDegree_add_of_shortExact_of_isProper k f hdim
        (ShortComplex.mk (kernel.ι q) q (kernel.condition q)) hS (n+1) (n+2) 1
    have hddeg : curveDegree k f hdim (dualSheaf E) (n+2) =
        curveDegree k f hdim (dualSheaf L) 1 +
          curveDegree k f hdim (dualSheaf (kernel q)) (n+1) :=
      curveDegree_add_of_shortExact_of_isProper k f hdim
        (ShortComplex.mk (dualMap q) (dualMap (kernel.ι q)) w) hd 1 (n+2) (n+1)
    have hKL := ih (kernel q) hK
    have hLL := curveDegree_dual_line k f hdim L hLr
    linarith

end Curve

end M9Native.MukaiDualDegree
