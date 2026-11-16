module

public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# Actual determinant and tensor rows of a named rank-three quotient flag

The actual flag rows are `0 → L2 → F2 → L1 → 0` and
`0 → L3 → Q → F2 → 0`.  Thus `L1` remains the first projective
quotient line.  The determinant isomorphisms come from the actual
native top-exterior comparison of short exact sequences; the tensor
row is the actual first row tensored with the actual invertible `L3`.
No K-zero or Chern identity is a flag hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.RankThreeFlagDeterminant

variable {X : Scheme.{u}} (L1 L2 L3 F2 Q : X.Modules)
  [hL1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L1 1]
  [hL2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L2 1]
  [hL3 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L3 1]
  [hF2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F2 2]
  [hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 3]
  (i21 : L2 ⟶ F2) (p21 : F2 ⟶ L1) (w21 : i21 ≫ p21 = 0)
  (h21 : (ShortComplex.mk i21 p21 w21).ShortExact)
  (i32 : L3 ⟶ Q) (p32 : Q ⟶ F2) (w32 : i32 ≫ p32 = 0)
  (h32 : (ShortComplex.mk i32 p32 w32).ShortExact)

/-- The actual rank-two top exterior line, in the order of the
first two actual projective quotient lines. -/
def rankTwoDetIso : topExterior F2 2 ≅ tensor L1 L2 :=
  (Scheme.Modules.exteriorPowerTensorExteriorPowerIso i21 p21 w21 h21 1 0).symm ≪≫
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf L2)
      (Scheme.Modules.exteriorPowerOneIsoSelf L1) ≪≫
    Scheme.Modules.tensorObjBraiding L2 L1

/-- The actual rank-three determinant line is the actual tensor
of the three named quotient lines, with their order retained. -/
def rankThreeDetIso : topExterior Q 3 ≅ tensor (tensor L1 L2) L3 :=
  (Scheme.Modules.exteriorPowerTensorExteriorPowerIso i32 p32 w32 h32 1 1).symm ≪≫
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf L3)
      (rankTwoDetIso L1 L2 F2 i21 p21 w21 h21) ≪≫
    Scheme.Modules.tensorObjBraiding L3 (tensor L1 L2)

include h21 in
/-- The literal first flag row remains short exact after tensoring
on the left by the actual third line. -/
theorem tensor21_shortExact :
    ∃ (a : tensor L3 L2 ⟶ tensor L3 F2) (b : tensor L3 F2 ⟶ tensor L3 L1)
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  have hInv : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L3 :=
    (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L3).mpr hL3
  let T : X.Modules ⥤ X.Modules := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L3
  letI : T.IsEquivalence :=
    Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L3
  let S := (ShortComplex.mk i21 p21 w21).map T
  have hS : S.ShortExact := h21.map_of_exact T
  exact ⟨S.f, S.g, S.zero, hS⟩

include h21 in
/-- The actual tensor flag row gives its actual K-zero relation. -/
theorem tensor21_class :
    VectorBundleKZero.classOf X (tensor L3 F2) =
      VectorBundleKZero.classOf X (tensor L3 L2) +
        VectorBundleKZero.classOf X (tensor L3 L1) := by
  obtain ⟨a, b, w, hs⟩ := tensor21_shortExact L1 L2 L3 F2 i21 p21 w21 h21
  letI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L1 := hL1.isFiniteLocallyFree
  letI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L2 := hL2.isFiniteLocallyFree
  letI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L3 := hL3.isFiniteLocallyFree
  letI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F2 := hF2.isFiniteLocallyFree
  have ht (A : X.Modules) (hA : SheafOfModules.IsFiniteLocallyFree.{u, u, u} A) :
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree (tensor L3 A) := by
    have hAs := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry A).mpr hA
    have hLs := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L3).mpr
      hL3.isFiniteLocallyFree
    exact @AlgebraicGeometry.isFiniteLocallyFree_tensorObj X L3 A hLs hAs
  exact @VectorBundleKZero.classOf_shortExact X _ _ _ a b hs.mono_f hs.epi_g w
    (ht L2 inferInstance) (ht F2 inferInstance) (ht L1 inferInstance) hs.exact

include h21 h32 in
/-- The named flag gives the sum of its named lines in genuine
bundle K-zero, with no assumed splitting isomorphism. -/
theorem rankThree_class :
    VectorBundleKZero.classOf X Q = VectorBundleKZero.classOf X L1 +
      VectorBundleKZero.classOf X L2 + VectorBundleKZero.classOf X L3 := by
  have h1 := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L1).mpr
    hL1.isFiniteLocallyFree
  have h2 := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L2).mpr
    hL2.isFiniteLocallyFree
  have h3 := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L3).mpr
    hL3.isFiniteLocallyFree
  have hf := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F2).mpr
    hF2.isFiniteLocallyFree
  have hq := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry Q).mpr
    hQ.isFiniteLocallyFree
  have e21 := @VectorBundleKZero.classOf_shortExact X L2 F2 L1 i21 p21
    h21.mono_f h21.epi_g w21 h2 hf h1 h21.exact
  have e32 := @VectorBundleKZero.classOf_shortExact X L3 Q F2 i32 p32
    h32.mono_f h32.epi_g w32 h3 hq hf h32.exact
  rw [e32, e21]
  abel

end M9Native.RankThreeFlagDeterminant
