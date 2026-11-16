module

public import M9StacksIntegration.RankThreeFlagDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerLineSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank

/-!
# The actual exterior-square filtration of the named quotient flag

The native stalkwise exterior-power theorem applies to the actual
rank-one submodule `L3` in `0 → L3 → Q → F2 → 0`.  Transport only
the degree-one exterior powers and the actual determinant of `F2`.
This gives `0 → L3 ⊗ F2 → Λ²Q → L1 ⊗ L2 → 0`.
The first flag row tensored by `L3` then provides its genuine
three-line filtration and its actual bundle K-zero identity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundleDeterminant
open Stacks.SheafOfModules.TopWedge

universe u

namespace M9Native.RankThreeFlagExterior

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

include h21 h32 in
/-- The actual exterior-square row, with its actual named end bundles. -/
theorem exteriorSquare_shortExact :
    ∃ (a : tensor L3 F2 ⟶ topExterior Q 2)
      (b : topExterior Q 2 ⟶ tensor L1 L2) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  let A3 := _root_.SheafOfModules.algebras _ L3
  let AQ := _root_.SheafOfModules.algebras _ Q
  let A2 := _root_.SheafOfModules.algebras _ F2
  let a0 : tensor (topExterior L3 1) (topExterior F2 1) ⟶ topExterior Q 2 :=
    @lineComparison _ X.sheaf L3 Q F2 A3 AQ A2 i32 p32 w32 h32.exact
      h32.epi_g hL3 0
  let b0 : topExterior Q 2 ⟶ topExterior F2 2 :=
    (extHom AQ A2 p32).app 2
  have w0 : a0 ≫ b0 = 0 :=
    @lineComparison_comp_extHom _ X.sheaf L3 Q F2 A3 AQ A2 i32 p32 w32 h32.exact
      h32.mono_f h32.epi_g hL3 2 hF2 0
  let S : ShortComplex X.Modules := ShortComplex.mk a0 b0 w0
  have hS : S.ShortExact :=
    @shortExact_lineComparison _ X.sheaf L3 Q F2 A3 AQ A2 i32 p32 w32 h32.exact
      h32.mono_f h32.epi_g hL3 2 hF2 0
  let e1 : S.X₁ ≅ tensor L3 F2 :=
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf L3)
      (Scheme.Modules.exteriorPowerOneIsoSelf F2)
  let e2 : S.X₂ ≅ topExterior Q 2 := Iso.refl _
  let e3 : S.X₃ ≅ tensor L1 L2 :=
    RankThreeFlagDeterminant.rankTwoDetIso L1 L2 F2 i21 p21 w21 h21
  let a := e1.inv ≫ S.f ≫ e2.hom
  let b := e2.inv ≫ S.g ≫ e3.hom
  have w : a ≫ b = 0 := by
    simp only [a, b, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc S.f S.g e3.hom, S.zero, zero_comp, comp_zero]
  refine ⟨a, b, w, ShortComplex.shortExact_of_iso ?_ hS⟩
  exact ShortComplex.isoMk e1 e2 e3
    (by simp [a, Category.assoc]) (by simp [b, Category.assoc])

include h21 h32 in
/-- Its actual K-zero class is the sum of the actual pairwise
tensor products of the three named quotient lines. -/
theorem exteriorSquare_class :
    VectorBundleKZero.classOf X (topExterior Q 2) =
      VectorBundleKZero.classOf X (tensor L1 L2) +
        VectorBundleKZero.classOf X (tensor L1 L3) +
          VectorBundleKZero.classOf X (tensor L2 L3) := by
  obtain ⟨a, b, w, hs⟩ := exteriorSquare_shortExact
    L1 L2 L3 F2 Q i21 p21 w21 h21 i32 p32 w32 h32
  have ht (A B : X.Modules) (hA : SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
      (hB : SheafOfModules.IsFiniteLocallyFree.{u, u, u} B) :
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree (tensor A B) :=
    @AlgebraicGeometry.isFiniteLocallyFree_tensorObj X A B
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry A).mpr hA)
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry B).mpr hB)
  have hWrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (topExterior Q 2) 3 := by
    have hc : Nat.choose 3 2 = 3 := by decide
    simpa only [topExterior, hc] using
      Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower Q 3 2
  have hW := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry
    (topExterior Q 2)).mpr hWrank.isFiniteLocallyFree
  have hrow := @VectorBundleKZero.classOf_shortExact X _ _ _ a b hs.mono_f hs.epi_g w
    (ht L3 F2 hL3.isFiniteLocallyFree hF2.isFiniteLocallyFree) hW
    (ht L1 L2 hL1.isFiniteLocallyFree hL2.isFiniteLocallyFree) hs.exact
  have h31 : VectorBundleKZero.classOf X (tensor L3 L1) =
      VectorBundleKZero.classOf X (tensor L1 L3) := VectorBundleKZero.classOf_eq_of_iso
    (Scheme.Modules.tensorObjBraiding L3 L1)
    (ht L3 L1 hL3.isFiniteLocallyFree hL1.isFiniteLocallyFree)
  have h32' : VectorBundleKZero.classOf X (tensor L3 L2) =
      VectorBundleKZero.classOf X (tensor L2 L3) := VectorBundleKZero.classOf_eq_of_iso
    (Scheme.Modules.tensorObjBraiding L3 L2)
    (ht L3 L2 hL3.isFiniteLocallyFree hL2.isFiniteLocallyFree)
  rw [hrow, RankThreeFlagDeterminant.tensor21_class L1 L2 L3 F2 i21 p21 w21 h21,
    h31, h32']
  abel

end M9Native.RankThreeFlagExterior
