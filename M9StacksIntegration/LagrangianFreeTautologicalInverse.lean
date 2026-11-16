module

public import M9StacksIntegration.ChowTautologicalKernelInverse
public import M9StacksIntegration.ChowFreeBundleChern

/-!
# Actual free-bundle specializations of the tautological kernel recurrence

All trivializations here are isomorphisms of the original sheaves. The
actual inverse-Chern factorizations of their original kernels, including
arbitrary further scheme pullbacks, are consequences rather than inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern
universe u
namespace M9Native.LagrangianFreeTautologicalInverse
open GradedCapVirtualSchur

/-- The actual canonical free trivialization after an arbitrary scheme pullback. -/
def pullbackTrivialization {X T : Scheme.{u}} (g : T ⟶ X) (E : X.Modules) (r : ℕ)
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) :
    (Scheme.Modules.pullback g).obj E ≅
      SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin r)) :=
  (Scheme.Modules.pullback g).mapIso e ≪≫
    Scheme.Modules.pullbackFreeIso g (ULift.{u} (Fin r))

/-- Genuine split-row free Chern normalization gives actual inverse one. -/
theorem inverseFamily_eq_one_of_iso_free (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) :
    inverseFamily C q E r = 1 := by
  have h : inverseFamily C q E r * chernFamily C q E r = 1 := by
    simp only [inverseFamily, IsUnit.val_inv_mul]
  simpa only [ChowFreeBundleChern.chernFamily_eq_one_of_iso_free C q E r e,
    mul_one] using h

/-- Arbitrary pullback of the actual free-trivialized sheaf has actual inverse one. -/
theorem inverseFamily_pullback_eq_one_of_iso_free (C : ChowSituation.{u})
    {X T : Scheme.{u}} (qT : T ⟶ C.S) [LocallyOfFiniteType qT]
    (g : T ⟶ X) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r
    inverseFamily C qT ((Scheme.Modules.pullback g).obj E) r = 1 := by
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r
  exact inverseFamily_eq_one_of_iso_free C qT _ r (pullbackTrivialization g E r e)

section Kernel
variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u})

/-- The first original kernel of an actual free bundle has inverse
exactly the actual Chern family of its actual tautological quotient line. -/
theorem inverseFamily_kernel_of_iso_free
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n+1)))) :
    letI := hE.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    ∀ (q : bundle E ⟶ C.S) [LocallyOfFiniteType q],
      inverseFamily C q (kernel (bundleTautological E)) n =
        chernFamily C q (bundleTwist E) 1 := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
  intro q _
  have h := ChowTautologicalKernelInverse.inverseFamily_kernel E n C q
  rw [inverseFamily_pullback_eq_one_of_iso_free C q (bundleProj E) E (n+1) e,
    mul_one] at h
  exact h

/-- The same actual inverse identity on every further test scheme.
The pulled original exact row, and the actual pulled free trivialization,
are derived; neither flatness nor preservation of kernels is assumed. -/
theorem inverseFamily_pullback_kernel_of_iso_free
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n+1)))) :
    letI := hE.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    ∀ {T : Scheme.{u}} (g : T ⟶ bundle E) (qT : T ⟶ C.S) [LocallyOfFiniteType qT],
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
        (kernel (bundleTautological E)) n
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g (bundleTwist E) 1
      inverseFamily C qT ((Scheme.Modules.pullback g).obj (kernel (bundleTautological E))) n =
        chernFamily C qT ((Scheme.Modules.pullback g).obj (bundleTwist E)) 1 := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
  intro T g qT _
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
    (kernel (bundleTautological E)) n
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g (bundleTwist E) 1
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
    ((Scheme.Modules.pullback (bundleProj E)).obj E) (n+1)
  have h := ChowTautologicalKernelInverse.inverseFamily_pullback_kernel E n C g qT
  have hfree := inverseFamily_eq_one_of_iso_free C qT
    ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (bundleProj E)).obj E))
    (n+1) (pullbackTrivialization g _ (n+1)
      (pullbackTrivialization (bundleProj E) E (n+1) e))
  rw [hfree, mul_one] at h
  exact h

end Kernel
end M9Native.LagrangianFreeTautologicalInverse
