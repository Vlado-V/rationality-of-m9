module

public import M9StacksIntegration.ChowWhitneyKernelInverse
public import StacksFrontier.AlgebraicGeometry.FlagTower.Tower

/-!
# Genuine inverse-Chern recurrence for original tautological kernels

The actual kernel, original quotient map, actual tautological line, and
all arbitrary pullbacks of their true exact row are retained. All ranks
and exactness are derived from the original finite locally free bundle.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern

universe u
namespace M9Native.ChowTautologicalKernelInverse
open GradedCapVirtualSchur

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (C : ChowSituation.{u})

/-- The exact original tautological kernel, not a row supplied as an
assumption, has the genuine inverse-Chern factorization. Every displayed
local instance is derived from the original rank hypothesis. -/
theorem inverseFamily_kernel :
    letI := hE.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
    ∀ (q : bundle E ⟶ C.S) [LocallyOfFiniteType q],
      inverseFamily C q (kernel (bundleTautological E)) n =
        chernFamily C q (bundleTwist E) 1 *
          inverseFamily C q ((Scheme.Modules.pullback (bundleProj E)).obj E) (n+1) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
  intro q _
  exact ChowWhitneyKernelInverse.inverseFamily_kernel_of_shortExact C q
    (ShortComplex.mk (kernel.ι (bundleTautological E)) (bundleTautological E)
      (kernel.condition _)) (Stacks.Chow.shortExact_bundleTautological E) n

/-- The actual signed factorization used by genuine projective moments. -/
theorem signScale_inverseFamily_kernel :
    letI := hE.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
    ∀ (q : bundle E ⟶ C.S) [LocallyOfFiniteType q],
      capFamilySignScale (inverseFamily C q (kernel (bundleTautological E)) n) =
        capFamilySignScale (chernFamily C q (bundleTwist E) 1) *
          capFamilySignScale
            (inverseFamily C q ((Scheme.Modules.pullback (bundleProj E)).obj E) (n+1)) := by
  letI := hE.isFiniteLocallyFree
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
  letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
  intro q _
  simpa only [capFamilySignScale_mul] using
    congrArg capFamilySignScale (inverseFamily_kernel E n C q)

/-- Along every actual test morphism, the original exact row remains
exact because its genuine quotient is locally free. No flatness or
kernel-preservation premise is needed. -/
theorem inverseFamily_pullback_kernel :
    letI := hE.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
    ∀ {T : Scheme.{u}} (g : T ⟶ bundle E) (qT : T ⟶ C.S) [LocallyOfFiniteType qT],
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
        (kernel (bundleTautological E)) n
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g (bundleTwist E) 1
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
        ((Scheme.Modules.pullback (bundleProj E)).obj E) (n+1)
      inverseFamily C qT ((Scheme.Modules.pullback g).obj (kernel (bundleTautological E))) n =
        chernFamily C qT ((Scheme.Modules.pullback g).obj (bundleTwist E)) 1 *
          inverseFamily C qT ((Scheme.Modules.pullback g).obj
            ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n+1) := by
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
  let S : ShortComplex T.Modules :=
    (ShortComplex.mk (kernel.ι (bundleTautological E)) (bundleTautological E)
      (kernel.condition _)).map (Scheme.Modules.pullback g)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ n := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback g).obj (kernel (bundleTautological E))) n
    infer_instance
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback g).obj (bundleTwist E)) 1
    infer_instance
  exact ChowWhitneyKernelInverse.inverseFamily_kernel_of_shortExact C qT S
    (Stacks.FlagTower.shortExact_pullback_kernel_bundleTautological E g) n

/-- The same all-test genuine pulled-kernel factorization with the
actual native degree-sign operator. -/
theorem signScale_inverseFamily_pullback_kernel :
    letI := hE.isFiniteLocallyFree
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological E n hE
    letI := Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) E (n+1)
    ∀ {T : Scheme.{u}} (g : T ⟶ bundle E) (qT : T ⟶ C.S) [LocallyOfFiniteType qT],
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
        (kernel (bundleTautological E)) n
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g (bundleTwist E) 1
      letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g
        ((Scheme.Modules.pullback (bundleProj E)).obj E) (n+1)
      capFamilySignScale (inverseFamily C qT
        ((Scheme.Modules.pullback g).obj (kernel (bundleTautological E))) n) =
        capFamilySignScale (chernFamily C qT
          ((Scheme.Modules.pullback g).obj (bundleTwist E)) 1) *
          capFamilySignScale (inverseFamily C qT ((Scheme.Modules.pullback g).obj
            ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n+1)) := by
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
  simpa only [capFamilySignScale_mul] using
    congrArg capFamilySignScale (inverseFamily_pullback_kernel E n C g qT)

end M9Native.ChowTautologicalKernelInverse
