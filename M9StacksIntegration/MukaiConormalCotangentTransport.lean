module

public import M9StacksIntegration.MukaiConormalSequence
public import M9StacksIntegration.LagrangianPluckerGeneration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow

/-!
# Actual cotangent transport to the integral Euler model

The conormal object remains the original categorical native I/I² of the
primitive embedding. Its canonical differential is transported through
the actual projective-coordinate isomorphism and the genuine projective
base-change square. This gives the intrinsic input for the Euler map on
the literal integral Proj model, without identifying unrelated twist
models or changing the conormal by an assumed isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.MukaiConormalCotangentTransport

abbrev integralProjection (n : ℕ) :
    projectiveSpaceAtUniverse.{u} n ⟶ Spec (.of (ULift.{u} ℤ)) :=
  projToSpecCoeff (ULift.{u} ℤ) n

abbrev fieldProjection (n : ℕ) (S : Scheme.{u}) : projectiveSpaceOver n S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))

/-- The ACTUAL terminal-base projective model is a base change over
the actual integral coefficient scheme. -/
theorem projectiveBaseChangeSquare (n : ℕ) (S : Scheme.{u}) :
    IsPullback (projectiveSpaceOver.toIntegralAtUniverse n S) (fieldProjection n S)
      (integralProjection n) (specULiftZIsTerminal.from S) := by
  let e : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  refine (IsPullback.of_hasPullback (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact specULiftZIsTerminal.hom_ext _ _
  · exact specULiftZIsTerminal.hom_ext _ _

def projectiveCotangentBaseChangeIso (n : ℕ) (S : Scheme.{u}) :
    (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
        (Scheme.Hom.relativeDifferentials (integralProjection n)) ≅
      Scheme.Hom.relativeDifferentials (fieldProjection n S) := by
  let h := projectiveBaseChangeSquare n S
  let m := Scheme.Hom.relativeDifferentialsMap (projectiveSpaceOver.toIntegralAtUniverse n S)
    (integralProjection n) (fieldProjection n S) (specULiftZIsTerminal.from S) h.w
  have : IsIso m := Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback _ _ _ _ h
  exact asIso m

variable (K : Type u) [Field K] [CharZero K]

theorem ambientCoordinateSquare :
    (LagrangianPluckerLinear.primitiveProjectiveIso K).hom ≫
      MukaiConormalSequence.ambientProjection K = fieldProjection 13 (Spec (.of K)) := by
  exact basisProjectiveSpaceIso_hom_comp_toSpec
    (LagrangianPluckerLinear.primitiveBasis14 K).dualBasis

def ambientCoordinateCotangentIso :
    (Scheme.Modules.pullback (LagrangianPluckerLinear.primitiveProjectiveIso K).hom).obj
        (Scheme.Hom.relativeDifferentials (MukaiConormalSequence.ambientProjection K)) ≅
      Scheme.Hom.relativeDifferentials (fieldProjection 13 (Spec (.of K))) := by
  let i := (LagrangianPluckerLinear.primitiveProjectiveIso K).hom
  let p := MukaiConormalSequence.ambientProjection K
  let q := fieldProjection 13 (Spec (.of K))
  have h : IsPullback i q p (𝟙 (Spec (.of K))) :=
    IsPullback.of_horiz_isIso ⟨by simpa using ambientCoordinateSquare K⟩
  let m := Scheme.Hom.relativeDifferentialsMap i p q (𝟙 _) h.w
  have : IsIso m := Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback _ _ _ _ h
  exact asIso m

/-- The original categorical conormal embeds into the actual ambient
cotangent sheaf over the original base field. -/
def conormalToFieldCotangent : MukaiConormalBundle.conormal K ⟶
    (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).obj
      (Scheme.Hom.relativeDifferentials (fieldProjection 13 (Spec (.of K)))) :=
  MukaiConormalSequence.inclusion K ≫
    ((Scheme.Modules.pullbackComp (LagrangianPlucker.primitivePlucker K)
      (LagrangianPluckerLinear.primitiveProjectiveIso K).hom).app
        (Scheme.Hom.relativeDifferentials (MukaiConormalSequence.ambientProjection K))).inv ≫
    (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).map
      (ambientCoordinateCotangentIso K).hom

/-- The original conormal differential, canonically read in the literal
integral Proj cotangent sheaf used by the native Euler sequence. -/
def conormalToIntegralCotangent : MukaiConormalBundle.conormal K ⟶
    (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).obj
      (Scheme.Hom.relativeDifferentials (integralProjection 13)) :=
  conormalToFieldCotangent K ≫
    (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).map
      (projectiveCotangentBaseChangeIso 13 (Spec (.of K))).inv ≫
    ((Scheme.Modules.pullbackComp (LagrangianPlucker.primitivePlucker K)
      (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))).app
        (Scheme.Hom.relativeDifferentials (integralProjection 13))).hom ≫
    ((Scheme.Modules.pullbackCongr (LagrangianPlucker.primitivePlucker_toIntegral K)).app
      (Scheme.Hom.relativeDifferentials (integralProjection 13))).hom

variable [IsAlgClosed K]

instance conormalToFieldCotangent_mono : Mono (conormalToFieldCotangent K) := by
  unfold conormalToFieldCotangent
  infer_instance

instance conormalToIntegralCotangent_mono : Mono (conormalToIntegralCotangent K) := by
  unfold conormalToIntegralCotangent
  infer_instance

end M9Native.MukaiConormalCotangentTransport
