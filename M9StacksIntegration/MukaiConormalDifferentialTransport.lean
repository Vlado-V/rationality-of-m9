module

public import M9StacksIntegration.MukaiConormalEulerPullback
public import M9StacksIntegration.RelativeDifferentialsSpatialComposition

/-! The actual integral cotangent map is pinned to the original native
conormal differential by canonical differential composition. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiConormalDifferentialTransport

open Scheme.Hom LagrangianGrassmannian LagrangianPlucker
open MukaiConormalCotangentTransport MukaiConormalRank
open RelativeDifferentialsSpatialComposition

/-- Transport along equality of the actual structure morphisms retains
the canonical native differential map. -/
theorem relativeDifferentialsMap_target_eq {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ S) (q : X ⟶ S) (h : f ≫ p = q) :
    relativeDifferentialsMap f p (f ≫ p) (𝟙 S) (by simp) ≫
      eqToHom (congrArg relativeDifferentials h) =
        relativeDifferentialsMap f p q (𝟙 S) (by simpa using h) := by
  subst q
  simp only [eqToHom_refl, Category.comp_id]

variable (K : Type u) [Field K] [CharZero K]

theorem fieldSquare :
    primitivePlucker K ≫ fieldProjection 13 (Spec (.of K)) =
      projection K ≫ 𝟙 (Spec (.of K)) := by
  simpa only [Category.comp_id] using primitivePlucker_projection K

theorem integralSquare :
    integralPrimitivePlucker K ≫ integralProjection 13 =
      projection K ≫ specULiftZIsTerminal.from (Spec (.of K)) :=
  specULiftZIsTerminal.hom_ext _ _

def fieldDifferential :
    (Scheme.Modules.pullback (primitivePlucker K)).obj
      (relativeDifferentials (fieldProjection 13 (Spec (.of K)))) ⟶
        relativeDifferentials (projection K) :=
  relativeDifferentialsMap (primitivePlucker K)
    (fieldProjection 13 (Spec (.of K))) (projection K) (𝟙 _) (fieldSquare K)

def integralDifferential :
    (Scheme.Modules.pullback (integralPrimitivePlucker K)).obj
      (relativeDifferentials (integralProjection 13)) ⟶
        relativeDifferentials (projection K) :=
  relativeDifferentialsMap (integralPrimitivePlucker K)
    (integralProjection 13) (projection K)
    (specULiftZIsTerminal.from (Spec (.of K))) (integralSquare K)

theorem originalDifferential_eq :
    MukaiConormalSequence.differential K =
      relativeDifferentialsMap (LagrangianPluckerLinear.primitivePlucker K)
        (MukaiConormalSequence.ambientProjection K) (projection K)
        (𝟙 _) (by simpa only [Category.comp_id] using
          MukaiConormalSequence.primitivePlucker_projection K) := by
  exact relativeDifferentialsMap_target_eq _ _ _
    (MukaiConormalSequence.primitivePlucker_projection K)

theorem coordinateCotangent_hom :
    (ambientCoordinateCotangentIso K).hom =
      relativeDifferentialsMap (LagrangianPluckerLinear.primitiveProjectiveIso K).hom
        (MukaiConormalSequence.ambientProjection K)
        (fieldProjection 13 (Spec (.of K))) (𝟙 _)
        (by simpa only [Category.comp_id] using ambientCoordinateSquare K) := rfl

omit [CharZero K] in
theorem baseChangeCotangent_hom :
    (projectiveCotangentBaseChangeIso 13 (Spec (.of K))).hom =
      relativeDifferentialsMap (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))
        (integralProjection 13) (fieldProjection 13 (Spec (.of K)))
        (specULiftZIsTerminal.from (Spec (.of K)))
        (projectiveBaseChangeSquare 13 (Spec (.of K))).w := rfl

theorem coordinate_factor :
    (Scheme.Modules.pullbackComp (primitivePlucker K)
      (LagrangianPluckerLinear.primitiveProjectiveIso K).hom).inv.app
        (relativeDifferentials (MukaiConormalSequence.ambientProjection K)) ≫
      (Scheme.Modules.pullback (primitivePlucker K)).map (ambientCoordinateCotangentIso K).hom ≫
        fieldDifferential K = MukaiConormalSequence.differential K := by
  rw [originalDifferential_eq, coordinateCotangent_hom]
  have h := relativeDifferentialsMap_spatial_comp
    (primitivePlucker K) (LagrangianPluckerLinear.primitiveProjectiveIso K).hom
    (MukaiConormalSequence.ambientProjection K)
    (fieldProjection 13 (Spec (.of K))) (projection K) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using ambientCoordinateSquare K) (fieldSquare K)
    (by simpa only [Category.id_comp, Category.comp_id,
      LagrangianPluckerLinear.primitivePlucker] using
      MukaiConormalSequence.primitivePlucker_projection K)
  simpa only [Category.id_comp, fieldDifferential, Category.assoc,
    LagrangianPluckerLinear.primitivePlucker] using h

theorem integral_factor :
    (Scheme.Modules.pullbackComp (primitivePlucker K)
      (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))).hom.app
        (relativeDifferentials (integralProjection 13)) ≫
      (Scheme.Modules.pullbackCongr (primitivePlucker_toIntegral K)).hom.app
        (relativeDifferentials (integralProjection 13)) ≫ integralDifferential K =
      (Scheme.Modules.pullback (primitivePlucker K)).map
        (projectiveCotangentBaseChangeIso 13 (Spec (.of K))).hom ≫ fieldDifferential K := by
  rw [baseChangeCotangent_hom]
  have h := relativeDifferentialsMap_spatial_comp_hom
    (primitivePlucker K) (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))
    (integralPrimitivePlucker K) (primitivePlucker_toIntegral K)
    (integralProjection 13) (fieldProjection 13 (Spec (.of K))) (projection K)
    (specULiftZIsTerminal.from (Spec (.of K))) (𝟙 _)
    (projectiveBaseChangeSquare 13 (Spec (.of K))).w (fieldSquare K)
    (by simpa only [Category.id_comp] using integralSquare K)
  simpa only [Category.id_comp, integralDifferential, fieldDifferential] using h

/-- This is the literal original conormal differential, transported
through the actual coordinate and integral base-change isomorphisms. -/
theorem ambientIntegralIso_comp_integralDifferential :
    (ambientIntegralIso K).hom ≫ integralDifferential K =
      MukaiConormalSequence.differential K := by
  simp only [ambientIntegralIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [integral_factor K]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  exact coordinate_factor K

/-- The actual categorical conormal therefore kills the actual integral
pullback differential, with no first-jet or image equality assumed. -/
theorem conormalToIntegralCotangent_comp_integralDifferential :
    conormalToIntegralCotangent K ≫ integralDifferential K = 0 := by
  rw [MukaiConormalEulerPullback.conormalToIntegralCotangent_factor,
    Category.assoc, ambientIntegralIso_comp_integralDifferential]
  exact MukaiConormalSequence.inclusion_comp_differential K

end M9Native.MukaiConormalDifferentialTransport
