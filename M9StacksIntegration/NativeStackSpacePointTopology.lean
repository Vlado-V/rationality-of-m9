/-
Selected faithful replay from AxiomMath/Stacks (Apache-2.0), commit
c496df0d9beea9deaeabcea8492605f9a0a2313b, of the initial three point-space
comparison declarations in Stacks/PointsAlgebraicSpaceStack.lean.
Only its already verified PointsTopology parents are used. The unrelated
open-substack declarations and their extra dependencies are not imported.
Exact source provenance is recorded in the owning audit journal.
-/
module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology

/-!
# The genuine algebraic-space and associated-stack point homeomorphism

The comparison is the actual native spacePointMap at the identity based
functor. The two point sets and their two native topologies are retained;
there is no model equality or assumed point-space comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Stack

namespace M9Native.NativeStackSpacePointTopology

universe u w
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The actual tautological point map is open for the native topologies. -/
theorem isOpenMap_spacePointMap_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    @IsOpenMap _ _ (Space.pointTopology B S hS F)
      (Stack.pointTopology B S hS (fibredCategory B S hS F))
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val)) := by
  intro V hV
  refine (isOpen_pointTopology_iff B S hS (fibredCategory B S hS F) _).2 fun c => ?_
  have hfac : spacePointMap B S hS c.1.1 (fibredCategory B S hS F) c.2 =
      spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val) ∘
      Space.pointsMap B S hS c.1.1 (presheafMapOfBasedFunctor c.2) := by
    funext p
    have hcomp := congrFun (spacePointMap_comp B S hS c.1.1 (fibredCategory B S hS c.1.1)
      (fibredCategory B S hS F) (BasedFunctor.id (fibredCategory B S hS c.1.1).val) c.2) p
    rw [BasedFunctor.id_comp] at hcomp
    rw [Function.comp_apply, spacePointMap_presheafMapOfBasedFunctor]
    exact hcomp
  rw [hfac, Set.preimage_comp,
    Set.preimage_image_eq V (spacePointMap_id_bijective B S hS F).injective]
  have hc := Space.continuous_pointsMap B S hS (presheafMapOfBasedFunctor c.2)
  rw [continuous_def] at hc
  exact hc V hV

/-- An actual algebraic space has the same genuine point topology as its
associated stack, through the actual tautological point map. -/
theorem isHomeomorph_spacePointMap_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    @IsHomeomorph _ _ (Space.pointTopology B S hS F)
      (Stack.pointTopology B S hS (fibredCategory B S hS F))
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val)) :=
  @IsHomeomorph.mk _ _ (Space.pointTopology B S hS F)
    (Stack.pointTopology B S hS (fibredCategory B S hS F)) _
    (continuous_spacePointMap B S hS F hF (fibredCategory B S hS F) _)
    (isOpenMap_spacePointMap_id B S hS F)
    (spacePointMap_id_bijective B S hS F)

/-- The actual point homeomorphism between an algebraic space and its
associated native stack, in either stack-object universe. -/
def pointsHomeomorphSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    letI := Space.pointTopology B S hS F
    letI := Stack.pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS F hF).val
    @Homeomorph (Space.points B S hS F)
      (Stack.points B S hS (algebraicSpaceStack.{u, w} B S hS F hF).val.val
        (algebraicSpaceStack.{u, w} B S hS F hF).val.property) _ _ :=
  letI := Space.pointTopology B S hS F
  letI := Stack.pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS F hF).val
  (isHomeomorph_spacePointMap_id B S hS F hF).homeomorph _

end M9Native.NativeStackSpacePointTopology
