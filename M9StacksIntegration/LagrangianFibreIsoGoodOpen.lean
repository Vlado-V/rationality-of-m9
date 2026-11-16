module

public import M9StacksIntegration.LagrangianGoodPointCriterion
public import M9StacksIntegration.LagrangianFibreFactorization
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth

/-!
# The original good parameter from a genuine original curve-fibre isomorphism

An actual isomorphism over the original field transports smoothness,
irreducibility and dimension one to the entire original incidence
fibre. The proved original good-point criterion therefore applies.
Neither membership in the good open nor geometry of the fibre is an
input. Both conventions for the original pullback are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace M9Native.LagrangianFibreIsoGoodOpen

open LagrangianLinearSections LagrangianFibreFactorization

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f]
  (p : Spec (.of K) ⟶ parameter K) (hp : p ≫ parameterProjection K = 𝟙 _)

include hp

/-- A true isomorphism to the entire conventional original fibre,
with its actual base triangle, proves original good-open membership. -/
theorem lands_goodOpen_of_iso
    (e : X ≅ pullback (familyProjection K) p)
    (he : e.hom ≫ pullback.snd (familyProjection K) p = f) :
    ∀ t : Spec (.of K), p t ∈ LagrangianLinearSectionGenericSmooth.goodOpen K := by
  let q := pullback.snd (familyProjection K) p
  have hi : e.inv ≫ f = q := by
    exact (congrArg (fun a => e.inv ≫ a) he.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ q) e.inv_hom_id).trans (Category.id_comp q)))
  letI : Smooth q := by rw [← hi]; infer_instance
  letI : IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K) p) :=
    (Scheme.homeoOfIso e).irreducibleSpace_iff.mp inferInstance
  have hd : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K) p) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq (Scheme.homeoOfIso e)
      (Scheme.homeoOfIso e).isHomeomorph).symm.trans
        (IsCurve.topologicalKrullDim_eq_one (f := f))
  exact LagrangianGoodPointCriterion.fieldPoint_lands_goodOpen K p hp hd

/-- The same conclusion for the literal reversed original fibre used
by the actual Mukai factorization. The pullback symmetry and base
triangle are actual categorical maps. -/
theorem lands_goodOpen_of_original_iso
    (e : X ≅ fibre K p) (he : e.hom ≫ pullback.fst p (familyProjection K) = f) :
    ∀ t : Spec (.of K), p t ∈ LagrangianLinearSectionGenericSmooth.goodOpen K := by
  apply lands_goodOpen_of_iso K f p hp
    (e ≪≫ pullbackSymmetry p (familyProjection K))
  simpa only [Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd] using he

end M9Native.LagrangianFibreIsoGoodOpen
