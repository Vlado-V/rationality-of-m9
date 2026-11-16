module

public import StacksFrontier.Deformation.Schlessinger.VersalBijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# The actual hull differential as a canonical linear equivalence

The native point-naturality map compares the transported represented tangent
module with the canonical tangent module of the original deformation
category. Actual bijectivity of the hull differential upgrades this very
map, retaining its coefficients and its actual class function.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory Deformation

universe u uF vF

namespace M9Native.HullTangentComparison

variable {k : Type u} [Field k] {F : Type uF} [Category.{vF} F]
  (𝓕 : BasedCategory.{vF,uF} (ArtinianLocalAlgCat.{u,u,u} k k))
  (hp : IsPredeformationCategory 𝓕.p)
  (hS2 : SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered)))

/-- The native actual hull differential, with its canonical target scalars. -/
def tangentLinearEquiv (ξ : FormalObject 𝓕.p)
    (hξ : HasBijectiveDifferential hp.cofibered ξ) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
    tangentSpaceArtinian k k (restrictedCoyoneda ξ.base) ≃ₗ[k]
      tangentSpaceArtinian k k (isomorphismClasses 𝓕 hp.cofibered) := by
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  let L := associatedTangentSpaceModuleStructure 𝓕 hp hS2
  let P := hξ.choose
  have hP := hξ.choose_spec
  let A := linearMapOfPointNaturality ξ.base L.functor
    (pointToModule hp.cofibered ξ P L) (pointToModule_naturality hp.cofibered ξ P L)
  let E := tangentSpaceDerivationsLinearEquiv ξ.base
  let V := FGModuleCat.of k (ULift.{u} k)
  have hinj : Function.Injective A := by
    intro a b hab
    apply E.injective
    apply hP.1
    rw [derivationToTangent_eq_pointClass,derivationToTangent_eq_pointClass,
      LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    change (eqToHom L.forget_comp.symm).app V
      (pointClass hp.cofibered ξ P _ a) =
        (eqToHom L.forget_comp.symm).app V
          (pointClass hp.cofibered ξ P _ b) at hab
    have hh := congrArg ((eqToHom L.forget_comp).app V) hab
    change ((eqToHom L.forget_comp.symm ≫ eqToHom L.forget_comp).app V)
      (pointClass hp.cofibered ξ P _ a) =
        ((eqToHom L.forget_comp.symm ≫ eqToHom L.forget_comp).app V)
          (pointClass hp.cofibered ξ P _ b) at hh
    simpa only [eqToHom_trans,eqToHom_refl,NatTrans.id_app,types_id_apply] using hh
  have hsurj : Function.Surjective A := by
    intro y
    let z := (eqToHom L.forget_comp).app V y
    obtain ⟨d,hd⟩ := hP.2 z
    have hpoint : derivationToTangent hp.cofibered ξ P d =
        pointClass hp.cofibered ξ P _ (E.symm d) :=
      derivationToTangent_eq_pointClass hp.cofibered ξ P d
    refine ⟨E.symm d,?_⟩
    change (eqToHom L.forget_comp.symm).app V
      (pointClass hp.cofibered ξ P _ (E.symm d)) = y
    rw [←hpoint,hd]
    change ((eqToHom L.forget_comp ≫ eqToHom L.forget_comp.symm).app V) y = y
    simp only [eqToHom_trans,eqToHom_refl,NatTrans.id_app,types_id_apply]
  exact (LinearEquiv.ofBijective A ⟨hinj,hsurj⟩).trans
    (associatedTangentSpaceCarrierLinearEquiv 𝓕 hp hS2)

end M9Native.HullTangentComparison
