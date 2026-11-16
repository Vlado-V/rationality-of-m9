module

public import M9StacksIntegration.PoincareOrdinaryDegreeZero
public import M9StacksIntegration.PoincareFiniteFree

/-!
# Actual free direct images of original-field lines after base change

The original proper field-valued direct image has the proved derived
rank, so its ordinary degree-zero bundle is actually free. The genuine
cartesian base-change comparison and the actual supplied line
isomorphism transport that trivialization to the original ordinary
pushforward on the new base. No free trivialization or base-change
comparison is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace M9Native.FieldLineBaseChangeFree

/-- A proper morphism to an actual field spectrum is of finite presentation. -/
theorem finitePresentation_of_proper_to_field (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] :
    FinitePresentation f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

variable (k : Type u) [Field k] {C B Y : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsProper f]
    (A₀ : C.Modules)
    [hA₀ : Stacks.SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A₀]
    (r : ℕ) (hr : HasDerivedPushforwardRank f A₀ 0 r)
    (sB : B ⟶ Spec (.of k)) (π : Y ⟶ B) (u : Y ⟶ C)
    (hsq : IsPullback u π f sB) (A : Y.Modules)
    (eA : A ≅ (Scheme.Modules.pullback u).obj A₀)

/-- The displayed isomorphism uses the original push/pull functors,
the original base-change square, and the given actual line isomorphism. -/
def ordinaryPushforwardFreeIso :
    (Scheme.Modules.pushforward π).obj A ≅
      SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin r)) := by
  letI : Subsingleton (Spec (.of k)) := SpecField.subsingleton_carrier (Field.toIsField k)
  letI : Flat f := inferInstance
  letI : Stacks.Ample.IsInvertibleModule C A₀ :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hA₀
  let hfp := finitePresentation_of_proper_to_field k f
  let hM := PoincareChern.OrdinaryDegreeZero.ordinaryPushforward_rank_of_derivedRank f A₀ r hr
  let ebc := PoincareChern.OrdinaryDegreeZero.ordinaryPushforwardPullbackIso
    f hfp A₀ r hr sB π u hsq
  exact (Scheme.Modules.pushforward π).mapIso eA ≪≫ ebc.symm ≪≫
    (Scheme.Modules.pullback sB).mapIso
      (PoincareChern.specFieldIsoFiniteFreeOfRank k ((Scheme.Modules.pushforward f).obj A₀) r hM) ≪≫
    PoincareChern.pullbackFiniteFreeIso sB r

/-- The rank-nine endpoint used by the actual initial C9 direct image. -/
def ordinaryPushforwardFreeNineIso
    (h9 : HasDerivedPushforwardRank f A₀ 0 9) :
    (Scheme.Modules.pushforward π).obj A ≅
      SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin 9)) :=
  ordinaryPushforwardFreeIso k f A₀ 9 h9 sB π u hsq A eA

end M9Native.FieldLineBaseChangeFree
