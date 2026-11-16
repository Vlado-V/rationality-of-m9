module

public import M9StacksIntegration.NativeDominantFunctionField

/-! Functoriality and coefficient formulas for genuine dominant
generic-stalk pullbacks. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.NativeFunctionFieldFunctor

open M9Native.NativeDominantFunctionField

variable {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

abbrev genericSpec (X : Scheme.{u}) [IrreducibleSpace X] : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

instance genericSpec_isDominant (X : Scheme.{u}) [IrreducibleSpace X] :
    IsDominant (genericSpec X) where
  denseRange := by
    intro x
    have hx : x ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]
      trivial
    apply closure_mono (Set.singleton_subset_iff.mpr ?_) hx
    exact ⟨IsLocalRing.closedPoint X.functionField,Scheme.fromSpecStalk_closedPoint⟩

theorem map_square (f : X ⟶ Y) [IsDominant f] :
    Spec.map (CommRingCat.ofHom (map f)) ≫ genericSpec Y = genericSpec X ≫ f := by
  change Spec.map ((Y.presheaf.stalkCongr
      (Inseparable.of_eq (map_genericPoint f).symm)).hom ≫ f.stalkMap (genericPoint X)) ≫ _ = _
  rw [Spec.map_comp,Category.assoc,TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    map (f ≫ g) = (map f).comp (map g) := by
  have h : CommRingCat.ofHom (map (f ≫ g)) =
      CommRingCat.ofHom ((map f).comp (map g)) := by
    apply Spec.map_injective
    apply (cancel_mono (genericSpec Z)).mp
    rw [map_square,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,map_square]
    simp only [← Category.assoc,map_square]
  exact congrArg CommRingCat.Hom.hom h

theorem map_id : map (𝟙 X) = RingHom.id X.functionField := by
  have h : CommRingCat.ofHom (map (𝟙 X)) = 𝟙 (CommRingCat.of X.functionField) := by
    apply Spec.map_injective
    apply (cancel_mono (genericSpec X)).mp
    rw [map_square,Spec.map_id]
    simp only [Category.comp_id,Category.id_comp]
  exact congrArg CommRingCat.Hom.hom h

theorem affine_map_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (φ : R →+* S)
    [IsDominant (Spec.map (CommRingCat.ofHom φ))] (r : R) :
    map (Spec.map (CommRingCat.ofHom φ)) (algebraMap R (Spec (.of R)).functionField r) =
      algebraMap S (Spec (.of S)).functionField (φ r) := by
  have h : (Scheme.ΓSpecIso (.of R)).inv ≫
      (Spec (.of R)).presheaf.germ ⊤ (genericPoint (Spec (.of R))) (by trivial) ≫
      CommRingCat.ofHom (map (Spec.map (CommRingCat.ofHom φ))) =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
        (Spec (.of S)).presheaf.germ ⊤ (genericPoint (Spec (.of S))) (by trivial) := by
    rw [NativeDominantFunctionField.map_germ,← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality,Category.assoc]
  exact congrArg (fun f : CommRingCat.of R ⟶ (Spec (.of S)).functionField => f r) h

end M9Native.NativeFunctionFieldFunctor
