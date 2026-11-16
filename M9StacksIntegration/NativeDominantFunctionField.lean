module

public import M9StacksIntegration.GrassmannianFunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Pullback on the actual generic stalks of integral schemes along an
actual dominant morphism, with the original scalar maps. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.NativeDominantFunctionField

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

theorem map_genericPoint (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ,f.denseRange.closure_range] at h
  exact ((genericPoint_spec Y).eq h).symm

/-- Pullback is the genuine stalk map, with its target point transported
along dominance's equality of generic points. -/
def map (f : X ⟶ Y) [IsDominant f] : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr
      (Inseparable.of_eq (map_genericPoint f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

theorem map_germ (f : X ⟶ Y) [IsDominant f] :
    Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) ≫ CommRingCat.ofHom (map f) =
      f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial) := by
  simp only [map,CommRingCat.ofHom_hom,← Category.assoc,TopCat.Presheaf.stalkCongr_hom]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap ⊤ (genericPoint X) (by trivial)

theorem map_scalar (K : Type u) [Field K] (f : X ⟶ Y) [IsDominant f]
    (p : Y ⟶ Spec (.of K)) :
    (map f).comp (GrassmannianCharts.structureScalarMap K p) =
      GrassmannianCharts.structureScalarMap K (f ≫ p) := by
  have h : p.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) ≫
      CommRingCat.ofHom (map f) =
      (f ≫ p).appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial) := by
    rw [map_germ]
    simp only [Scheme.Hom.comp_appTop,Category.assoc]
  exact congrArg (fun g => g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) h

theorem map_injective [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    Function.Injective (map f) := (map f).injective

variable {R S : Type u} [CommRing R] [CommRing S]

/-- An actual injective ring homomorphism gives a dominant affine morphism. -/
theorem specMap_isDominant (φ : R →+* S) (hφ : Function.Injective φ) :
    IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
  apply isDominant_of_of_appTop_injective
  have he : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of S)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of R)).inv).1
    simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).inv).injective.comp
    (hφ.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).injective)

end M9Native.NativeDominantFunctionField
