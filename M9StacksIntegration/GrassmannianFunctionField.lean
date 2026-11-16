module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.FractionRing

/-! Restriction of genuine generic stalks, with the actual base-field scalar map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.GrassmannianCharts

variable (K : Type u) [Field K]

instance affineFunctionField_ringAlgebra (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)

instance affineFunctionField_isFractionRing (R : Type u) [CommRing R] [IsDomain R] :
    IsFractionRing R (Spec (.of R)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (.of R)

/-- Constants enter an actual generic stalk through the scheme's structure morphism. -/
def structureScalarMap {X : Scheme.{u}} [IrreducibleSpace X] (p : X ⟶ Spec (.of K)) :
    K →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) (by trivial)).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

/-- Restricting to the dense chart is an isomorphism of the actual generic stalks. -/
def openImmersionFunctionFieldIso {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (i : Y ⟶ X) [IsOpenImmersion i] : X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion i).symm) ≪≫
    asIso (i.stalkMap (genericPoint Y))

theorem openImmersionFunctionFieldIso_germ {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (i : Y ⟶ X) [IsOpenImmersion i] :
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫ (openImmersionFunctionFieldIso i).hom =
      i.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
  simp only [openImmersionFunctionFieldIso,Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom,asIso_hom,← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact i.germ_stalkMap ⊤ (genericPoint Y) (by trivial)

theorem openImmersionFunctionFieldIso_scalar {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (i : Y ⟶ X) [IsOpenImmersion i] (p : X ⟶ Spec (.of K)) :
    (openImmersionFunctionFieldIso i).hom.hom.comp (structureScalarMap K p) =
      structureScalarMap K (i ≫ p) := by
  have h : p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫
      (openImmersionFunctionFieldIso i).hom =
      (i ≫ p).appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
    rw [openImmersionFunctionFieldIso_germ]
    simp only [Scheme.Hom.comp_appTop,Category.assoc]
  exact congrArg (fun g => g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) h

theorem affine_structureScalarMap (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] :
    structureScalarMap K (Spec.map (CommRingCat.ofHom (algebraMap K R))) =
      (algebraMap R (Spec (.of R)).functionField).comp (algebraMap K R) := by
  change (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap K R))).appTop) ≫
        (Spec (.of R)).presheaf.germ ⊤ (genericPoint (Spec (.of R))) (by trivial)).hom = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end M9Native.GrassmannianCharts
