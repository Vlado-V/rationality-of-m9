module

public import M9StacksIntegration.LagrangianFamilyOrbitIsomorphism
public import M9StacksIntegration.ProperSmoothLocusBaseChange
public import M9StacksIntegration.PrimitiveGenericOpenPoints

@[expose] public section

/-! The actual proper smooth good open is preserved by the genuine raw
universal-family automorphism. The proved coordinateChange conjugation
therefore restricts the ORIGINAL native constant Sp6 action to its exact
coordinate good open. No open-preservation or action-identification premise
is supplied, and arbitrary original test schemes are retained. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianGoodOpenConstantAction
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianParameterCoordinates LagrangianRawFamilyAction
open LagrangianFamilyOrbitIsomorphism PrimitiveGenericOpenPoints

instance coordinateGoodOpen_nonempty_instance : Nonempty coordinateGoodOpen := by
  obtain ⟨x,hx⟩ := LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen_nonempty
  exact ⟨⟨x,hx⟩⟩

/-- The actual raw family automorphism preserves the actual largest
proper smooth parameter open, by flat base-change of the smooth locus. -/
theorem raw_goodOpen_eq_preimage (g : LagrangianParameterCoordinates.Sp6) :
    goodOpen ℂ = rawAction g ⁻¹ᵁ goodOpen ℂ := by
  have sq : IsPullback (familyAction g) (familyProjection ℂ)
      (familyProjection ℂ) (rawAction g) :=
    IsPullback.of_horiz_isIso ⟨familyAction_projection g⟩
  exact ProperSmoothLocusBaseChange.goodOpen_eq_preimage sq (Or.inr inferInstance)

private theorem preimage_eq_of_commuting_square {X Y : Scheme}
    (c : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (U : Y.Opens)
    (hc : a ≫ c = c ≫ b) (hU : U = b ⁻¹ᵁ U) :
    c ⁻¹ᵁ U = a ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  ext x
  change c x ∈ U ↔ c (a x) ∈ U
  have hcx := congrArg (fun f : X ⟶ Y => f x) hc
  simp only [Scheme.Hom.comp_apply] at hcx
  rw [hcx]
  change c x ∈ U ↔ c x ∈ b ⁻¹ᵁ U
  rw [← hU]

/-- Preservation concerns the true coordinate-shifted domain and the
ORIGINAL native action; the actual C-conjugation is retained. -/
theorem coordinateGoodOpen_eq_preimage (h : PrimitiveConstantFieldAction.Sp6) :
    coordinateGoodOpen = PrimitiveConstantFieldAction.schemeMap h ⁻¹ᵁ coordinateGoodOpen :=
  preimage_eq_of_commuting_square coordinateChange.hom
    (PrimitiveConstantFieldAction.schemeMap h)
    (rawAction (PrimitiveRingFieldBridge.fromOriginal h)) (goodOpen ℂ)
    (schemeMap_coordinateChange h)
    (raw_goodOpen_eq_preimage (PrimitiveRingFieldBridge.fromOriginal h))

/-- Restriction of the actual original constant action to its genuine
invariant coordinate good open. -/
def coordinateAction (h : PrimitiveConstantFieldAction.Sp6) :
    coordinateGoodOpen.toScheme ⟶ coordinateGoodOpen.toScheme :=
  OpenRestrictionPointFiber.lift coordinateGoodOpen
    (coordinateGoodOpen.ι ≫ PrimitiveConstantFieldAction.schemeMap h) (by
      intro t
      have ht : coordinateGoodOpen.ι t ∈ coordinateGoodOpen := t.property
      have hm := (coordinateGoodOpen_eq_preimage h).le ht
      change PrimitiveConstantFieldAction.schemeMap h (coordinateGoodOpen.ι t) ∈
        coordinateGoodOpen at hm
      simpa only [Scheme.Hom.comp_apply] using hm)

@[reassoc] theorem coordinateAction_comp (h : PrimitiveConstantFieldAction.Sp6) :
    coordinateAction h ≫ coordinateGoodOpen.ι =
      coordinateGoodOpen.ι ≫ PrimitiveConstantFieldAction.schemeMap h :=
  OpenRestrictionPointFiber.lift_comp _ _ _

/-- The actual restricted action retains the original complex base. -/
theorem coordinateAction_projection (h : PrimitiveConstantFieldAction.Sp6) :
    coordinateAction h ≫ (coordinateGoodOpen.ι ≫ PrimitiveGrassmannianAction.projection) =
      coordinateGoodOpen.ι ≫ PrimitiveGrassmannianAction.projection := by
  rw [← Category.assoc, coordinateAction_comp, Category.assoc,
    PrimitiveConstantFieldAction.schemeMap_projection]

/-- The actual original action in the exact Over category used by the
frozen native invariant-field criterion. -/
def overAction (h : PrimitiveConstantFieldAction.Sp6) :
    openOver coordinateGoodOpen ⟶ openOver coordinateGoodOpen :=
  Over.homMk (coordinateAction h) (coordinateAction_projection h)

@[reassoc] theorem overAction_comp (h : PrimitiveConstantFieldAction.Sp6) :
    overAction h ≫ inclusionOver coordinateGoodOpen =
      inclusionOver coordinateGoodOpen ≫ PrimitiveConstantFieldAction.overMap h := by
  apply Over.OverMorphism.ext
  exact coordinateAction_comp h

/-- On EVERY original test, the ambient native action relation uniquely
identifies the acted good-open point. No site containment is needed. -/
theorem eq_overAction_of_relation (T : Over PrimitiveFamilyFreeAction.base)
    (x y : T ⟶ openOver coordinateGoodOpen) (h : PrimitiveConstantFieldAction.Sp6)
    (hxy : x ≫ inclusionOver coordinateGoodOpen ≫ PrimitiveConstantFieldAction.overMap h =
      y ≫ inclusionOver coordinateGoodOpen) : x ≫ overAction h = y := by
  have hleft : x.left ≫ (coordinateGoodOpen.ι ≫ PrimitiveConstantFieldAction.schemeMap h) =
      y.left ≫ coordinateGoodOpen.ι :=
    congrArg (fun z => z.left) hxy
  apply Over.OverMorphism.ext
  apply (cancel_mono coordinateGoodOpen.ι).mp
  change (x.left ≫ coordinateAction h) ≫ coordinateGoodOpen.ι =
    y.left ≫ coordinateGoodOpen.ι
  simpa only [Category.assoc, coordinateAction_comp] using hleft

end M9Native.LagrangianGoodOpenConstantAction
