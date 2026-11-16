module

public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth

/-! The original incidence fibres over the actual good open have relative
dimension one. This transports the already proved restricted-family
dimension statement through the actual original cartesian square. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.LagrangianGoodOpenFibreSmoothness
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
variable (K : Type u) [Field K] [CharZero K]

theorem preimage_comp_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1
      (((familyProjection K) ⁻¹ᵁ goodOpen K).ι ≫ familyProjection K) := by
  have h : SmoothOfRelativeDimension (1+0)
      (restrictedProjection K ≫ (goodOpen K).ι) :=
    smoothOfRelativeDimension_comp (n:=1) (m:=0) _ _
  simpa only [add_zero, restrictedProjection, morphismRestrict_ι] using h

theorem smoothOfRelativeDimension_of_isPullback {T F : Scheme.{u}}
    (p : T ⟶ parameter K) (hp : ∀ t : T, p t ∈ goodOpen K)
    (c : F ⟶ family K) (h : F ⟶ T)
    (sq : IsPullback c h (familyProjection K) p) : SmoothOfRelativeDimension 1 h := by
  have hrange : Set.range c ⊆ Set.range (((familyProjection K) ⁻¹ᵁ goodOpen K).ι) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x,rfl⟩
    change familyProjection K (c x) ∈ goodOpen K
    rw [← Scheme.Hom.comp_apply,sq.w,Scheme.Hom.comp_apply]
    exact hp _
  have hbig := (IsOpenImmersion.isPullback_lift_id c
    (((familyProjection K) ⁻¹ᵁ goodOpen K).ι) hrange).paste_vert sq
  rw [Category.id_comp] at hbig
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hbig
    (preimage_comp_smoothOfRelativeDimension K)

theorem baseChange_smoothOfRelativeDimension {T : Scheme.{u}}
    (p : T ⟶ parameter K) (hp : ∀ t : T, p t ∈ goodOpen K) :
    SmoothOfRelativeDimension 1 (pullback.snd (familyProjection K) p) :=
  smoothOfRelativeDimension_of_isPullback K p hp _ _ (IsPullback.of_hasPullback _ _)

theorem fieldPoint_fibre_smoothOfRelativeDimension (L : Type u) [Field L]
    (p : Spec (.of L) ⟶ parameter K)
    (hp : p (IsLocalRing.closedPoint L) ∈ goodOpen K) :
    SmoothOfRelativeDimension 1 (pullback.snd (familyProjection K) p) := by
  apply baseChange_smoothOfRelativeDimension K p
  intro t
  simpa only [Subsingleton.elim t (IsLocalRing.closedPoint L)] using hp

end M9Native.LagrangianGoodOpenFibreSmoothness
end
