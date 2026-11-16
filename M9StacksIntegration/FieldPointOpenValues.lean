module

public import M9StacksIntegration.FieldPointLocalDerivation
public import M9StacksIntegration.LagrangianFieldJetCoefficients

/-! The genuine lift of a field-valued point to an open subscheme and
the exact actual coefficient-value comparison. No point-factorization
or ring-comparison premise is supplied. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.FieldPointOpenValues

open SpecFieldStalkSections SpecFieldPullbackSections

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (p : Spec (.of K) ⟶ X) (U : X.Opens) (hp : p.base (point K) ∈ U)

include hp in
theorem range_subset_open : Set.range p.base ⊆ Set.range U.ι.base := by
  rintro x ⟨z,rfl⟩
  refine ⟨⟨p z, ?_⟩,rfl⟩
  simpa only [Subsingleton.elim z (point K)] using hp

/-- The actual original point factors canonically through the genuine open immersion. -/
def liftToOpen : Spec (.of K) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι p (range_subset_open K p U hp)

theorem liftToOpen_fac : liftToOpen K p U hp ≫ U.ι = p :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual open inclusion's local coefficient map is exactly the inverse of its native global ring comparison. -/
theorem inclusion_appLE_top :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE,Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- Original local point values agree with genuine global values on the actual open subscheme. -/
theorem valueOn_topIso (r : Γ(U.toScheme,⊤)) :
    FieldPointLocalDerivation.valueOnRingHom K p U hp (U.topIso.hom r) =
      LagrangianFieldJetCoefficients.pointValue K (liftToOpen K p U hp) r := by
  have h := Scheme.Hom.appLE_comp_appLE (liftToOpen K p U hp) U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (show ⊤ ≤ liftToOpen K p U hp ⁻¹ᵁ ⊤ by simp)
  have hq : (liftToOpen K p U hp).appLE ⊤ ⊤ (by simp) =
      (liftToOpen K p U hp).appTop := (liftToOpen K p U hp).appLE_eq_app
  rw [inclusion_appLE_top,hq] at h
  have congrLE (q₁ q₂ : Spec (.of K) ⟶ X) (hq : q₁ = q₂)
      (h₁ : ⊤ ≤ q₁ ⁻¹ᵁ U) (h₂ : ⊤ ≤ q₂ ⁻¹ᵁ U) :
      q₁.appLE U ⊤ h₁ = q₂.appLE U ⊤ h₂ := by
    subst q₂
    rfl
  have h' : U.topIso.inv ≫ (liftToOpen K p U hp).appTop =
      p.appLE U ⊤ (preimageTop K p U hp) :=
    h.trans (congrLE _ _ (liftToOpen_fac K p U hp) _ _)
  have hh : U.topIso.hom ≫ p.appLE U ⊤ (preimageTop K p U hp) =
      (liftToOpen K p U hp).appTop := by
    rw [← h']
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact congrArg (fun z => (Scheme.ΓSpecIso (.of K)).hom z)
    (ConcreteCategory.congr_hom hh r)

end M9Native.FieldPointOpenValues
