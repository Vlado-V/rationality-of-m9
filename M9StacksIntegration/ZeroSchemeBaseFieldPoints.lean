module

public import M9StacksIntegration.BaseFieldPoints
public import M9StacksIntegration.SectionPullbackNonvanishing
public import M9StacksIntegration.SectionZeroIdealFactorization

/-!
# Base-field nonvanishing and actual zero schemes

A section on a scheme locally of finite type over an algebraically
closed field has empty zero scheme if it is nonzero at every point over
that field. Once this actual zero scheme is empty, the section is
nonzero at every field-valued point, including extension-field points.
The second assertion follows from the zero scheme's universal property;
it does not extend a nonexistence assertion about linear series.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ZeroSchemeBaseFieldPoints

open M9Native.SectionZeroIdealFactorization

/-- Base-field nonvanishing implies emptiness of the actual zero
scheme by the closed-point theorem over an algebraically closed base. -/
theorem isEmpty_zeroScheme_of_base_field_pullbacks_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q]
    (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (s : Γ(E, ⊤))
    (hs : ∀ (p : Spec (.of K) ⟶ X), p ≫ q = 𝟙 _ →
      pullbackGlobalSections p E s ≠ 0) :
    IsEmpty (sectionZeroIdeal X E s).subscheme := by
  let Z := (sectionZeroIdeal X E s).subscheme
  let i : Z ⟶ X := (sectionZeroIdeal X E s).subschemeι
  apply BaseFieldPoints.isEmpty_of_no_point (i ≫ q)
  intro p hp
  apply hs (p ≫ i) (by simpa only [Category.assoc] using hp)
  exact (pullbackGlobalSections_eq_zero_iff_factorsThrough E r s (p ≫ i)).2 ⟨p, rfl⟩

/-- Emptiness of the actual zero scheme implies nonvanishing after
pullback to every actual field-valued point. -/
theorem field_pullback_ne_zero_of_isEmpty_zeroScheme
    {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (s : Γ(E, ⊤)) [IsEmpty (sectionZeroIdeal X E s).subscheme]
    (L : Type u) [Field L] (p : Spec (.of L) ⟶ X) :
    pullbackGlobalSections p E s ≠ 0 := by
  intro hp
  obtain ⟨g, _⟩ := (pullbackGlobalSections_eq_zero_iff_factorsThrough E r s p).1 hp
  exact isEmptyElim (g (Classical.choice (inferInstance : Nonempty (Spec (.of L)))))

/-- The passage from base-field nonvanishing to arbitrary field-point
nonvanishing is geometric: both steps pass through the actual empty
zero scheme. -/
theorem field_pullback_ne_zero_of_base_field_pullbacks_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q]
    (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (s : Γ(E, ⊤))
    (hs : ∀ (p : Spec (.of K) ⟶ X), p ≫ q = 𝟙 _ →
      pullbackGlobalSections p E s ≠ 0)
    (L : Type u) [Field L] (p : Spec (.of L) ⟶ X) :
    pullbackGlobalSections p E s ≠ 0 := by
  let := isEmpty_zeroScheme_of_base_field_pullbacks_ne_zero q E r s hs
  exact field_pullback_ne_zero_of_isEmpty_zeroScheme E r s L p

/-- Actual section nonvanishing detects nonzero pullback of the
original structure-sheaf morphism. -/
theorem pullback_map_ne_zero_of_unitSection_ne_zero
    {X Y : Scheme.{u}} (p : Y ⟶ X) {E : X.Modules}
    (a : Stacks.Ample.unitModule X ⟶ E)
    (ha : pullbackGlobalSections p E (UnitSectionPullback.unitSection a) ≠ 0) :
    (Scheme.Modules.pullback p).map a ≠ 0 :=
  SectionPullbackNonvanishing.pullback_map_ne_zero_of_unitSection_ne_zero p a ha

end M9Native.ZeroSchemeBaseFieldPoints
