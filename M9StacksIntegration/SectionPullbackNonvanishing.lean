module

public import M9StacksIntegration.UnitSectionPullback

/-!
# Detecting an actual pulled-back section morphism

Pullback of a structure-sheaf morphism is zero exactly when pullback
of its actual global unit section is zero. This comparison uses the
genuine structure-sheaf pullback isomorphism and holds for every scheme
morphism, without a flatness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.SectionPullbackNonvanishing

theorem pullback_map_eq_zero_iff_unitSection_eq_zero
    {X Y : Scheme.{u}} (p : Y ⟶ X) {E : X.Modules}
    (a : Stacks.Ample.unitModule X ⟶ E) :
    (Scheme.Modules.pullback p).map a = 0 ↔
      pullbackGlobalSections p E (UnitSectionPullback.unitSection a) = 0 := by
  rw [← UnitSectionPullback.unitSection_pulledUnitMap]
  constructor
  · intro h
    have hz : UnitSectionPullback.pulledUnitMap p a = 0 := by
      unfold UnitSectionPullback.pulledUnitMap
      rw [h, comp_zero]
    rw [hz]
    simp only [UnitSectionPullback.unitSection, Scheme.Modules.Hom.zero_app]
    rfl
  · intro h
    have hmap := UnitSectionPullback.eq_zero_of_unitSection_eq_zero
      (UnitSectionPullback.pulledUnitMap p a) h
    have hc := congrArg (fun b => (Scheme.Modules.pullbackUnitIso p).hom ≫ b) hmap
    simpa only [UnitSectionPullback.pulledUnitMap, Category.assoc,
      Iso.hom_inv_id_assoc, comp_zero] using hc

theorem pullback_map_ne_zero_of_unitSection_ne_zero
    {X Y : Scheme.{u}} (p : Y ⟶ X) {E : X.Modules}
    (a : Stacks.Ample.unitModule X ⟶ E)
    (ha : pullbackGlobalSections p E (UnitSectionPullback.unitSection a) ≠ 0) :
    (Scheme.Modules.pullback p).map a ≠ 0 :=
  mt (pullback_map_eq_zero_iff_unitSection_eq_zero p a).1 ha

end M9Native.SectionPullbackNonvanishing
