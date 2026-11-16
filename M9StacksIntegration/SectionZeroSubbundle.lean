module

public import M9StacksIntegration.NativeVectorSectionZeroPullback
public import M9StacksIntegration.ExteriorSubbundleUniversalMono
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization

/-!
# Full section-zero ideals are unchanged by a subbundle inclusion

Universal injectivity is used on EVERY native test scheme, without a
reducedness restriction on the test. The actual section-zero universal
property then identifies the full ideal sheaves, not only their supports
or their closed field points. The exterior subbundle theorem discharges
universal injectivity from an actual short exact sequence with locally
free quotient in the applications.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9Native.SectionZeroSubbundle
open SectionZeroIdealFactorization
universe u
variable {X : Scheme.{u}}

/-- Monicity of an actual module morphism gives injectivity on actual
global sections, through the genuine unit-Hom universal property. -/
theorem appTop_injective_of_mono {E F : X.Modules} (j : E ⟶ F) [Mono j] :
    Function.Injective (j.app ⊤) := by
  intro a b hab
  let sa := Stacks.PresheafOfModules.sectionOfTop E.val a
  let sb := Stacks.PresheafOfModules.sectionOfTop E.val b
  have hs : _root_.SheafOfModules.sectionsMap j sa =
      _root_.SheafOfModules.sectionsMap j sb := by
    apply Stacks.PresheafOfModules.sections_ext_top
    change j.app ⊤ (sa.eval (op ⊤)) = j.app ⊤ (sb.eval (op ⊤))
    simpa only [sa, sb, Stacks.PresheafOfModules.sectionOfTop_val_top] using hab
  have hm : E.unitHomEquiv.symm sa ≫ j = E.unitHomEquiv.symm sb ≫ j := by
    rw [_root_.SheafOfModules.unitHomEquiv_symm_comp,
      _root_.SheafOfModules.unitHomEquiv_symm_comp, hs]
  have he : sa = sb := E.unitHomEquiv.symm.injective ((cancel_mono j).mp hm)
  have hv := congrArg (fun s : E.sections => s.eval (op ⊤)) he
  simpa only [sa, sb, Stacks.PresheafOfModules.sectionOfTop_val_top] using hv

/-- Equality of factorization on ALL schemes determines the full ideals. -/
theorem ideal_eq_of_all_factors (I J : X.IdealSheafData)
    (h : ∀ {T : Scheme.{u}} (f : T ⟶ X),
      (∃ a : T ⟶ I.subscheme, a ≫ I.subschemeι = f) ↔
        ∃ b : T ⟶ J.subscheme, b ≫ J.subschemeι = f) : I = J := by
  apply le_antisymm
  · have he : ∃ a : J.subscheme ⟶ I.subscheme, a ≫ I.subschemeι = J.subschemeι :=
      (h J.subschemeι).mpr ⟨𝟙 _, by simp⟩
    rw [factorsThrough_ideal_iff_ideal_le_ker, Scheme.IdealSheafData.ker_subschemeι] at he
    exact he
  · have he : ∃ b : I.subscheme ⟶ J.subscheme, b ≫ J.subschemeι = I.subschemeι :=
      (h I.subschemeι).mp ⟨𝟙 _, by simp⟩
    rw [factorsThrough_ideal_iff_ideal_le_ker, Scheme.IdealSheafData.ker_subschemeι] at he
    exact he

/-- After arbitrary pullback, a universally monic map detects exact
vanishing of the original section, also on nonreduced schemes. -/
theorem pullback_image_eq_zero_iff {E F : X.Modules} (j : E ⟶ F)
    (hj : ∀ {T : Scheme.{u}} (f : T ⟶ X), Mono ((Scheme.Modules.pullback f).map j))
    (s : Γ(E, ⊤)) {T : Scheme.{u}} (f : T ⟶ X) :
    pullbackGlobalSections f F (j.app ⊤ s) = 0 ↔ pullbackGlobalSections f E s = 0 := by
  let : Mono ((Scheme.Modules.pullback f).map j) := hj f
  rw [← pullback_map_app_pullbackGlobalSections]
  exact map_eq_zero_iff _ (appTop_injective_of_mono _)

/-- Equality of full ideal sheaves follows from the genuine all-test
zero-scheme universal property, with no support/radical replacement. -/
theorem sectionZeroIdeal_eq_of_universallyMono {E F : X.Modules} (j : E ⟶ F)
    (r q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F q]
    (hj : ∀ {T : Scheme.{u}} (f : T ⟶ X), Mono ((Scheme.Modules.pullback f).map j))
    (s : Γ(E, ⊤)) :
    sectionZeroIdeal X F (j.app ⊤ s) = sectionZeroIdeal X E s := by
  apply ideal_eq_of_all_factors
  intro T f
  rw [← pullbackGlobalSections_eq_zero_iff_factorsThrough F q (j.app ⊤ s) f,
    ← pullbackGlobalSections_eq_zero_iff_factorsThrough E r s f]
  exact pullback_image_eq_zero_iff j hj s f

/-- The literal native zero schemes have the SAME full ideal sheaf. -/
theorem zeroSchemeOfSection_eq_of_universallyMono {E F : X.Modules} (j : E ⟶ F)
    (r q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F q]
    (hj : ∀ {T : Scheme.{u}} (f : T ⟶ X), Mono ((Scheme.Modules.pullback f).map j))
    (s : Γ(E, ⊤)) :
    Stacks.Chow.zeroSchemeOfSection X F (j.app ⊤ s) =
      Stacks.Chow.zeroSchemeOfSection X E s := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F q
  rw [NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal,
    NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal]
  exact sectionZeroIdeal_eq_of_universallyMono j r q hj s

end M9Native.SectionZeroSubbundle
