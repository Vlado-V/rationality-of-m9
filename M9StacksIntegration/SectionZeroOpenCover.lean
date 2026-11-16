module

public import M9StacksIntegration.SectionZeroSubbundle
public import M9StacksIntegration.NonzeroSectionZeroFinite
public import Mathlib.AlgebraicGeometry.Gluing

/-! Actual section vanishing is local on a genuine scheme open cover.
The proof glues actual factorization maps through the full section zero
scheme. It applies on nonreduced schemes and makes no field-point test. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v

namespace M9Native.SectionZeroOpenCover

theorem section_eq_zero_of_pullbacks_eq_zero {X : Scheme.{u}} (E : X.Modules)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (s : Γ(E, ⊤)) (U : Scheme.OpenCover.{v} X)
    (h : ∀ i, pullbackGlobalSections (U.f i) E s = 0) : s = 0 := by
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let I := SectionZeroIdealFactorization.sectionZeroIdeal X E s
  choose g hg using fun i =>
    (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
      E r s (U.f i)).mp (h i)
  have hg' (i : U.I₀) : g i ≫ I.subschemeι = U.f i := hg i
  have hc (i j : U.I₀) : pullback.fst (U.f i) (U.f j) ≫ g i =
      pullback.snd (U.f i) (U.f j) ≫ g j := by
    apply (cancel_mono I.subschemeι).mp
    simpa only [Category.assoc, hg'] using pullback.condition (f := U.f i) (g := U.f j)
  have hf : U.glueMorphisms g hc ≫ I.subschemeι = 𝟙 X := by
    apply U.hom_ext
    intro i
    rw [← Category.assoc, U.ι_glueMorphisms, hg', Category.comp_id]
  have hI := (factorsThrough_ideal_iff_ideal_le_ker I (𝟙 X)).mp
    ⟨U.glueMorphisms g hc, hf⟩
  have hbot : I = ⊥ := le_bot_iff.mp (by
    simpa only [Scheme.Hom.ker_eq_bot_of_isIso] using hI)
  apply NonzeroSectionZeroFinite.section_eq_zero_of_zeroScheme_eq_bot E s
  exact (NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal E s).trans hbot

end M9Native.SectionZeroOpenCover
