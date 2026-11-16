module

public import M9StacksIntegration.LagrangianLinearSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Scheme-theoretic fibres of the original universal LG incidence.
For every actual base-valued parameter point, the original family fibre
is the actual pulled tensor-section zero scheme on the actual base change
of LG. The isomorphism retains both the structural map and the original
LG map; this is not a replacement by a pointwise fibre predicate. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.LagrangianLinearSections

universe u

namespace M9Native.LagrangianIncidenceFibres

variable (K : Type u) [Field K] {T : Scheme.{u}} (p : T ⟶ parameter K)

abbrev lagrangianOverPoint :=
  pullback (LagrangianGrassmannian.projection K) (p ≫ parameterProjection K)

/-- The genuine product map determined by the original parameter point. -/
def toAmbient : lagrangianOverPoint K p ⟶ ambient K :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := LagrangianGrassmannian.projection K)
        (g := p ≫ parameterProjection K)))

@[reassoc (attr := simp)] theorem toAmbient_toLG :
    toAmbient K p ≫ toLG K = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem toAmbient_toParameter :
    toAmbient K p ≫ toParameter K = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem toAmbient_isPullback : IsPullback (toAmbient K p) (pullback.snd _ _)
    (toParameter K) p := by
  apply IsPullback.of_right (h₁₂ := toLG K) (h₂₂ := parameterProjection K)
  · simpa only [toAmbient_toLG] using
      (IsPullback.of_hasPullback (LagrangianGrassmannian.projection K)
        (p ≫ parameterProjection K))
  · exact toAmbient_toParameter K p
  · exact IsPullback.of_hasPullback _ _

def zeroIdeal : (lagrangianOverPoint K p).IdealSheafData :=
  (ideal K).comap (toAmbient K p)

/-- The ideal is literally the zero ideal of the original pulled tensor
section, with no vanishing, rank, or fibre-identification hypothesis. -/
theorem zeroIdeal_eq_sectionZeroIdeal : zeroIdeal K p =
    SectionZeroIdealFactorization.sectionZeroIdeal (lagrangianOverPoint K p)
      ((Scheme.Modules.pullback (toAmbient K p)).obj (equationBundle K))
      (AlgebraicGeometry.pullbackGlobalSections (toAmbient K p)
        (equationBundle K) (equationSection K)) :=
  ideal_baseChange K (toAmbient K p)

abbrev zeroScheme := (zeroIdeal K p).subscheme
abbrev zeroInclusion : zeroScheme K p ⟶ lagrangianOverPoint K p :=
  (zeroIdeal K p).subschemeι

/-- The genuine original scheme-theoretic fibre is the genuine zero
subscheme of the pulled rank-five tensor section on LG over the point. -/
def zeroSchemeIsoFibre : zeroScheme K p ≅ pullback p (familyProjection K) :=
  (ideal K).comapIso (toAmbient K p) ≪≫
    ((IsPullback.of_hasPullback (toAmbient K p) (inclusion K)).flip.paste_vert
      (toAmbient_isPullback K p)).isoPullback ≪≫
    pullbackSymmetry (familyProjection K) p

@[reassoc (attr := simp)] theorem zeroSchemeIsoFibre_hom_base :
    (zeroSchemeIsoFibre K p).hom ≫ pullback.fst p (familyProjection K) =
      zeroInclusion K p ≫ pullback.snd _ _ := by
  dsimp only [zeroSchemeIsoFibre, zeroInclusion, zeroScheme, zeroIdeal]
  simp only [Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, IsPullback.isoPullback_hom_snd]
  rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]

@[reassoc (attr := simp)] theorem zeroSchemeIsoFibre_hom_toLG :
    (zeroSchemeIsoFibre K p).hom ≫ pullback.snd p (familyProjection K) ≫ familyToLG K =
      zeroInclusion K p ≫ pullback.fst _ _ := by
  dsimp only [zeroSchemeIsoFibre, zeroInclusion, zeroScheme, zeroIdeal]
  simp only [Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd_assoc, IsPullback.isoPullback_hom_fst_assoc]
  change ((ideal K).comapIso (toAmbient K p)).hom ≫
      pullback.snd (toAmbient K p) (inclusion K) ≫ inclusion K ≫ toLG K = _
  rw [← pullback.condition_assoc]
  simp only [toAmbient_toLG, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

end M9Native.LagrangianIncidenceFibres
