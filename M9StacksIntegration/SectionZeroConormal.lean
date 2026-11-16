module

public import M9StacksIntegration.SectionZeroEvaluation
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.EpiIso

/-!
# Actual section evaluation into the conormal of its zero scheme

This is the actual pullback of the original dual-evaluation map onto
the actual native zero ideal, followed by the canonical comparison
with the original immersion conormal. Local generators prove Epi.
The equal-rank lemma then derives IsIso; a geometric caller must prove
that actual conormal rank and is not allowed to supply a desired map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionZeroConormal

variable {X : Scheme.{u}} (E : X.Modules)
  [hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
  (s : Γ(E, (⊤ : X.Opens)))

abbrev zeroIdeal : X.IdealSheafData := Stacks.Chow.zeroSchemeOfSection X E s

abbrev space : Scheme.{u} := (zeroIdeal E s).subscheme

abbrev inclusion : space E s ⟶ X := (zeroIdeal E s).subschemeι

/-- The original native conormal, in the canonical category of modules. -/
abbrev conormalModule : (space E s).Modules :=
  Stacks.Conormal.conormalSheaf (inclusion E s)

/-- Only the canonical defining-ideal/coborder comparison is used here. -/
def idealPullbackConormalIso :
    (Scheme.Modules.pullback (inclusion E s)).obj (idealSheafModule (zeroIdeal E s)) ≅
      conormalModule E s :=
  Stacks.Immersion.conormalSheafSelfIso (inclusion E s)

abbrev sourceModule : (space E s).Modules :=
  (Scheme.Modules.pullback (inclusion E s)).obj (dualSheaf E)

/-- The actual section-induced conormal evaluation. -/
def evaluationMap : sourceModule E s ⟶ conormalModule E s :=
  (Scheme.Modules.pullback (inclusion E s)).map
    (SectionZeroEvaluation.evaluationIdealMap E s) ≫ (idealPullbackConormalIso E s).hom

/-- The actual map is epimorphic; no regularity or conormal rank is needed. -/
instance evaluationMap_epi : Epi (evaluationMap E s) := by
  have : Epi (SectionZeroEvaluation.evaluationIdealMap E s) :=
    SectionZeroEvaluation.evaluationIdealMap_epi E s
  have : Epi ((Scheme.Modules.pullback (inclusion E s)).map
      (SectionZeroEvaluation.evaluationIdealMap E s)) :=
    Functor.map_epi (Scheme.Modules.pullback (inclusion E s)) _
  exact epi_comp _ _

/-- The canonical ideal-section to conormal-class morphism. -/
def idealClassMap : idealSheafModule (zeroIdeal E s) ⟶
    (Scheme.Modules.pushforward (inclusion E s)).obj (conormalModule E s) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (inclusion E s)).unit.app _ ≫
    (Scheme.Modules.pushforward (inclusion E s)).map (idealPullbackConormalIso E s).hom

/-- The normalization is actual evaluation followed by the canonical class map. -/
theorem evaluationMap_adjunction :
    ((Scheme.Modules.pullbackPushforwardAdjunction (inclusion E s)).homEquiv _ _)
      (evaluationMap E s) =
        SectionZeroEvaluation.evaluationIdealMap E s ≫ idealClassMap E s := by
  change (Scheme.Modules.pullbackPushforwardAdjunction (inclusion E s)).unit.app _ ≫
    (Scheme.Modules.pushforward (inclusion E s)).map
      ((Scheme.Modules.pullback (inclusion E s)).map
        (SectionZeroEvaluation.evaluationIdealMap E s) ≫
        (idealPullbackConormalIso E s).hom) = _
  rw [Functor.map_comp, ← Category.assoc]
  exact (congrArg (fun g => g ≫ (Scheme.Modules.pushforward (inclusion E s)).map
      (idealPullbackConormalIso E s).hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction (inclusion E s)).unit.naturality
      (SectionZeroEvaluation.evaluationIdealMap E s)).symm).trans (Category.assoc _ _ _)

/-- Equal actual ranks force the original evaluation map to be an iso.
A caller must derive the actual target rank, not assume the normal map. -/
theorem evaluationMap_isIso_of_rank (r : ℕ)
    (hEr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r)
    (hNr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalModule E s) r) :
    IsIso (evaluationMap E s) := by
  let := hNr
  let := isFiniteLocallyFreeOfRank_dualSheaf E r hEr
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (sourceModule E s) r :=
    isFiniteLocallyFreeOfRank_pullback (inclusion E s) (dualSheaf E) r
  exact SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank (evaluationMap E s) r

/-- The actual evaluation isomorphism under independently proved equal ranks. -/
def evaluationIsoOfRank (r : ℕ)
    (hEr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r)
    (hNr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalModule E s) r) :
    sourceModule E s ≅ conormalModule E s := by
  let := evaluationMap_isIso_of_rank E s r hEr hNr
  exact asIso (evaluationMap E s)

theorem evaluationIsoOfRank_hom (r : ℕ)
    (hEr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r)
    (hNr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalModule E s) r) :
    (evaluationIsoOfRank E s r hEr hNr).hom = evaluationMap E s := rfl

end M9Native.SectionZeroConormal
