module

public import M9StacksIntegration.LagrangianCurveConormal
public import M9StacksIntegration.SectionZeroConormal

/-! The actual rank-five section conormal of a genuine smooth curve zero scheme in LG. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianSmoothSectionConormal

open LagrangianGrassmannian
variable (K : Type u) [Field K] (E : (space K).Modules)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 5]

local instance equation_finiteLocallyFree : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
  hE.isFiniteLocallyFree

variable (s : Γ(E,⊤))
  [SmoothOfRelativeDimension 1 (SectionZeroConormal.inclusion E s ≫ projection K)]

/-- The exact native smooth-curve conormal sequence of the original
zero scheme of the original section. -/
abbrev nativeSequence := LagrangianCurveConormal.sequence K (SectionZeroConormal.inclusion E s)

theorem nativeSequence_shortExact : (nativeSequence K E s).ShortExact :=
  LagrangianCurveConormal.sequence_shortExact K (SectionZeroConormal.inclusion E s)

/-- The actual section evaluation is an isomorphism because actual
smooth curve geometry derives conormal rank five. -/
def conormalEvaluationIso : SectionZeroConormal.sourceModule E s ≅
    SectionZeroConormal.conormalModule E s :=
  SectionZeroConormal.evaluationIsoOfRank E s 5 hE
    (LagrangianCurveConormal.conormal_rank K (SectionZeroConormal.inclusion E s))

/-- The actual equation-dual bundle identifies with the native first
term, through actual evaluation and the canonical defining-ideal bridge. -/
def equationConormalIso : SectionZeroConormal.sourceModule E s ≅
    (nativeSequence K E s).X₁ :=
  conormalEvaluationIso K E s ≪≫
    (LagrangianCurveConormal.sourceIso K (SectionZeroConormal.inclusion E s)).symm

/-- The isomorphism retains the literal original evaluation map. -/
theorem conormalEvaluationIso_hom :
    (conormalEvaluationIso K E s).hom=SectionZeroConormal.evaluationMap E s := rfl

/-- The actual conormal complex, with the original equation-dual bundle
as its source and the actual native differentials as its other terms. -/
def equationSequence : ShortComplex (SectionZeroConormal.space E s).Modules :=
  ShortComplex.mk
    ((equationConormalIso K E s).hom ≫ (nativeSequence K E s).f)
    (nativeSequence K E s).g (by simp [Category.assoc])

/-- The change of first term is the genuine evaluation isomorphism. -/
def equationSequenceIso : equationSequence K E s ≅ nativeSequence K E s :=
  ShortComplex.isoMk (equationConormalIso K E s) (Iso.refl _) (Iso.refl _)
    (by simp [equationSequence]) (by simp [equationSequence])

/-- The actual original rank-five equation-dual conormal complex is
short exact, with no evaluation-isomorphism or conormal-rank premise. -/
theorem equationSequence_shortExact : (equationSequence K E s).ShortExact :=
  ShortComplex.shortExact_of_iso (equationSequenceIso K E s).symm
    (nativeSequence_shortExact K E s)

end M9Native.LagrangianSmoothSectionConormal
