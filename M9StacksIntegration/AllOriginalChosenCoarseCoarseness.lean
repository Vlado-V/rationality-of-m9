module

public import M9StacksIntegration.AllOriginalChosenCoarseCategorical
public import M9StacksIntegration.AllOriginalChosenCoarseGeometric

@[expose] public section

/-! The actual full original chosen classifier is a genuine coarse moduli
map. Both categorical universality against ALL original algebraic-space
targets and the exact original geometric-fibre assertion are theorems.
No semantic, classifier-comparison or coarse-existence premise is supplied.
This NEW leaf augments the existing frozen classifier namespace. -/

noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace M9Native.AllOriginalChosenCoarseClassifier

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- Full coarse moduli of ALL original smooth connected unpointed genus-g
families, on every original test and every algebraically closed extension.
The independently chosen actual native target and actual classifier are
retained; no original/native comparison premise is an input. -/
theorem isCoarse (g : ℕ) (hg : 2 ≤ g) :
    M9StandaloneDraft.IsCoarse K (classifier B hZ K hK g hg) :=
  ⟨AllOriginalChosenCoarseCategorical.isCategorical B hZ K hK g hg,
    AllOriginalChosenCoarseGeometric.classifier_isGeometric B hZ K hK g hg⟩

/-- The literal genus-nine extraction used by the actual paper endpoint. -/
theorem genusNine_isCoarse :
    M9StandaloneDraft.IsCoarse K (classifier B hZ K hK 9 (by decide)) :=
  isCoarse B hZ K hK 9 (by decide)

end M9Native.AllOriginalChosenCoarseClassifier
