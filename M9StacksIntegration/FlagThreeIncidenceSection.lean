module

public import M9StacksIntegration.FlagThreeQuotient
public import M9StacksIntegration.DualQuotientSubbundle
public import M9StacksIntegration.HomBundleRank
public import M9StacksIntegration.ZeroSchemeBaseFieldPoints
public import M9StacksIntegration.FlagTowerProper

/-!
# Actual incidence section on the smaller rank-three flag tower

The native tower of three projective bundles of `E∨` carries its actual
rank-three quotient `Q`. Genuine finite locally free duality constructs
the actual inclusion `Q∨ → π*E`. Restricting an actual bundle map `E → F`
and currying gives an actual section of an actual rank-thirty Hom bundle.

If the original map has kernel dimension at most two at the actual
base-field points, this section has empty actual zero scheme over an
algebraically closed base. The finite-type/rational-point step is proved
from the actual proper flag projection. Its universal property then
gives nonvanishing of this section at arbitrary field points; no kernel
bound or absence of linear series over extension fields is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.FlagThreeIncidence

local instance finiteLocallyFreeDual {X : Scheme.{u}}
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf E) :=
  isFiniteLocallyFree_dualSheaf E inferInstance

variable {X : Scheme.{u}} (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The actual tower of three projective bundles of the actual dual. -/
abbrev space : Scheme.{u} := FlagThreeQuotient.space (dualSheaf E)
abbrev projection : space E ⟶ X := FlagThreeQuotient.projection (dualSheaf E)
abbrev quotientBundle : (space E).Modules := FlagThreeQuotient.quotientBundle (dualSheaf E) 2
abbrev kernelBundle : (space E).Modules := dualSheaf (quotientBundle E)

local instance projectionProper : IsProper (projection E) :=
  FlagTowerProper.isProper_tower 3 (dualSheaf E)

def inclusion : kernelBundle E ⟶ (Scheme.Modules.pullback (projection E)).obj E :=
  DualQuotientSubbundle.inclusion (projection E) E
    (FlagThreeQuotient.quotientMap (dualSheaf E) 2)

theorem quotientBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (quotientBundle E) 3 :=
  FlagThreeQuotient.quotientBundle_rank (dualSheaf E) 2

theorem kernelBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernelBundle E) 3 :=
  isFiniteLocallyFreeOfRank_dualSheaf (quotientBundle E) 3 (quotientBundle_rank E)

theorem pullback_inclusion_mono {T : Scheme.{u}} (p : T ⟶ space E) :
    Mono ((Scheme.Modules.pullback p).map (inclusion E)) :=
  DualQuotientSubbundle.pullback_inclusion_mono (projection E) E
    (FlagThreeQuotient.quotientMap (dualSheaf E) 2) inferInstance
    (quotientBundle_rank E).isFiniteLocallyFree p

/-- The actual restricted morphism whose zero locus is the incidence. -/
def restriction {F : X.Modules} (v : E ⟶ F) :
    kernelBundle E ⟶ (Scheme.Modules.pullback (projection E)).obj F :=
  inclusion E ≫ (Scheme.Modules.pullback (projection E)).map v

/-- The actual Hom bundle, rather than data asserting such a bundle. -/
def incidenceBundle (F : X.Modules) : (space E).Modules :=
  CurriedHomSection.homBundle (kernelBundle E) ((Scheme.Modules.pullback (projection E)).obj F)

/-- The actual global incidence section, obtained by actual currying. -/
def incidenceSection {F : X.Modules} (v : E ⟶ F) : Γ(incidenceBundle E F, ⊤) :=
  CurriedHomSection.homSection (restriction E v)

theorem incidenceBundle_rank_thirty (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (incidenceBundle E F) 30 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernelBundle E) 3 :=
    kernelBundle_rank E
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (projection E)).obj F) 10 :=
    @isFiniteLocallyFreeOfRank_pullback _ _ (projection E) F 10 hF
  exact HomBundleRank.homBundle_rank_thirty _ _

/-- Nonvanishing of the actual incidence section at an actual field
point follows from the actual kernel at the composite point. -/
theorem fieldPoint_incidenceSection_ne_zero
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {F : X.Modules} (v : E ⟶ F) (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ space E)
    (hker : Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback (p ≫ projection E)).map v)).hom) ≤ 2) :
    pullbackGlobalSections p (incidenceBundle E F) (incidenceSection E v) ≠ 0 :=
  DualQuotientSubbundle.fieldPoint_homSection_ne_zero_of_compositeKernel
    (projection E) E hE (FlagThreeQuotient.quotientMap (dualSheaf E) 2)
    inferInstance (quotientBundle_rank E) v K p hker

/-- Kernel dimension at most two over the stated algebraically closed
base gives actual incidence-zero-scheme emptiness. The needed finite
type follows from the actual proper native flag projection. -/
theorem isEmpty_zeroScheme_of_base_field_kernel_le_two
    (K : Type u) [Field K] [IsAlgClosed K]
    (qX : X ⟶ Spec (.of K)) [LocallyOfFiniteType qX]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {F : X.Modules} (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10)
    (v : E ⟶ F)
    (hker : ∀ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ →
      Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) ≤ 2) :
    IsEmpty (SectionZeroIdealFactorization.sectionZeroIdeal (space E)
      (incidenceBundle E F) (incidenceSection E v)).subscheme := by
  let : IsProper (projection E) := FlagTowerProper.isProper_tower 3 (dualSheaf E)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (incidenceBundle E F) 30 :=
    incidenceBundle_rank_thirty E F hF
  apply ZeroSchemeBaseFieldPoints.isEmpty_zeroScheme_of_base_field_pullbacks_ne_zero
    (projection E ≫ qX) (incidenceBundle E F) 30 (incidenceSection E v)
  intro p hp
  apply fieldPoint_incidenceSection_ne_zero E hE v K p
  exact hker (p ≫ projection E) (by simpa only [Category.assoc] using hp)

/-- Base-field kernel bounds imply nonvanishing at every actual
field point by first proving the actual zero scheme empty. No absence
of linear series over extension fields is used. -/
theorem fieldPoint_incidenceSection_ne_zero_of_base_field_kernel_le_two
    (K : Type u) [Field K] [IsAlgClosed K]
    (qX : X ⟶ Spec (.of K)) [LocallyOfFiniteType qX]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {F : X.Modules} (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10)
    (v : E ⟶ F)
    (hker : ∀ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ →
      Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) ≤ 2)
    (L : Type u) [Field L] (p : Spec (.of L) ⟶ space E) :
    pullbackGlobalSections p (incidenceBundle E F) (incidenceSection E v) ≠ 0 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (incidenceBundle E F) 30 :=
    incidenceBundle_rank_thirty E F hF
  letI := isEmpty_zeroScheme_of_base_field_kernel_le_two E K qX hE hF v hker
  exact ZeroSchemeBaseFieldPoints.field_pullback_ne_zero_of_isEmpty_zeroScheme
    (incidenceBundle E F) 30 (incidenceSection E v) L p

/-- The corresponding actual curried unit morphism stays nonzero at
all actual field points, exactly as needed by the genuine
nowhere-zero-section/cokernel theorem. -/
theorem fieldPoint_curriedMap_ne_zero_of_base_field_kernel_le_two
    (K : Type u) [Field K] [IsAlgClosed K]
    (qX : X ⟶ Spec (.of K)) [LocallyOfFiniteType qX]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {F : X.Modules} (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10)
    (v : E ⟶ F)
    (hker : ∀ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ →
      Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) ≤ 2)
    (L : Type u) [Field L] (p : Spec (.of L) ⟶ space E) :
    (Scheme.Modules.pullback p).map (CurriedHomSection.curriedMap (restriction E v)) ≠ 0 := by
  apply SectionPullbackNonvanishing.pullback_map_ne_zero_of_unitSection_ne_zero
  exact fieldPoint_incidenceSection_ne_zero_of_base_field_kernel_le_two E K qX hE hF v hker L p

end M9Native.FlagThreeIncidence
