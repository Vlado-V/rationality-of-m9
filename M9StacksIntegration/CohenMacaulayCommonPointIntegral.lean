module

public import M9StacksIntegration.CurveContainingComponents
public import M9StacksIntegration.OrderedPrefixRegularity
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization

/-!
# From a common regular point and Cohen--Macaulayness to actual integrality

If every component of an actual locally Noetherian scheme passes through a
single regular point, its local spectrum proves irreducibility. Regularity
then propagates to the unique generic point, and the genuine scheme Serre
criterion makes Cohen--Macaulayness remove the possible nilpotent structure.

The affine proof of regularity under generization follows the corresponding
step of the pinned native `Properties/RegularCharacterization.lean` proof of
`isRegular_tfae` (Apache 2.0), using its public `regular_atPrime_of_le` theorem.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
namespace M9Native.CohenMacaulayCommonPointIntegral

/-- Regularity of the actual local ring propagates from a point to every
generization, with the genuine affine localization maps. -/
theorem regular_stalk_of_specializes (X : Scheme.{u}) [IsLocallyNoetherian X]
    {x y : X} (hxy : x ⤳ y)
    (hy : IsRegularLocalRing (X.presheaf.stalk y)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, hyV⟩ : ∃ V : X.affineOpens, y ∈ V.val := by
    rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]
    trivial
  have hxV : x ∈ V.val := hxy.mem_open V.1.2 hyV
  let px := V.2.primeIdealOf ⟨x, hxV⟩
  let py := V.2.primeIdealOf ⟨y, hyV⟩
  have hpxy : px ≤ py := by
    rw [PrimeSpectrum.le_iff_specializes]
    change V.2.isoSpec.hom ⟨x, hxV⟩ ⤳ V.2.isoSpec.hom ⟨y, hyV⟩
    exact V.2.isoSpec.hom.base.hom.map_specializes
      (Topology.IsInducing.subtypeVal.specializes_iff.mp hxy)
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  let := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
  have := V.2.isLocalization_stalk ⟨y, hyV⟩
  let : IsRegularLocalRing (X.presheaf.stalk y) := hy
  have hpy : IsRegularLocalRing (Localization.AtPrime py.asIdeal) :=
    IsRegularLocalRing.of_ringEquiv
      ((IsLocalization.algEquiv py.asIdeal.primeCompl
        (Localization.AtPrime py.asIdeal) (X.presheaf.stalk y)).toRingEquiv).symm
  have hpx : IsRegularLocalRing (Localization.AtPrime px.asIdeal) :=
    regular_atPrime_of_le px.asIdeal py.asIdeal hpxy hpy
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := V.2.isLocalization_stalk ⟨x, hxV⟩
  exact @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime px.asIdeal) _ hpx _ _
    (IsLocalization.algEquiv px.asIdeal.primeCompl
      (Localization.AtPrime px.asIdeal) (X.presheaf.stalk x)).toRingEquiv

attribute [local instance] specializationOrder in
/-- On an actual irreducible locally Noetherian scheme, a single regular
point gives the regularity in codimension zero needed by Serre's criterion. -/
theorem regularInCodimensionZero_of_regular_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IrreducibleSpace X]
    (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularInCodimension X 0 := by
  intro y hy
  have hc : Order.coheight y = 0 := by
    apply le_antisymm
    · rw [ringKrullDim_stalk_eq_coheight] at hy
      exact_mod_cast hy
    · exact bot_le
  have hym : IsMax y := Order.coheight_eq_zero.mp hc
  have hgen : y ≤ genericPoint X := genericPoint_specializes y
  have heq : y = genericPoint X := le_antisymm hgen (hym hgen)
  rw [heq]
  exact regular_stalk_of_specializes X (genericPoint_specializes x) hx

/-- Actual integrality follows from actual Cohen--Macaulayness and a
common regular point of the actual irreducible components. No reducedness,
irreducibility, associated-prime or zero-nilradical premise is supplied. -/
theorem integral_of_cm_of_components_common_regular_point
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hCM : IsCohenMacaulay X)
    (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x))
    (hcomp : ∀ Z ∈ irreducibleComponents X, x ∈ Z) : IsIntegral X := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := hx
  let : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  let : IrreducibleSpace X :=
    CurveContainingComponents.irreducibleSpace_of_domain_stalk_of_components X x hcomp
  have hS : HasPropertySk X 1 :=
    (isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM 1
  let : IsReduced X :=
    (isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero X).mpr
      ⟨hS, regularInCodimensionZero_of_regular_stalk X x hx⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end M9Native.CohenMacaulayCommonPointIntegral
