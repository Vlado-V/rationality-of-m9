module

public import M9StacksIntegration.LagrangianIncidenceFieldBaseChange
public import M9StacksIntegration.ProperSmoothLocusBaseChange
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth
public import M9StacksIntegration.OpenRestrictionPointFiber

/-! Actual cross-field parameters in the unchanged original good open.
The native smooth-locus reflection and the actual cartesian universal
family prove the good-open equality. The whole-fibre isomorphisms keep
the literal Spec L map and the literal original parameter triangle. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.LagrangianGoodOpenFieldBaseChange
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianIncidenceParameterBaseChange

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)

/-- A genuine field extension is flat on spectra. -/
theorem specMap_flat : Flat (GrassmannianFieldBaseChange.specMap φ) :=
  Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField K) _)

/-- The actual universal parameter field-base map is flat. -/
theorem parameterMap_flat : Flat (GrassmannianFieldBaseChange.map φ 9 14) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (GrassmannianFieldBaseChange.map_isPullback φ 9 14).flip (specMap_flat φ)

/-- The same actual parameter map is surjective: the field spectrum map
is surjective, and the native Grassmannian square is cartesian. -/
theorem parameterMap_surjective : Surjective (GrassmannianFieldBaseChange.map φ 9 14) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (GrassmannianFieldBaseChange.map_isPullback φ 9 14).flip
      (inferInstanceAs (Surjective (GrassmannianFieldBaseChange.specMap φ)))

/-- Faithful flatness of the actual parameter field-base change. -/
theorem parameterMap_flat_surjective :
    Flat (GrassmannianFieldBaseChange.map φ 9 14) ∧
      Surjective (GrassmannianFieldBaseChange.map φ 9 14) :=
  ⟨parameterMap_flat φ, parameterMap_surjective φ⟩

/-- The genuine proper smooth parameter open commutes with field base
change, derived from the full original incidence family. -/
theorem goodOpen_eq_preimage :
    goodOpen L = (GrassmannianFieldBaseChange.map φ 9 14) ⁻¹ᵁ goodOpen K :=
  ProperSmoothLocusBaseChange.goodOpen_eq_preimage
    (LagrangianIncidenceFieldBaseChange.familyMap_isPullback φ) (.inr (parameterMap_flat φ))

/-- Pointwise reflection for arbitrary test schemes. -/
theorem parameterMap_mem_goodOpen_iff {T : Scheme.{u}} (q : T ⟶ parameter L) (t : T) :
    parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q t ∈ goodOpen K ↔
      q t ∈ goodOpen L := by
  rw [goodOpen_eq_preimage φ]
  change _ ↔ (GrassmannianFieldBaseChange.map φ 9 14) (q t) ∈ goodOpen K
  rw [LagrangianIncidenceFieldBaseChange.parameterMap_eq]
  rfl

theorem parameterMap_lands_goodOpen {T : Scheme.{u}} (q : T ⟶ parameter L)
    (hgood : ∀ t : T, q t ∈ goodOpen L) :
    ∀ t : T, parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q t ∈ goodOpen K :=
  fun t => (parameterMap_mem_goodOpen_iff φ q t).mpr (hgood t)

/-- The actual cross-field point lifted into the original good open. -/
def goodParameter {T : Scheme.{u}} (q : T ⟶ parameter L)
    (hgood : ∀ t : T, q t ∈ goodOpen L) : T ⟶ (goodOpen K).toScheme :=
  OpenRestrictionPointFiber.lift (goodOpen K)
    (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q)
      (parameterMap_lands_goodOpen φ q hgood)

/-- The actual original-parameter triangle, with the exact given field map. -/
@[reassoc (attr := simp)] theorem goodParameter_comp {T : Scheme.{u}} (q : T ⟶ parameter L)
    (hgood : ∀ t : T, q t ∈ goodOpen L) :
    goodParameter φ q hgood ≫ (goodOpen K).ι =
      parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q :=
  OpenRestrictionPointFiber.lift_comp _ _ _

/-- The original native L-fibre is cartesian over the actual K-parameter,
with its original arbitrary test base retained. -/
theorem nativeFibre_isPullback {T : Scheme.{u}} (q : T ⟶ parameter L) :
    IsPullback
      (pullback.fst (familyProjection L) q ≫ LagrangianIncidenceFieldBaseChange.familyMap φ)
      (pullback.snd (familyProjection L) q) (familyProjection K)
      (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q) := by
  have h := (IsPullback.of_hasPullback (familyProjection L) q).paste_horiz
    (LagrangianIncidenceFieldBaseChange.familyMap_isPullback φ)
  simpa only [LagrangianIncidenceFieldBaseChange.parameterMap_eq] using h

def nativeFibreIso {T : Scheme.{u}} (q : T ⟶ parameter L) :
    pullback (familyProjection L) q ≅
      pullback (familyProjection K)
        (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q) :=
  (nativeFibre_isPullback φ q).isoPullback

@[reassoc (attr := simp)] theorem nativeFibreIso_hom_base {T : Scheme.{u}} (q : T ⟶ parameter L) :
    (nativeFibreIso φ q).hom ≫
      pullback.snd (familyProjection K)
        (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q) =
      pullback.snd (familyProjection L) q :=
  (nativeFibre_isPullback φ q).isoPullback_hom_snd

/-- The native whole fibre, now as a fibre of the unchanged original
restricted good family, retaining the original arbitrary test base. -/
def nativeGoodFibreIso {T : Scheme.{u}} (q : T ⟶ parameter L)
    (hgood : ∀ t : T, q t ∈ goodOpen L) :
    pullback (familyProjection L) q ≅
      pullback (restrictedProjection K) (goodParameter φ q hgood) :=
  nativeFibreIso φ q ≪≫
    (OpenRestrictionPointFiber.fiberIso (familyProjection K) (goodOpen K)
      (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q)
        (parameterMap_lands_goodOpen φ q hgood)).symm

@[reassoc (attr := simp)] theorem nativeGoodFibreIso_hom_base {T : Scheme.{u}}
    (q : T ⟶ parameter L) (hgood : ∀ t : T, q t ∈ goodOpen L) :
    (nativeGoodFibreIso φ q hgood).hom ≫
      pullback.snd (restrictedProjection K) (goodParameter φ q hgood) =
      pullback.snd (familyProjection L) q := by
  have h := OpenRestrictionPointFiber.fiberIso_hom_snd (familyProjection K) (goodOpen K)
    (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q)
      (parameterMap_lands_goodOpen φ q hgood)
  change ((nativeFibreIso φ q).hom ≫
    (OpenRestrictionPointFiber.fiberIso (familyProjection K) (goodOpen K)
      (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q)
        (parameterMap_lands_goodOpen φ q hgood)).inv) ≫
    pullback.snd (familyProjection K ∣_ goodOpen K)
      (OpenRestrictionPointFiber.lift (goodOpen K)
        (parameterMap K L (GrassmannianFieldBaseChange.specMap φ) q)
          (parameterMap_lands_goodOpen φ q hgood)) = _
  rw [Category.assoc, ← h, Iso.inv_hom_id_assoc]
  exact nativeFibreIso_hom_base φ q

end M9Native.LagrangianGoodOpenFieldBaseChange
