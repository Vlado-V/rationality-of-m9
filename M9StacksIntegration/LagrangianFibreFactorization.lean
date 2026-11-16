module

public import M9StacksIntegration.LagrangianIncidenceFibres
public import M9StacksIntegration.LagrangianProjectiveSectionScheme
public import M9StacksIntegration.IteratedLineSectionCuts

/-! Actual all-test factorization properties of the original incidence
fibre and the original projective-plane intersection. All structural maps
are retained, including on nonreduced test schemes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.LagrangianLinearSections
open M9Native.LagrangianProjectiveIntersection
open M9Native.LagrangianProjectiveSectionScheme
open AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace M9Native.LagrangianFibreFactorization

variable (K : Type u) [Field K]
variable (p : Spec (.of K) ⟶ parameter K)
variable (hp : p ≫ parameterProjection K = 𝟙 _)

def fixedAmbient {T : Scheme.{u}} (l : T ⟶ LagrangianGrassmannian.space K) :
    T ⟶ LagrangianLinearSections.ambient K :=
  pullback.lift l ((l ≫ LagrangianGrassmannian.projection K) ≫ p)
    (by simp only [Category.assoc, hp, Category.comp_id])

@[reassoc (attr := simp)] theorem fixedAmbient_toLG {T : Scheme.{u}}
    (l : T ⟶ LagrangianGrassmannian.space K) :
    fixedAmbient K p hp l ≫ toLG K = l := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fixedAmbient_toParameter {T : Scheme.{u}}
    (l : T ⟶ LagrangianGrassmannian.space K) :
    fixedAmbient K p hp l ≫ toParameter K =
      (l ≫ LagrangianGrassmannian.projection K) ≫ p := pullback.lift_snd _ _ _

abbrev fibre : Scheme.{u} := pullback p (familyProjection K)

abbrev fibreToLG : fibre K p ⟶ LagrangianGrassmannian.space K :=
  pullback.snd p (familyProjection K) ≫ familyToLG K

include hp in
theorem fibre_base : pullback.fst p (familyProjection K) =
    fibreToLG K p ≫ LagrangianGrassmannian.projection K := by
  have h := congrArg (fun a => a ≫ parameterProjection K)
    (pullback.condition (f := p) (g := familyProjection K))
  simpa only [Category.assoc, hp, Category.comp_id, ← family_over K,
    fibreToLG] using h

include hp in
theorem fibreToLG_mono : Mono (fibreToLG K p) := by
  constructor
  intro T g h hgh
  have hb : g ≫ pullback.fst p (familyProjection K) =
      h ≫ pullback.fst p (familyProjection K) := by
    rw [fibre_base K p hp]
    simpa only [Category.assoc] using congrArg
      (fun a => a ≫ LagrangianGrassmannian.projection K) hgh
  apply pullback.hom_ext
  · exact hb
  · apply (cancel_mono (inclusion K)).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, fibreToLG, familyToLG] using hgh
    · change g ≫ pullback.snd p (familyProjection K) ≫ familyProjection K =
        h ≫ pullback.snd p (familyProjection K) ≫ familyProjection K
      simpa only [Category.assoc, pullback.condition] using congrArg (fun a => a ≫ p) hb

theorem fibre_factorsThrough_iff {T : Scheme.{u}}
    (l : T ⟶ LagrangianGrassmannian.space K) :
    (∃ z : T ⟶ fibre K p, z ≫ fibreToLG K p = l) ↔
      (∃ z : T ⟶ family K, z ≫ inclusion K = fixedAmbient K p hp l) := by
  constructor
  · rintro ⟨z, hz⟩
    have hb : z ≫ pullback.fst p (familyProjection K) =
        l ≫ LagrangianGrassmannian.projection K := by
      rw [fibre_base K p hp]
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ LagrangianGrassmannian.projection K) hz
    refine ⟨z ≫ pullback.snd p (familyProjection K), ?_⟩
    apply pullback.hom_ext
    · change (z ≫ pullback.snd p (familyProjection K)) ≫ familyToLG K =
        fixedAmbient K p hp l ≫ toLG K
      rw [fixedAmbient_toLG]
      exact hz
    · change (z ≫ pullback.snd p (familyProjection K)) ≫ familyProjection K =
        fixedAmbient K p hp l ≫ toParameter K
      calc
        _ = (z ≫ pullback.fst p (familyProjection K)) ≫ p := by
          simp only [Category.assoc, pullback.condition]
        _ = (l ≫ LagrangianGrassmannian.projection K) ≫ p := by rw [hb]
        _ = _ := (fixedAmbient_toParameter K p hp l).symm
  · rintro ⟨z, hz⟩
    have hq : z ≫ familyProjection K =
        (l ≫ LagrangianGrassmannian.projection K) ≫ p := by
      change (z ≫ inclusion K) ≫ toParameter K = _
      rw [hz, fixedAmbient_toParameter]
    refine ⟨pullback.lift (l ≫ LagrangianGrassmannian.projection K) z hq.symm, ?_⟩
    change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ familyToLG K = l
    rw [pullback.lift_snd]
    change (z ≫ inclusion K) ≫ toLG K = l
    rw [hz, fixedAmbient_toLG]

variable [CharZero K]

theorem section_factorsThrough_iff (L : Coordinates K →ₗ[K] (Fin 5 → K))
    {T : Scheme.{u}} (l : T ⟶ LagrangianGrassmannian.space K) :
    (∃ z : T ⟶ sectionScheme K L, z ≫ sectionToLG K L = l) ↔
      (∃ z : T ⟶ plane K L,
        z ≫ quotientMap K (Forms K) (constraints K L) =
          l ≫ LagrangianPlucker.primitivePlucker K ≫ (coordinateIso K).hom) := by
  constructor
  · rintro ⟨z, hz⟩
    change z ≫ pullback.fst _ _ = l at hz
    refine ⟨z ≫ pullback.snd _ _, ?_⟩
    have h := congrArg (fun a => z ≫ a ≫ (coordinateIso K).hom)
      (pullback.condition (f := LagrangianPlucker.primitivePlucker K)
        (g := planeInclusion K L))
    have h' : (z ≫ pullback.snd _ _) ≫ quotientMap K (Forms K) (constraints K L) =
        (z ≫ pullback.fst _ _) ≫ LagrangianPlucker.primitivePlucker K ≫
          (coordinateIso K).hom := by
      simpa only [planeInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        using h.symm
    simpa only [hz] using h'
  · rintro ⟨z, hz⟩
    have hc : l ≫ LagrangianPlucker.primitivePlucker K = z ≫ planeInclusion K L := by
      have h := congrArg (fun a => a ≫ (coordinateIso K).inv) hz
      simpa only [planeInclusion, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
    exact ⟨pullback.lift l z hc, pullback.lift_fst _ _ _⟩

end M9Native.LagrangianFibreFactorization
