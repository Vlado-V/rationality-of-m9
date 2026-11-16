module

public import M9StacksIntegration.LagrangianIncidenceParameterBaseChange

/-!
# The original LG-point incidence fibre and its actual quotient

The fibre is the literal pullback of the original family-to-LG map.  Its
quotient has a genuine native Grassmannian classifier over the point's
field, and kills the actual constant Pluecker line on the whole fibre.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianIncidenceFibreQuotient

open LagrangianLinearSections LagrangianIncidenceParameterBaseChange
open LagrangianIncidenceFieldFrame

variable (K L : Type u) [Field K] [Field L]
    (x : Spec (.of L) ⟶ LagrangianGrassmannian.space K)

abbrev fibre : Scheme.{u} := pullback (familyToLG K) x
abbrev toFamily : fibre K L x ⟶ family K := pullback.fst _ _
abbrev projection : fibre K L x ⟶ Spec (.of L) := pullback.snd _ _

/-- The literal original quotient, classified over the actual field of
the LG point. -/
def toParameter : fibre K L x ⟶ parameter L :=
  pullback.lift (projection K L x)
    (toFamily K L x ≫ familyProjection K ≫ GrassmannianCharts.toIntegral K 9 14)
      (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem toParameter_projection :
    toParameter K L x ≫ parameterProjection L = projection K L x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toParameter_toIntegral :
    toParameter K L x ≫ GrassmannianCharts.toIntegral L 9 14 =
      toFamily K L x ≫ familyProjection K ≫ GrassmannianCharts.toIntegral K 9 14 :=
  pullback.lift_snd _ _ _

theorem parameterMap_toParameter :
    parameterMap K L (x ≫ LagrangianGrassmannian.projection K) (toParameter K L x) =
      toFamily K L x ≫ familyProjection K := by
  apply pullback.hom_ext
  · have hb : toFamily K L x ≫ familyProjection K ≫ parameterProjection K =
        projection K L x ≫ x ≫ LagrangianGrassmannian.projection K := by
      rw [← family_over, ← Category.assoc, pullback.condition, Category.assoc]
    simpa only [Category.assoc, parameterMap_projection, toParameter_projection_assoc] using hb.symm
  · simp only [Category.assoc, parameterMap_toIntegral, toParameter_toIntegral]

/-- The ambient point reconstructed from the actual field quotient is
the original fibre point, as an equality of scheme morphisms. -/
theorem ambientMap_eq :
    ambientMap K L x (projection K L x) (toParameter K L x) (toParameter_projection K L x) =
      toFamily K L x ≫ LagrangianLinearSections.inclusion K := by
  apply pullback.hom_ext
  · rw [ambientMap_toLG]
    exact (pullback.condition (f := familyToLG K) (g := x)).symm
  · rw [ambientMap_toParameter, parameterMap_toParameter]
    rfl

theorem toFamily_inclusion_eq {T : Scheme.{u}} (u : T ⟶ fibre K L x) :
    u ≫ toFamily K L x ≫ LagrangianLinearSections.inclusion K =
      ambientMap K L x (u ≫ projection K L x) (u ≫ toParameter K L x)
        (by simp only [Category.assoc, toParameter_projection]) := by
  rw [← ambientMap_eq, ambientMap_comp]

theorem hom_ext_of_parameter {T : Scheme.{u}} (u v : T ⟶ fibre K L x)
    (h : u ≫ toParameter K L x = v ≫ toParameter K L x) : u = v := by
  have hp : u ≫ projection K L x = v ≫ projection K L x := by
    simpa only [Category.assoc, toParameter_projection] using
      congrArg (fun a => a ≫ parameterProjection L) h
  apply pullback.hom_ext
  · apply (cancel_mono (LagrangianLinearSections.inclusion K)).1
    simp only [Category.assoc]
    rw [toFamily_inclusion_eq, toFamily_inclusion_eq]
    apply pullback.hom_ext
    · simp only [ambientMap_toLG]
      exact congrArg (fun a => a ≫ x) hp
    · simp only [ambientMap_toParameter]
      exact congrArg (parameterMap K L (x ≫ LagrangianGrassmannian.projection K)) h
  · exact hp

instance toParameter_mono : Mono (toParameter K L x) where
  right_cancellation := fun {_T} u v h => hom_ext_of_parameter K L x u v h

/-- On the whole genuine fibre, the actual universal quotient kills the
constant line-column obtained from any actual field-point line frame. -/
theorem quotient_kills_column
    (e : (Scheme.Modules.pullback x).obj (LagrangianPluckerQuotient.determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules)) :
    coefficientColumn (fibre K L x) (fun j =>
      (projection K L x).appTop ((Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j))) ≫
        (AlgebraicGeometry.Grassmannian.pullbackPresentation (toParameter K L x)
          (parameterQuotient L)).map = 0 := by
  apply (ambientMap_factorsThrough_iff_constantColumn_zero K L x
    (projection K L x) (toParameter K L x) (toParameter_projection K L x) e).mp
  exact ⟨toFamily K L x, (ambientMap_eq K L x).symm⟩

/-- The original fibre is exactly the annihilation subfunctor on every
test scheme of the native field Grassmannian. -/
theorem factorsThrough_iff_column_zero {T : Scheme.{u}} (q : T ⟶ parameter L)
    (e : (Scheme.Modules.pullback x).obj (LagrangianPluckerQuotient.determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules)) :
    (∃ u : T ⟶ fibre K L x, u ≫ toParameter K L x = q) ↔
      coefficientColumn T (fun j =>
        (q ≫ parameterProjection L).appTop
          ((Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j))) ≫
            (AlgebraicGeometry.Grassmannian.pullbackPresentation q (parameterQuotient L)).map = 0 := by
  rw [← ambientMap_factorsThrough_iff_constantColumn_zero K L x
    (q ≫ parameterProjection L) q rfl e]
  constructor
  · rintro ⟨u, hu⟩
    have hp : u ≫ projection K L x = q ≫ parameterProjection L := by
      simpa only [Category.assoc, toParameter_projection] using
        congrArg (fun a => a ≫ parameterProjection L) hu
    refine ⟨u ≫ toFamily K L x, ?_⟩
    simp only [Category.assoc]
    rw [toFamily_inclusion_eq]
    apply pullback.hom_ext
    · simp only [ambientMap_toLG]
      exact congrArg (fun a => a ≫ x) hp
    · simp only [ambientMap_toParameter]
      exact congrArg (parameterMap K L (x ≫ LagrangianGrassmannian.projection K)) hu
  · rintro ⟨z, hz⟩
    have hzx : z ≫ familyToLG K = (q ≫ parameterProjection L) ≫ x := by
      have h := congrArg (fun a => a ≫ toLG K) hz
      simpa only [Category.assoc, familyToLG, ambientMap_toLG] using h
    let u : T ⟶ fibre K L x := pullback.lift z (q ≫ parameterProjection L) hzx
    refine ⟨u, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, toParameter_projection]
      exact pullback.lift_snd _ _ _
    · have hzp : z ≫ familyProjection K =
          parameterMap K L (x ≫ LagrangianGrassmannian.projection K) q := by
        have h := congrArg (fun a => a ≫ LagrangianLinearSections.toParameter K) hz
        simpa only [Category.assoc, familyProjection, ambientMap_toParameter] using h
      simp only [Category.assoc, toParameter_toIntegral]
      rw [← Category.assoc, show u ≫ toFamily K L x = z from pullback.lift_fst _ _ _]
      have hi := congrArg (fun a => a ≫ GrassmannianCharts.toIntegral K 9 14) hzp
      simpa only [familyProjection, Category.assoc, parameterMap_toIntegral] using hi

end M9Native.LagrangianIncidenceFibreQuotient

end
