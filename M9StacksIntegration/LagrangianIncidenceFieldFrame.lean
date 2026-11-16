module

public import M9StacksIntegration.LagrangianIncidenceLineEvaluation

/-!
# Genuine constant Pluecker coefficients in an incidence fibre

At every field-valued LG point an actual determinant frame exists, and
its actual fourteen coefficients are nonzero.  Their pullbacks are the
literal scalar coefficients on every test scheme of the incidence fibre.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianIncidenceFieldFrame

open LagrangianLinearSections LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianLinearSectionLineCharts LagrangianIncidenceLineEvaluation
open LinearIncidenceTensorCoordinates LineFramePullback

/-- The actual native unit-to-free-module column with the specified
global coefficients. -/
def coefficientColumn (T : Scheme.{u}) (c : Fin 14 → Γ(T, ⊤)) :
    (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶ LagrangianMatrixChart.freeOn T 14 :=
  Scheme.Modules.unitHomEquivTop _ (coefficientVector T c)

theorem coefficientColumn_top_one (T : Scheme.{u}) (c : Fin 14 → Γ(T, ⊤)) :
    Scheme.Modules.Hom.app (X := T) (coefficientColumn T c) ⊤
      (1 : Γ(T, ⊤)) = coefficientVector T c :=
  LagrangianAffineDeterminant.unitHom_top_one _ _

theorem coefficientColumn_comp_eq_zero_iff {T : Scheme.{u}}
    (c : Fin 14 → Γ(T, ⊤)) {Q : T.Modules}
    (q : LagrangianMatrixChart.freeOn T 14 ⟶ Q) :
    coefficientColumn T c ≫ q = 0 ↔ q.app ⊤ (coefficientVector T c) = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun a : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶ Q =>
      Scheme.Modules.Hom.app (X := T) a ⊤ (1 : Γ(T, ⊤))) h
    change q.app ⊤ (Scheme.Modules.Hom.app (X := T)
      (coefficientColumn T c) ⊤ (1 : Γ(T, ⊤))) = 0 at h'
    rwa [coefficientColumn_top_one] at h'
  · intro h
    apply LagrangianSectionGeneration.unitHom_ext_top_one Q
    change q.app ⊤ (Scheme.Modules.Hom.app (X := T)
      (coefficientColumn T c) ⊤ (1 : Γ(T, ⊤))) = 0
    rwa [coefficientColumn_top_one]

variable (K : Type u) [Field K] (L : Type u) [Field L]
    (x : Spec (.of L) ⟶ LagrangianGrassmannian.space K)

/-- The actual fourteen coefficients in an actual field-point frame. -/
def fieldCoefficients
    (e : (Scheme.Modules.pullback x).obj (determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules)) :
    Fin 14 → L := fun j =>
  (Scheme.ΓSpecIso (.of L)).hom
    (unitCoordinate (Spec (.of L)) (e.hom.app ⊤
      (pullbackGlobalSections x (determinantLine K) (primitiveSections K j))))

theorem scalar_fieldCoefficients
    (e : (Scheme.Modules.pullback x).obj (determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules))
    (j : Fin 14) :
    (Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j) =
      unitCoordinate (Spec (.of L)) (e.hom.app ⊤
        (pullbackGlobalSections x (determinantLine K) (primitiveSections K j))) :=
  (Scheme.ΓSpecIso (.of L)).hom_inv_id_apply _

/-- The actual primitive Pluecker system supplies a frame with a genuinely
nonzero scalar coefficient vector, over every field-valued point. -/
theorem exists_frame_coefficients_ne_zero [CharZero K] :
    ∃ e : (Scheme.Modules.pullback x).obj (determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules),
        fieldCoefficients K L x e ≠ 0 := by
  obtain ⟨ι, g, hg⟩ := LagrangianIncidenceFieldPoints.exists_integralChart_factor L
    ((x ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _)
  let e := lineTrivialization K x ι g hg
  refine ⟨e, ?_⟩
  have hc : fieldCoefficients K L x e =
      LagrangianFieldCoordinates.values L (LagrangianPlucker.chartCoordinates K x ι g) := by
    funext j
    exact congrArg (fun z => (Scheme.ΓSpecIso (.of L)).hom z)
      (lineTrivialization_sections K x ι g hg j)
  rw [hc]
  exact LagrangianFieldCoordinates.values_ne_zero L _
    (LagrangianPlucker.chartCoordinates_span K x ι g hg)

variable
    (e : (Scheme.Modules.pullback x).obj (determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules))
    {T : Scheme.{u}} (f : T ⟶ ambient K) (p : T ⟶ Spec (.of L))
    (h : f ≫ toLG K = p ≫ x)

/-- Pull the actual field-point frame around the actual incidence square. -/
def constantFrame :
    (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (SheafOfModules.unit T.ringCatSheaf : T.Modules) :=
  squareFrame f (toLG K) p x h (determinantLine K) e

theorem constantFrame_coefficients (j : Fin 14) :
    LagrangianLinearSectionEquations.lineCoefficients K f
      (constantFrame K L x e f p h) j =
        p.appTop ((Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j)) := by
  rw [scalar_fieldCoefficients]
  exact squareFrame_coordinate f (toLG K) p x h (determinantLine K) e (primitiveSections K j)

include h

/-- Scheme-theoretic factorization through the original incidence ideal is
annihilation of the genuine constant Pluecker vector.  There is no affine,
reduced, or quotient-frame hypothesis on the test scheme. -/
theorem factorsThrough_iff_constant_evaluation_zero :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f) ↔
      Scheme.Modules.Hom.app (X := T)
        (AlgebraicGeometry.Grassmannian.pullbackPresentation f (ambientQuotient K)).map ⊤
        (coefficientVector T (fun j =>
          p.appTop ((Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j)))) = 0 := by
  rw [factorsThrough_iff_evaluation_zero K f (constantFrame K L x e f p h)]
  rw [show LagrangianLinearSectionEquations.lineCoefficients K f
      (constantFrame K L x e f p h) = fun j =>
        p.appTop ((Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j)) from
      funext (constantFrame_coefficients K L x e f p h)]

theorem factorsThrough_iff_constantColumn_zero :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f) ↔
      coefficientColumn T (fun j =>
        p.appTop ((Scheme.ΓSpecIso (.of L)).inv (fieldCoefficients K L x e j))) ≫
          (AlgebraicGeometry.Grassmannian.pullbackPresentation f (ambientQuotient K)).map = 0 :=
  (factorsThrough_iff_constant_evaluation_zero K L x e f p h).trans
    (coefficientColumn_comp_eq_zero_iff _ _).symm

end M9Native.LagrangianIncidenceFieldFrame

end
