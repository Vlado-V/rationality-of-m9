module

public import M9StacksIntegration.LagrangianIncidenceFieldFrame

/-!
# The original incidence quotient over an arbitrary field-valued LG point

The two fields are related by the actual scheme morphism on their spectra.
Native quotient classes are retained on arbitrary test schemes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianIncidenceParameterBaseChange

open LagrangianLinearSections LagrangianGrassmannian LagrangianMatrixChart
open LagrangianLinearSectionQuotientCharts LagrangianPluckerTrivialization
open AlgebraicGeometry.Grassmannian

variable (K L : Type u) [Field K] [Field L]

/-- Change only the base component of the actual Grassmannian point. -/
def parameterMap {T : Scheme.{u}} (b : Spec (.of L) ⟶ Spec (.of K))
    (q : T ⟶ parameter L) : T ⟶ parameter K :=
  pullback.lift (q ≫ parameterProjection L ≫ b)
    (q ≫ GrassmannianCharts.toIntegral L 9 14) (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem parameterMap_projection {T : Scheme.{u}}
    (b : Spec (.of L) ⟶ Spec (.of K)) (q : T ⟶ parameter L) :
    parameterMap K L b q ≫ parameterProjection K = q ≫ parameterProjection L ≫ b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem parameterMap_toIntegral {T : Scheme.{u}}
    (b : Spec (.of L) ⟶ Spec (.of K)) (q : T ⟶ parameter L) :
    parameterMap K L b q ≫ GrassmannianCharts.toIntegral K 9 14 =
      q ≫ GrassmannianCharts.toIntegral L 9 14 :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem parameterMap_comp {S T : Scheme.{u}}
    (b : Spec (.of L) ⟶ Spec (.of K)) (q : T ⟶ parameter L) (g : S ⟶ T) :
    g ≫ parameterMap K L b q = parameterMap K L b (g ≫ q) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, parameterMap_projection, parameterMap_toIntegral]

/-- Both genuine universal quotients have literally the same native
representing class; no quotient isomorphism is supplied. -/
theorem parameterMap_class {T : Scheme.{u}}
    (b : Spec (.of L) ⟶ Spec (.of K)) (q : T ⟶ parameter L) :
    (⟦pullbackPresentation (parameterMap K L b q) (parameterQuotient K)⟧ : Points T 9 14) =
      ⟦pullbackPresentation q (parameterQuotient L)⟧ := by
  rw [pullback_parameter_class K, pullback_parameter_class L, parameterMap_toIntegral]

theorem parameterMap_quotient_isomorphic {T : Scheme.{u}}
    (b : Spec (.of L) ⟶ Spec (.of K)) (q : T ⟶ parameter L) :
    (pullbackPresentation (parameterMap K L b q) (parameterQuotient K)).Isomorphic
      (pullbackPresentation q (parameterQuotient L)) :=
  presentation_isomorphic_of_class_eq (parameterMap_class K L b q)

variable (x : Spec (.of L) ⟶ LagrangianGrassmannian.space K)
    {T : Scheme.{u}} (p : T ⟶ Spec (.of L)) (q : T ⟶ parameter L)
    (hq : q ≫ parameterProjection L = p)

/-- The actual ambient point with its actual LG and parameter maps. -/
def ambientMap : T ⟶ ambient K :=
  pullback.lift (p ≫ x) (parameterMap K L (x ≫ LagrangianGrassmannian.projection K) q)
    (by
      rw [parameterMap_projection]
      simpa only [Category.assoc] using
        (congrArg (fun a : T ⟶ Spec (.of L) =>
          a ≫ x ≫ LagrangianGrassmannian.projection K) hq).symm)

@[reassoc (attr := simp)]
theorem ambientMap_toLG : ambientMap K L x p q hq ≫ toLG K = p ≫ x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem ambientMap_toParameter :
    ambientMap K L x p q hq ≫ toParameter K =
      parameterMap K L (x ≫ LagrangianGrassmannian.projection K) q :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem ambientMap_comp {S : Scheme.{u}} (g : S ⟶ T) :
    g ≫ ambientMap K L x p q hq =
      ambientMap K L x (g ≫ p) (g ≫ q)
        (by simpa only [Category.assoc] using congrArg (fun a => g ≫ a) hq) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, ambientMap_toLG, ambientMap_toParameter, parameterMap_comp]

/-- The actual quotient of the original ambient incidence point is the
actual field-base quotient, up to a proved native quotient isomorphism. -/
theorem ambientMap_quotient_isomorphic :
    (pullbackPresentation (ambientMap K L x p q hq) (ambientQuotient K)).Isomorphic
      (pullbackPresentation q (parameterQuotient L)) := by
  apply presentation_isomorphic_of_class_eq
  have hc :
      (⟦pullbackPresentation (ambientMap K L x p q hq) (ambientQuotient K)⟧ : Points T 9 14) =
        ⟦pullbackPresentation (ambientMap K L x p q hq ≫ toParameter K)
          (parameterQuotient K)⟧ :=
    Quotient.sound (.rel _ _ (pullbackPresentation_comp_isomorphic (toParameter K)
      (ambientMap K L x p q hq) (parameterQuotient K)))
  rw [ambientMap_toParameter] at hc
  exact hc.trans (parameterMap_class K L (x ≫ LagrangianGrassmannian.projection K) q)

/-- The line-annihilation condition depends only on the actual native
quotient class, including on nonreduced test schemes. -/
theorem column_comp_eq_zero_iff_of_isomorphic
    {q₁ q₂ : QuotientPresentation T 9 14} (h : q₁.Isomorphic q₂)
    (c : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶ freeOn T 14) :
    c ≫ q₁.map = 0 ↔ c ≫ q₂.map = 0 := by
  obtain ⟨e, he⟩ := h
  constructor
  · intro hc
    rw [← he, ← Category.assoc, hc, zero_comp]
  · intro hc
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc, he, zero_comp] using hc

theorem ambientMap_factorsThrough_iff_constantColumn_zero
    (e : (Scheme.Modules.pullback x).obj (LagrangianPluckerQuotient.determinantLine K) ≅
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf : (Spec (.of L)).Modules)) :
    (∃ z : T ⟶ family K, z ≫ LagrangianLinearSections.inclusion K =
      ambientMap K L x p q hq) ↔
        LagrangianIncidenceFieldFrame.coefficientColumn T (fun j =>
          p.appTop ((Scheme.ΓSpecIso (.of L)).inv
            (LagrangianIncidenceFieldFrame.fieldCoefficients K L x e j))) ≫
              (pullbackPresentation q (parameterQuotient L)).map = 0 :=
  (LagrangianIncidenceFieldFrame.factorsThrough_iff_constantColumn_zero K L x e
    (ambientMap K L x p q hq) p (ambientMap_toLG K L x p q hq)).trans
      (column_comp_eq_zero_iff_of_isomorphic
        (ambientMap_quotient_isomorphic K L x p q hq) _)

end M9Native.LagrangianIncidenceParameterBaseChange

end
