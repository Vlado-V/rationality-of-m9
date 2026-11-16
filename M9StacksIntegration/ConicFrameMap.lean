module

public import M9StacksIntegration.ConicFramePolynomial
public import M9StacksIntegration.GrassmannianCharts

/-!
# The genuine Grassmannian morphism of an invertible ternary frame

Adjugate congruence gives a polynomial rank-two quotient of the trivial
rank-six bundle. Its explicit splitting constructs a quotient presentation
on any scheme carrying an invertible frame. Native Grassmannian
representability then supplies the classifying morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.ConicFrame

open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix

variable (T : Scheme.{u})

/-- The literal polynomial quotient map of free sheaves. -/
def sheafQuotient (F : Mat3 Γ(T, ⊤)) :
    Stacks.FreeSheafMatrix.F T 6 ⟶ Stacks.FreeSheafMatrix.F T 2 :=
  ofMatrix (quotientMatrix F)

/-- The splitting is a map of the actual free sheaves. -/
def sheafSection (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    Stacks.FreeSheafMatrix.F T 2 ⟶ Stacks.FreeSheafMatrix.F T 6 :=
  ofMatrix (quotientSection F hF)

theorem sheafSection_quotient (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    sheafSection T F hF ≫ sheafQuotient T F = 𝟙 _ := by
  apply toMatrix_injective
  rw [toMatrix_comp]
  simp only [sheafSection,sheafQuotient,toMatrix_ofMatrix,toMatrix_id,
    quotientMatrix_section]

theorem sheafQuotient_epi (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    Epi (sheafQuotient T F) := by
  have : Epi (sheafSection T F hF ≫ sheafQuotient T F) := by
    rw [sheafSection_quotient T F hF]
    infer_instance
  exact epi_of_epi (sheafSection T F hF) (sheafQuotient T F)

/-- A genuine quotient presentation, with surjectivity proved by its splitting. -/
def presentation (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    QuotientPresentation T 4 6 where
  target := Stacks.FreeSheafMatrix.F T 2
  map := sheafQuotient T F
  map_epi := sheafQuotient_epi T F hF
  finiteLocallyFree := free_isFiniteLocallyFreeOfRank T 2

/-- The representing morphism into the native integral Grassmannian. -/
def integralMap (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) : T ⟶ scheme.{u} 4 6 :=
  (schemeRepresentableBy 4 6).homEquiv.symm
    (((functorData 4 6).objEquiv T).symm ⟦presentation T F hF⟧)

/-- The classifying property is the actual native quotient-class equivalence. -/
theorem integralMap_class (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    (functorData 4 6).objEquiv T
      ((schemeRepresentableBy 4 6).homEquiv (integralMap T F hF)) =
      ⟦presentation T F hF⟧ := by
  simp only [integralMap,Equiv.apply_symm_apply]

/-- Multiplication by a unit is an actual automorphism of the free quotient bundle. -/
def sheafScalarIso (c : Γ(T, ⊤)ˣ) :
    Stacks.FreeSheafMatrix.F T 2 ≅ Stacks.FreeSheafMatrix.F T 2 where
  hom := ofMatrix ((c : Γ(T, ⊤)) • (1 : Matrix (Fin 2) (Fin 2) Γ(T, ⊤)))
  inv := ofMatrix ((↑c⁻¹ : Γ(T, ⊤)) • (1 : Matrix (Fin 2) (Fin 2) Γ(T, ⊤)))
  hom_inv_id := by
    apply toMatrix_injective
    rw [toMatrix_comp,toMatrix_ofMatrix,toMatrix_ofMatrix,toMatrix_id,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul,
      Units.inv_mul,one_smul]
  inv_hom_id := by
    apply toMatrix_injective
    rw [toMatrix_comp,toMatrix_ofMatrix,toMatrix_ofMatrix,toMatrix_id,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul,
      Units.mul_inv,one_smul]

/-- The degree-four scalar factor changes the quotient only by a target isomorphism. -/
theorem presentation_smul_isomorphic (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det)
    (c : Γ(T, ⊤)ˣ) (hF' : IsUnit (((c : Γ(T, ⊤)) • F).det)) :
    (presentation T F hF).Isomorphic (presentation T ((c : Γ(T, ⊤)) • F) hF') := by
  refine ⟨sheafScalarIso T (c ^ 4),?_⟩
  apply toMatrix_injective
  rw [toMatrix_comp]
  simp only [presentation,sheafQuotient,sheafScalarIso,toMatrix_ofMatrix,
    Units.val_pow_eq_pow_val,Matrix.smul_mul,Matrix.one_mul,quotientMatrix_smul]

/-- Scalar compatibility holds as an equality of genuine scheme morphisms. -/
theorem integralMap_smul (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det)
    (c : Γ(T, ⊤)ˣ) (hF' : IsUnit (((c : Γ(T, ⊤)) • F).det)) :
    integralMap T F hF = integralMap T ((c : Γ(T, ⊤)) • F) hF' := by
  apply (schemeRepresentableBy 4 6).homEquiv.injective
  apply ((functorData 4 6).objEquiv T).injective
  rw [integralMap_class,integralMap_class]
  exact Quotient.sound (.rel _ _ (presentation_smul_isomorphic T F hF c hF'))

variable (K : Type u) [Field K]

/-- The same classifying morphism, genuinely base changed over the given field. -/
def map (p : T ⟶ Spec (.of K)) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    T ⟶ GrassmannianCharts.space K 4 6 :=
  pullback.lift p (integralMap T F hF) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem map_projection
    (p : T ⟶ Spec (.of K)) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    map T K p F hF ≫ GrassmannianCharts.projection K 4 6 = p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem map_toIntegral
    (p : T ⟶ Spec (.of K)) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det) :
    map T K p F hF ≫ GrassmannianCharts.toIntegral K 4 6 = integralMap T F hF :=
  pullback.lift_snd _ _ _

theorem map_smul (p : T ⟶ Spec (.of K)) (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det)
    (c : Γ(T, ⊤)ˣ) (hF' : IsUnit (((c : Γ(T, ⊤)) • F).det)) :
    map T K p F hF = map T K p ((c : Γ(T, ⊤)) • F) hF' := by
  apply pullback.hom_ext
  · simp only [map_projection]
  · simp only [map_toIntegral]
    exact integralMap_smul T F hF c hF'

end M9Native.ConicFrame
