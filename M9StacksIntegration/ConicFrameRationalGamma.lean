module

public import M9StacksIntegration.ConicFrameGammaCongruence
public import M9StacksIntegration.ConicFrameGammaAction
public import M9StacksIntegration.ConicFrameExtension
public import Mathlib.Algebra.MvPolynomial.Funext

/-! The actual native right-frame action, in the named affine matrix
coordinates used by the conic morphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace M9Native.ConicFrameRationalGamma

open ConicFrame ConicFrameProjective ConicFrameCoordinates ConicFrameGammaAction
open M9.ProjectiveFunctionField M9.FrameProjectiveGeometry M9.FrameProjectiveRatios
open M9.ProjectiveGeometry
open Matrix
open scoped BigOperators

abbrev L := rationalField ℂ
abbrev P := polynomial ℂ

def rationalRepresentation : Gamma →* (L ≃ₐ[ℂ] L) :=
  (AlgEquiv.autCongr (functionFieldEquiv 8 0)).toMonoidHom.comp
    (M9.FrameProjectiveGeometry.fieldRepresentation.comp rightEmbedding)

theorem rationalRepresentation_injective : Function.Injective rationalRepresentation :=
  (AlgEquiv.autCongr (functionFieldEquiv 8 0)).injective.comp
    (M9.FrameProjectiveGeometry.fieldRepresentation_injective.comp rightEmbedding_injective)

def genericFrame : Mat3 L := (normalizedFrame ℂ).map (algebraMap P L)

theorem eval_normalizedPolynomial (x : Fin 8 → ℂ) (f : HomogeneousRing) :
    MvPolynomial.eval x (normalizedPolynomial 0 f) =
      MvPolynomial.eval (matrixCoordinates ((normalizedFrame ℂ).map (MvPolynomial.eval x))) f := by
  change MvPolynomial.eval x
      (MvPolynomial.rename (finSuccAboveEquiv 0).symm (Dehomogenization.dehomogenize 0 f)) = _
  rw [MvPolynomial.eval_rename,Dehomogenization.eval_dehomogenize]
  apply congrArg (fun v : Fin 9 → ℂ => MvPolynomial.eval v f)
  funext j
  by_cases hj : j = 0
  · subst j
    simp [Dehomogenization.insertOne,normalizedFrame,matrixCoordinates,matrixIndexEquiv,
      finProdFinEquiv,Fin.divNat,Fin.modNat]
  · obtain ⟨a,ha⟩ := (finSuccAboveEquiv (0 : Fin 9)).surjective ⟨j,hj⟩
    have ha' : (finSuccAboveEquiv 0 a).val = j := congrArg Subtype.val ha
    rw [← ha']
    rw [Dehomogenization.insertOne_of_ne _ _ _ (finSuccAboveEquiv 0 a).property]
    change x ((finSuccAboveEquiv 0).symm (finSuccAboveEquiv 0 a)) = _
    rw [Equiv.symm_apply_apply]
    fin_cases a <;>
      simp [normalizedFrame,matrixCoordinates,matrixIndexEquiv,
        finProdFinEquiv,Fin.divNat,Fin.modNat,finSuccAboveEquiv_apply]

theorem eval_linearForms (B : Matrix9) (v : Fin 9 → ℂ) (j : Fin 9) :
    MvPolynomial.eval v (linearForms B j) = (B *ᵥ v) j := by
  simp [linearForms,Matrix.mulVec,dotProduct]

theorem right_operator (g : Gamma) (F : Mat3 ℂ) :
    M9.FrameAction.tetrahedralRepresentation ((rightEmbedding g)⁻¹) F =
      F * M9.TetrahedralGroup.matrix g := by
  rw [← map_inv]
  change M9.TetrahedralGroup.matrix (1 : Gamma) * F *
      (M9.TetrahedralGroup.matrix g⁻¹).transpose = _
  change (1 : Mat3 ℂ) * F * (M9.TetrahedralGroup.matrix g).transpose.transpose = _
  rw [Matrix.one_mul,Matrix.transpose_transpose]

theorem normalizedLinearForms_right (g : Gamma) (j : Fin 9) :
    normalizedPolynomial 0 (linearForms (matrixRepresentation ((rightEmbedding g)⁻¹)) j) =
      ((normalizedFrame ℂ) * (M9.TetrahedralGroup.matrix g).map (MvPolynomial.C : ℂ →+* P))
        (matrixIndexEquiv.symm j).1 (matrixIndexEquiv.symm j).2 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_normalizedPolynomial,eval_linearForms,
    matrixRepresentation_matrixCoordinates,right_operator]
  change _ = (((normalizedFrame ℂ) *
      (M9.TetrahedralGroup.matrix g).map (MvPolynomial.C : ℂ →+* P)).map (MvPolynomial.eval x))
        (matrixIndexEquiv.symm j).1 (matrixIndexEquiv.symm j).2
  rw [Matrix.map_mul,Matrix.map_map]
  have hmap : (M9.TetrahedralGroup.matrix g).map
      (⇑(MvPolynomial.eval x) ∘ ⇑(MvPolynomial.C : ℂ →+* P)) =
      M9.TetrahedralGroup.matrix g := by
    ext a b
    simp
  rw [hmap]
  rfl

theorem rationalRepresentation_X (g : Gamma) (a : Fin 8) :
    rationalRepresentation g (algebraMap P L (MvPolynomial.X a)) =
      algebraMap P L
        (((normalizedFrame ℂ) * (M9.TetrahedralGroup.matrix g).map (MvPolynomial.C : ℂ →+* P))
          (matrixIndexEquiv.symm (finSuccAboveEquiv 0 a)).1
          (matrixIndexEquiv.symm (finSuccAboveEquiv 0 a)).2) /
      algebraMap P L
        (((normalizedFrame ℂ) * (M9.TetrahedralGroup.matrix g).map (MvPolynomial.C : ℂ →+* P)) 0 0) := by
  change functionFieldEquiv 8 0
    (M9.FrameProjectiveGeometry.fieldRepresentation (rightEmbedding g)
      ((functionFieldEquiv 8 0).symm (algebraMap P L (MvPolynomial.X a)))) = _
  rw [fieldRepresentation_normalized,normalizedLinearForms_right,normalizedLinearForms_right]
  rfl

end M9Native.ConicFrameRationalGamma
