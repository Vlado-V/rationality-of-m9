module

public import M9StacksIntegration.ConicPairBaseEmbedding
public import M9StacksIntegration.ConicGraphCoefficientDescent
public import M9StacksIntegration.RationalMatrixGaugeCoefficients
public import M9StacksIntegration.ConicPairCompensatorAction

/-! The literal moving-frame embedding of the actual graph coordinate field
into the original independent frame-pair field with sixteen raw Hom variables.
The image and induced deck action are proved from the actual base-cover
inclusion and actual compensators, without a bundle-field identification
premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open MvPolynomial Matrix
open scoped Classical

namespace M9Native.ConicFramedGraphField

open M9.GraphBundleDescent ConicPairMovingFrames

abbrev G := ConicGraphCoefficientDescent.G
abbrev M := ConicGraphCoefficientDescent.M
abbrev P := MvPolynomial FiberIndex B
abbrev FF := ChartFunctionField ℂ

attribute [local instance] ConicGraphCoefficientDescent.frameAction

/-- Canonical coefficient field automorphisms of the original sixteen
independent fibre variables. -/
def coefficientEquiv (g : G) : M ≃ₐ[ℂ] M :=
  M9.ProjectiveNoName.rationalCoefficientEquiv ℂ FiberIndex
    (ConicGraphCoefficientDescent.frameRepresentation g)

theorem coefficientEquiv_constant (g : G) (b : B) :
    coefficientEquiv g (algebraMap B M b) =
      algebraMap B M (ConicGraphCoefficientDescent.frameRepresentation g b) :=
  M9.ProjectiveNoName.rationalCoefficientEquiv_coefficient ℂ FiberIndex _ b

theorem coefficientEquiv_variable (g : G) (ij : FiberIndex) :
    coefficientEquiv g (algebraMap P M (X ij)) = algebraMap P M (X ij) :=
  M9.ProjectiveNoName.rationalCoefficientEquiv_variable ℂ FiberIndex _ ij

theorem coefficientEquiv_apply (g : G) (f : M) :
    coefficientEquiv g f = ConicGraphCoefficientDescent.coefficientTranslate g f := by
  have hh : (coefficientEquiv g).toRingHom = ConicGraphCoefficientDescent.coefficientTranslate g := by
    apply IsFractionRing.ringHom_ext (A := P)
    intro p
    have h := M9.FiniteNoNameField.rationalAction_polynomial G B FiberIndex g p
    change ConicGraphCoefficientDescent.coefficientTranslate g (algebraMap P M p) =
      algebraMap P M (MvPolynomial.map
        (ConicGraphCoefficientDescent.frameRepresentation g).toRingHom p) at h
    have hc := IsFractionRing.algEquivOfAlgEquiv_algebraMap (K := M) (L := M)
      (MvPolynomial.mapAlgEquiv FiberIndex (ConicGraphCoefficientDescent.frameRepresentation g)) p
    exact hc.trans h.symm
  exact RingHom.congr_fun hh f

def coefficientRepresentation : G →* (M ≃ₐ[ℂ] M) where
  toFun := coefficientEquiv
  map_one' := by
    have hh : (coefficientEquiv (1 : G)).toRingHom = (AlgEquiv.refl : M ≃ₐ[ℂ] M).toRingHom := by
      apply M9.ProjectiveNoName.rationalRingHom_ext B FiberIndex
      · intro b
        change coefficientEquiv 1 (algebraMap B M b) = algebraMap B M b
        rw [coefficientEquiv_constant, map_one]
        rfl
      · intro ij
        exact coefficientEquiv_variable 1 ij
    exact AlgEquiv.ext (fun f => RingHom.congr_fun hh f)
  map_mul' g h := by
    have hh : (coefficientEquiv (g*h)).toRingHom =
        (coefficientEquiv g).toRingHom.comp (coefficientEquiv h).toRingHom := by
      apply M9.ProjectiveNoName.rationalRingHom_ext B FiberIndex
      · intro b
        change coefficientEquiv (g*h) (algebraMap B M b) =
          coefficientEquiv g (coefficientEquiv h (algebraMap B M b))
        rw [coefficientEquiv_constant, coefficientEquiv_constant, coefficientEquiv_constant, map_mul]
        rfl
      · intro ij
        change coefficientEquiv (g*h) (algebraMap P M (X ij)) =
          coefficientEquiv g (coefficientEquiv h (algebraMap P M (X ij)))
        rw [coefficientEquiv_variable, coefficientEquiv_variable, coefficientEquiv_variable]
    exact AlgEquiv.ext (fun f => RingHom.congr_fun hh f)

/-- The explicit matrix substitution supplied by the actual two moving
determinant-tensor frames. -/
def movingGauge : M ≃ₐ[ℂ] M :=
  (RationalMatrixGauge.fieldEquiv B (Fin 4) (compensatedFrame 1) (compensatedFrame 0)⁻¹).restrictScalars ℂ

def embedding : FF →ₐ[ℂ] M :=
  movingGauge.toAlgHom.comp ConicGraphCoefficientDescent.chartEmbedding

def genericRawMatrix : FiberMatrix M := RationalMatrixGauge.rationalMatrix B (Fin 4)

theorem movingGauge_constant (b : B) : movingGauge (algebraMap B M b) = algebraMap B M b :=
  (RationalMatrixGauge.fieldEquiv B (Fin 4) (compensatedFrame 1) (compensatedFrame 0)⁻¹).commutes b

theorem embedding_base (s : Fin 2) (i : Fin 2) (j : Fin 4) :
    embedding (algebraMap (ChartRing ℂ) FF (X (.inl (s,i,j)))) =
      algebraMap B M (planeMatrix s i j) := by
  change movingGauge (ConicGraphCoefficientDescent.chartEmbedding _) = _
  rw [ConicGraphCoefficientDescent.chartEmbedding_base,
    ConicPairBaseEmbedding.baseEmbedding_entry, movingGauge_constant]

theorem embedding_fiber (i j : Fin 4) :
    embedding (algebraMap (ChartRing ℂ) FF (X (.inr (i,j)))) =
      ((compensatedFrame 1).val.map (algebraMap B M) * genericRawMatrix *
        ((compensatedFrame 0)⁻¹).val.map (algebraMap B M)) i j := by
  change movingGauge (ConicGraphCoefficientDescent.chartEmbedding _) = _
  rw [ConicGraphCoefficientDescent.chartEmbedding_fiber]
  exact RationalMatrixGauge.fieldEquiv_variable B (Fin 4) (compensatedFrame 1)
    (compensatedFrame 0)⁻¹ i j

/-- Genuine deck action induced through the explicit actual moving
matrices; its literal raw-Hom generator formula is proved separately. -/
def inducedRepresentation : G →* (M ≃ₐ[ℂ] M) :=
  (AlgEquiv.autCongr movingGauge).toMonoidHom.comp coefficientRepresentation

theorem inducedRepresentation_gauge (g : G) (f : M) :
    inducedRepresentation g (movingGauge f) = movingGauge (coefficientEquiv g f) := by
  change movingGauge (coefficientEquiv g (movingGauge.symm (movingGauge f))) = _
  exact congrArg (fun z => movingGauge (coefficientEquiv g z)) (movingGauge.symm_apply_apply f)

/-- Exact image of the literal moving-frame inclusion. -/
theorem embedding_image_iff (f : M) :
    (∃ x : FF, embedding x = f) ↔ ∀ g : G, inducedRepresentation g f = f := by
  constructor
  · rintro ⟨x,rfl⟩ g
    have hx := (ConicGraphCoefficientDescent.chartEmbedding_image_iff
      (ConicGraphCoefficientDescent.chartEmbedding x)).mp ⟨x,rfl⟩ g
    change inducedRepresentation g (movingGauge (ConicGraphCoefficientDescent.chartEmbedding x)) = _
    rw [inducedRepresentation_gauge, coefficientEquiv_apply, hx]
    rfl
  · intro hf
    have hc : ∀ g : G, ConicGraphCoefficientDescent.coefficientTranslate g (movingGauge.symm f) =
        movingGauge.symm f := by
      intro g
      apply movingGauge.injective
      calc
        movingGauge (ConicGraphCoefficientDescent.coefficientTranslate g (movingGauge.symm f)) =
            movingGauge (coefficientEquiv g (movingGauge.symm f)) :=
          congrArg movingGauge (coefficientEquiv_apply g (movingGauge.symm f)).symm
        _ = inducedRepresentation g (movingGauge (movingGauge.symm f)) :=
          (inducedRepresentation_gauge g (movingGauge.symm f)).symm
        _ = inducedRepresentation g f := congrArg (inducedRepresentation g) (movingGauge.apply_symm_apply f)
        _ = f := hf g
        _ = movingGauge (movingGauge.symm f) := (movingGauge.apply_symm_apply f).symm
    obtain ⟨x,hx⟩ := (ConicGraphCoefficientDescent.chartEmbedding_image_iff (movingGauge.symm f)).mpr hc
    refine ⟨x, ?_⟩
    exact (congrArg movingGauge hx).trans (movingGauge.apply_symm_apply f)

end M9Native.ConicFramedGraphField
