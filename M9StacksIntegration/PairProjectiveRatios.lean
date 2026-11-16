module

public import M9StacksIntegration.ConicFrameIndependentPairAction
public import M9.ProjectiveFrameQuotient

/-! The nested independent rational coordinates are the actual ratio field
of the two original matrix frames. The comparison uses the real ratio
embeddings twice, and proves equality with the existing adjoin-defined
projective pair field. Both normalizations use the original (0,0) entry. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000

namespace M9Native.PairProjectiveRatios

open MvPolynomial
open M9.ProjectiveNoName
open M9.FrameFieldElimination
open ConicFrameIndependentPairAction

attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Index := ConicFrameIndependentPairAction.Index
abbrev PairField := ConicFrameIndependentPairAction.PairField
abbrev RawIndex := Fin 3 × Fin 3
abbrev RawField (K : Type*) [Field K] := FractionRing (MvPolynomial RawIndex K)
abbrev MF := M9.ProjectiveFrameQuotient.MF
abbrev PF := M9.ProjectiveFrameQuotient.PF
abbrev Target := M9.ProjectiveFrameQuotient.projectivePairField

def affinePosition (i : Index) : RawIndex := finProdFinEquiv.symm i.succ

def frameIndex : Index ⊕ Unit → RawIndex
  | .inl i => affinePosition i
  | .inr _ => (0,0)

theorem frameIndex_bijective : Function.Bijective frameIndex := by decide

def frameIndexEquiv : (Index ⊕ Unit) ≃ RawIndex :=
  Equiv.ofBijective frameIndex frameIndex_bijective

@[simp] theorem frameIndexEquiv_inl (i : Index) :
    frameIndexEquiv (.inl i) = affinePosition i := rfl

@[simp] theorem frameIndexEquiv_inr :
    frameIndexEquiv (.inr ()) = (0,0) := rfl

def homogeneousReindex (K : Type*) [Field K] :
    HomogeneousRational K Index ≃ₐ[K] RawField K :=
  M9.rationalFieldReindex K frameIndexEquiv

/-- The original chart00 ratio map for one actual nine-coordinate frame. -/
def singleRatioEmbedding (K : Type*) [Field K] :
    Rational K Index →ₐ[K] RawField K :=
  (homogeneousReindex K).toAlgHom.comp (ratioEmbedding K Index)

theorem singleRatioEmbedding_variable (K : Type*) [Field K] (i : Index) :
    singleRatioEmbedding K
        (algebraMap (MvPolynomial Index K) (Rational K Index) (X i)) =
      algebraMap (MvPolynomial RawIndex K) (RawField K) (X (affinePosition i)) /
        algebraMap (MvPolynomial RawIndex K) (RawField K) (X (0,0)) := by
  rw [singleRatioEmbedding,AlgHom.comp_apply,ratioEmbedding_variable,map_div₀,
    homogeneousReindex]
  change M9.rationalFieldReindex K frameIndexEquiv
      (algebraMap (MvPolynomial (Index ⊕ Unit) K) (FractionRing (MvPolynomial (Index ⊕ Unit) K))
        (X (.inl i))) /
    M9.rationalFieldReindex K frameIndexEquiv
      (algebraMap (MvPolynomial (Index ⊕ Unit) K) (FractionRing (MvPolynomial (Index ⊕ Unit) K))
        (X (.inr ()))) = _
  rw [M9.rationalFieldReindex_algebraMap,M9.rationalFieldReindex_algebraMap]
  simp only [MvPolynomial.rename_X,frameIndexEquiv_inl,frameIndexEquiv_inr]

section CoefficientExtension

variable {E F : Type*} [Field E] [Field F] [Algebra ℂ E] [Algebra ℂ F]

/-- The actual coefficient-field extension for an injective field map.
The scalar tower is attached to that precise homomorphism. -/
def extendCoefficients (f : E →ₐ[ℂ] F) :
    Rational E Index →ₐ[ℂ] Rational F Index := by
  letI : Algebra E F := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ E F := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact (coefficientExtend E Index F).restrictScalars ℂ

theorem extendCoefficients_coefficient (f : E →ₐ[ℂ] F) (x : E) :
    extendCoefficients f (algebraMap E (Rational E Index) x) =
      algebraMap F (Rational F Index) (f x) := by
  letI : Algebra E F := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ E F := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  change coefficientExtend E Index F (algebraMap E (Rational E Index) x) = _
  rw [AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply E F (Rational F Index) x

theorem extendCoefficients_variable (f : E →ₐ[ℂ] F) (i : Index) :
    extendCoefficients f
        (algebraMap (MvPolynomial Index E) (Rational E Index) (X i)) =
      algebraMap (MvPolynomial Index F) (Rational F Index) (X i) := by
  letI : Algebra E F := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ E F := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact coefficientExtend_variable E Index F i

end CoefficientExtension

def firstProjectiveEmbedding : OneField →ₐ[ℂ] PF :=
  (IsScalarTower.toAlgHom ℂ MF PF).comp (singleRatioEmbedding ℂ)

/-- Two actual ratio embeddings into the two original independent frames. -/
def pairRatioEmbedding : PairField →ₐ[ℂ] PF :=
  ((singleRatioEmbedding MF).restrictScalars ℂ).comp
    (extendCoefficients (singleRatioEmbedding ℂ))

theorem pairRatioEmbedding_coefficient (x : OneField) :
    pairRatioEmbedding (coefficientEmbedding x) = firstProjectiveEmbedding x := by
  change singleRatioEmbedding MF
      (extendCoefficients (singleRatioEmbedding ℂ) (algebraMap OneField PairField x)) = _
  rw [extendCoefficients_coefficient,AlgHom.commutes]
  rfl

theorem firstProjectiveEmbedding_variable (i : Index) :
    firstProjectiveEmbedding (oneVariable i) =
      firstFrame ℂ (affinePosition i).1 (affinePosition i).2 / firstFrame ℂ 0 0 := by
  change algebraMap MF PF (singleRatioEmbedding ℂ
      (algebraMap (MvPolynomial Index ℂ) (Rational ℂ Index) (X i))) =
    algebraMap MF PF (algebraMap (MvPolynomial RawIndex ℂ) MF (X (affinePosition i))) /
      algebraMap MF PF (algebraMap (MvPolynomial RawIndex ℂ) MF (X (0,0)))
  rw [singleRatioEmbedding_variable]
  exact map_div₀ (algebraMap MF PF) _ _

theorem pairRatioEmbedding_firstVariable (i : Index) :
    pairRatioEmbedding (coefficientEmbedding (oneVariable i)) =
      firstFrame ℂ (affinePosition i).1 (affinePosition i).2 / firstFrame ℂ 0 0 := by
  rw [pairRatioEmbedding_coefficient,firstProjectiveEmbedding_variable]

theorem pairRatioEmbedding_secondVariable (i : Index) :
    pairRatioEmbedding (outerVariable i) =
      secondFrame ℂ (affinePosition i).1 (affinePosition i).2 / secondFrame ℂ 0 0 := by
  change singleRatioEmbedding MF
      (extendCoefficients (singleRatioEmbedding ℂ)
        (algebraMap (MvPolynomial Index OneField) PairField (X i))) = _
  rw [extendCoefficients_variable,singleRatioEmbedding_variable]
  rfl

theorem firstFrame_ne_zero (ij : RawIndex) : firstFrame ℂ ij.1 ij.2 ≠ 0 := by
  change algebraMap MF PF (algebraMap (MvPolynomial RawIndex ℂ) MF (X ij)) ≠ 0
  have hx : algebraMap (MvPolynomial RawIndex ℂ) MF (X ij) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial RawIndex ℂ) MF).ne (MvPolynomial.X_ne_zero ij)
  simpa only [map_zero] using (algebraMap MF PF).injective.ne hx

theorem secondFrame_ne_zero (ij : RawIndex) : secondFrame ℂ ij.1 ij.2 ≠ 0 := by
  change algebraMap (MvPolynomial RawIndex MF) PF (X ij) ≠ 0
  simpa only [map_zero] using
    (IsFractionRing.injective (MvPolynomial RawIndex MF) PF).ne (MvPolynomial.X_ne_zero ij)

theorem firstChartRatio_mem (ij : RawIndex) :
    firstFrame ℂ ij.1 ij.2 / firstFrame ℂ 0 0 ∈ Target := by
  have hh := Target.div_mem (M9.ProjectiveFrameQuotient.firstRatio_mem ij)
    (M9.ProjectiveFrameQuotient.firstRatio_mem (0,0))
  rw [div_div_div_cancel_right₀ M9.ProjectiveFrameQuotient.firstPivot_ne_zero] at hh
  exact hh

theorem secondChartRatio_mem (ij : RawIndex) :
    secondFrame ℂ ij.1 ij.2 / secondFrame ℂ 0 0 ∈ Target := by
  have hh := Target.div_mem (M9.ProjectiveFrameQuotient.secondRatio_mem ij)
    (M9.ProjectiveFrameQuotient.secondRatio_mem (0,0))
  rw [div_div_div_cancel_right₀ M9.ProjectiveFrameQuotient.secondPivot_ne_zero] at hh
  exact hh

theorem firstProjectiveEmbedding_mem (x : OneField) : firstProjectiveEmbedding x ∈ Target := by
  apply M9.ProjectiveFrameQuotient.rationalMap_mem Target firstProjectiveEmbedding
  · intro i
    change firstProjectiveEmbedding (oneVariable i) ∈ Target
    rw [firstProjectiveEmbedding_variable]
    exact firstChartRatio_mem _

theorem pairRatioEmbedding_mem (z : PairField) : pairRatioEmbedding z ∈ Target := by
  have hp : ∀ p : MvPolynomial Index OneField,
      pairRatioEmbedding (algebraMap (MvPolynomial Index OneField) PairField p) ∈ Target := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      change pairRatioEmbedding (coefficientEmbedding c) ∈ Target
      rw [pairRatioEmbedding_coefficient]
      exact firstProjectiveEmbedding_mem c
    | add p q hp hq =>
      rw [map_add,map_add]
      exact Target.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul,map_mul]
      apply Target.mul_mem hp
      change pairRatioEmbedding (outerVariable i) ∈ Target
      rw [pairRatioEmbedding_secondVariable]
      exact secondChartRatio_mem _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial Index OneField) z
  rw [map_div₀]
  exact Target.div_mem (hp p) (hp q)

theorem pairRange_le : pairRatioEmbedding.fieldRange ≤ Target := by
  rintro _ ⟨z,rfl⟩
  exact pairRatioEmbedding_mem z

theorem firstChartRatio_mem_range (ij : RawIndex) :
    firstFrame ℂ ij.1 ij.2 / firstFrame ℂ 0 0 ∈ pairRatioEmbedding.fieldRange := by
  obtain ⟨s,rfl⟩ := frameIndexEquiv.surjective ij
  rcases s with i | ⟨⟩
  · exact ⟨coefficientEmbedding (oneVariable i),pairRatioEmbedding_firstVariable i⟩
  · change firstFrame ℂ 0 0 / firstFrame ℂ 0 0 ∈ _
    rw [div_self (firstFrame_ne_zero (0,0))]
    exact pairRatioEmbedding.fieldRange.one_mem

theorem secondChartRatio_mem_range (ij : RawIndex) :
    secondFrame ℂ ij.1 ij.2 / secondFrame ℂ 0 0 ∈ pairRatioEmbedding.fieldRange := by
  obtain ⟨s,rfl⟩ := frameIndexEquiv.surjective ij
  rcases s with i | ⟨⟩
  · exact ⟨outerVariable i,pairRatioEmbedding_secondVariable i⟩
  · change secondFrame ℂ 0 0 / secondFrame ℂ 0 0 ∈ _
    rw [div_self (secondFrame_ne_zero (0,0))]
    exact pairRatioEmbedding.fieldRange.one_mem

theorem projectivePair_le_range : Target ≤ pairRatioEmbedding.fieldRange := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ (⟨ij,rfl⟩ | ⟨ij,rfl⟩)
  · have hh := pairRatioEmbedding.fieldRange.div_mem (firstChartRatio_mem_range ij)
      (firstChartRatio_mem_range M9.ProjectiveFrameQuotient.pivotIndex)
    rw [div_div_div_cancel_right₀ (firstFrame_ne_zero (0,0))] at hh
    exact hh
  · have hh := pairRatioEmbedding.fieldRange.div_mem (secondChartRatio_mem_range ij)
      (secondChartRatio_mem_range M9.ProjectiveFrameQuotient.pivotIndex)
    rw [div_div_div_cancel_right₀ (secondFrame_ne_zero (0,0))] at hh
    exact hh

/-- The constructed map has exactly the existing adjoin-defined
projective pair field as its range; the two field models were not assumed
to be isomorphic. -/
theorem pairRatioEmbedding_fieldRange : pairRatioEmbedding.fieldRange = Target :=
  le_antisymm pairRange_le projectivePair_le_range

def intoProjectivePair : PairField →ₐ[ℂ] Target where
  toFun z := ⟨pairRatioEmbedding z,pairRatioEmbedding_mem z⟩
  map_one' := Subtype.ext pairRatioEmbedding.map_one
  map_zero' := Subtype.ext pairRatioEmbedding.map_zero
  map_add' x y := Subtype.ext (pairRatioEmbedding.map_add x y)
  map_mul' x y := Subtype.ext (pairRatioEmbedding.map_mul x y)
  commutes' c := Subtype.ext (pairRatioEmbedding.commutes c)

/-- The actual nested8,8 rational field is isomorphic over the original
complex scalars to the original projective pair-ratio field. -/
def pairProjectiveEquiv : PairField ≃ₐ[ℂ] Target :=
  AlgEquiv.ofBijective intoProjectivePair ⟨intoProjectivePair.injective,by
    intro x
    have hx : (x : PF) ∈ pairRatioEmbedding.fieldRange := by
      rw [pairRatioEmbedding_fieldRange]
      exact x.property
    obtain ⟨z,hz⟩ := hx
    exact ⟨z,Subtype.ext hz⟩⟩

@[simp] theorem pairProjectiveEquiv_coe (z : PairField) :
    (pairProjectiveEquiv z : PF) = pairRatioEmbedding z := rfl

@[simp] theorem pairProjectiveEquiv_firstVariable (i : Index) :
    (pairProjectiveEquiv (coefficientEmbedding (oneVariable i)) : PF) =
      firstFrame ℂ (affinePosition i).1 (affinePosition i).2 / firstFrame ℂ 0 0 :=
  pairRatioEmbedding_firstVariable i

@[simp] theorem pairProjectiveEquiv_secondVariable (i : Index) :
    (pairProjectiveEquiv (outerVariable i) : PF) =
      secondFrame ℂ (affinePosition i).1 (affinePosition i).2 / secondFrame ℂ 0 0 :=
  pairRatioEmbedding_secondVariable i

end M9Native.PairProjectiveRatios
