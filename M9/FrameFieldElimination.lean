module

public import M9.ConstantFrameElimination
public import M9.FrameAction
public import M9.ProjectiveNoName

/-!
# Actual rational coordinates on the pair-frame cover

The pair-frame field is the literal iterated fraction field of the two
ternary frame matrices. An explicit polynomial change in the second frame
identifies its connected invariants with the actual entries of `HᵀF`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open scoped Classical Matrix BigOperators

namespace M9.FrameFieldElimination
open MvPolynomial ConstantFrameElimination

theorem algEquiv_conjugation_apply {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (e σ : B ≃ₐ[R] B) (f : B) :
    e (MulAut.conj e.symm.toRingEquiv σ.toRingEquiv f) = σ (e f) := by
  rw [MulAut.conj_apply, RingAut.mul_apply, RingAut.mul_apply, RingAut.inv_apply]
  change e (e.symm (σ (e f))) = _
  exact e.apply_symm_apply _

abbrev Index := ConstantFrameElimination.Index 3
abbrev MatrixField (K : Type*) [Field K] := ConstantFrameElimination.FunctionField K 3
abbrev PairField (K : Type*) [Field K] := ConstantFrameElimination.FunctionField (MatrixField K) 3

variable (K : Type*) [Field K] [Infinite K]

instance matrixField_infinite : Infinite (MatrixField K) :=
  Infinite.of_injective (algebraMap K (MatrixField K)) (algebraMap K (MatrixField K)).injective

def genericFieldMatrix : Matrix (Fin 3) (Fin 3) (MatrixField K) :=
  (ConstantFrameElimination.genericMatrix K 3).map
    (algebraMap (PolynomialRing K 3) (MatrixField K))

omit [Infinite K] in
theorem genericFieldMatrix_det_ne_zero : (genericFieldMatrix K).det ≠ 0 := by
  have he := (algebraMap (PolynomialRing K 3) (MatrixField K)).map_det
    (ConstantFrameElimination.genericMatrix K 3)
  change algebraMap (PolynomialRing K 3) (MatrixField K) (determinantPolynomial K 3) =
    (genericFieldMatrix K).det at he
  rw [← he]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (determinantPolynomial_ne_zero K 3))

def genericFrame : GLn (MatrixField K) 3 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (genericFieldMatrix K) (genericFieldMatrix_det_ne_zero K)

def firstFrame : Matrix (Fin 3) (Fin 3) (PairField K) :=
  (genericFieldMatrix K).map (algebraMap (MatrixField K) (PairField K))

def secondFrame : Matrix (Fin 3) (Fin 3) (PairField K) :=
  (ConstantFrameElimination.genericMatrix (MatrixField K) 3).map
    (algebraMap (PolynomialRing (MatrixField K) 3) (PairField K))

def invariantMatrix : Matrix (Fin 3) (Fin 3) (PairField K) :=
  (secondFrame K).transpose * firstFrame K

/-- The transpose is a genuine reindexing automorphism of the full
rational matrix field. -/
def transposeFractionEquiv (A : Type*) [Field A] : FunctionField A 3 ≃ₐ[A] FunctionField A 3 :=
  M9.rationalFieldReindex A (Equiv.prodComm (Fin 3) (Fin 3))

@[simp] theorem transposeFractionEquiv_variable (A : Type*) [Field A] (ij : Index) :
    transposeFractionEquiv A
      (algebraMap (PolynomialRing A 3) (FunctionField A 3) (X ij)) =
        algebraMap (PolynomialRing A 3) (FunctionField A 3) (X (ij.2,ij.1)) := by
  rw [transposeFractionEquiv, M9.rationalFieldReindex_algebraMap]
  rcases ij with ⟨i,j⟩
  rw [MvPolynomial.rename_X]
  rfl

/-- The literal substitution `H ↦ HᵀF`, over the independent first-frame
coefficient field. Its inverse is built from actual matrix inverses. -/
def invariantCoordinatesOverFrame : PairField K ≃ₐ[MatrixField K] PairField K :=
  leftFractionEquiv (MatrixField K) (MatrixField K) 3
      (FrameAction.contragredient (genericFrame K)⁻¹) *
    transposeFractionEquiv (MatrixField K)

theorem invariantCoordinates_firstFrame (i j : Fin 3) :
    invariantCoordinatesOverFrame K (firstFrame K i j) = firstFrame K i j :=
  (invariantCoordinatesOverFrame K).commutes (genericFieldMatrix K i j)

theorem invariantCoordinates_secondFrame (i j : Fin 3) :
    invariantCoordinatesOverFrame K (secondFrame K i j) = invariantMatrix K i j := by
  change leftFractionEquiv (MatrixField K) (MatrixField K) 3
    (FrameAction.contragredient (genericFrame K)⁻¹)
      (transposeFractionEquiv (MatrixField K)
        (algebraMap (PolynomialRing (MatrixField K) 3) (PairField K) (X (i,j)))) = _
  rw [transposeFractionEquiv_variable, leftFractionEquiv_polynomial, leftSubstitution_X, map_sum]
  change _ = ∑ k : Fin 3, secondFrame K k i * firstFrame K k j
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul]
  change algebraMap (MatrixField K) (PairField K)
      ((FrameAction.contragredient (genericFrame K)⁻¹).val j k) * secondFrame K k i = _
  simp only [FrameAction.contragredient_coe, inv_inv]
  change firstFrame K k j * secondFrame K k i = secondFrame K k i * firstFrame K k j
  exact mul_comm _ _

/-- The independent coefficient/fiber coordinates are exchanged after the
checked substitution. The resulting coefficient variables are exactly M=HᵀF,
while the remaining variables are the first frame F. -/
def normalCoordinates : PairField K ≃ₐ[K] PairField K :=
  ((invariantCoordinatesOverFrame K).symm.restrictScalars K).trans
    (ProjectiveNoName.rationalVariableSwap K Index Index)

/-- In the normal-coordinate target, the outer variables are the frame F. -/
def normalFrame : Matrix (Fin 3) (Fin 3) (PairField K) := secondFrame K

/-- In the normal-coordinate target, coefficient variables are M. -/
def normalInvariant : Matrix (Fin 3) (Fin 3) (PairField K) := firstFrame K

theorem normalCoordinates_firstFrame (i j : Fin 3) :
    normalCoordinates K (firstFrame K i j) = normalFrame K i j := by
  have he : (invariantCoordinatesOverFrame K).symm (firstFrame K i j) = firstFrame K i j := by
    apply (invariantCoordinatesOverFrame K).injective
    rw [AlgEquiv.apply_symm_apply, invariantCoordinates_firstFrame]
  rw [normalCoordinates, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply, he]
  exact ProjectiveNoName.rationalVariableSwap_coefficient K Index Index (i,j)

theorem normalCoordinates_invariantMatrix (i j : Fin 3) :
    normalCoordinates K (invariantMatrix K i j) = normalInvariant K i j := by
  rw [← invariantCoordinates_secondFrame K i j, normalCoordinates, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.symm_apply_apply]
  exact ProjectiveNoName.rationalVariableSwap_outer K Index Index (i,j)


/-- The actual inverse-pullback action in the normalized coordinates. -/
def normalActionHom : GLn K 3 →* (PairField K ≃ₐ[K] PairField K) :=
  (AlgEquiv.restrictScalarsHom K).comp (leftActionHom K (MatrixField K) 3)

theorem normalAction_apply (g : GLn K 3) (f : PairField K) :
    normalActionHom K g f = leftFractionEquiv K (MatrixField K) 3 g⁻¹ f := rfl

/-- The action on the original pair-frame field, transported through the
proved rational coordinate change. Generator formulas below verify the
literal connected action `(F,H) ↦ (g⁻¹F,gᵀH)`. -/
def normalRingActionHom : GLn K 3 →* (PairField K ≃+* PairField K) where
  toFun g := (normalActionHom K g).toRingEquiv
  map_one' := congrArg AlgEquiv.toRingEquiv (map_one (normalActionHom K))
  map_mul' g h := congrArg AlgEquiv.toRingEquiv (map_mul (normalActionHom K) g h)

def pairActionHom : GLn K 3 →* (PairField K ≃+* PairField K) :=
  (MulAut.conj (normalCoordinates K).symm.toRingEquiv).toMonoidHom.comp (normalRingActionHom K)

theorem pairAction_relative (g : GLn K 3) (f : PairField K) :
    normalCoordinates K (pairActionHom K g f) = normalActionHom K g (normalCoordinates K f) := by
  simpa only [pairActionHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, normalRingActionHom,
    MonoidHom.coe_mk, OneHom.coe_mk] using
      algEquiv_conjugation_apply (normalCoordinates K) (normalActionHom K g) f

/-- The invariant matrix coefficient field is embedded through its actual
entries in the original pair-frame field. -/
def invariantEmbedding : MatrixField K →ₐ[K] PairField K :=
  (normalCoordinates K).symm.toAlgHom.comp (IsScalarTower.toAlgHom K (MatrixField K) (PairField K))

theorem invariantEmbedding_coordinate (i j : Fin 3) :
    invariantEmbedding K (genericFieldMatrix K i j) = invariantMatrix K i j := by
  apply (normalCoordinates K).injective
  change normalCoordinates K ((normalCoordinates K).symm
    (algebraMap (MatrixField K) (PairField K) (genericFieldMatrix K i j))) = _
  rw [AlgEquiv.apply_symm_apply, normalCoordinates_invariantMatrix]
  rfl

theorem pairAction_invariantEmbedding (g : GLn K 3) (a : MatrixField K) :
    pairActionHom K g (invariantEmbedding K a) = invariantEmbedding K a := by
  apply (normalCoordinates K).injective
  rw [pairAction_relative]
  change normalActionHom K g
    (normalCoordinates K ((normalCoordinates K).symm (algebraMap (MatrixField K) (PairField K) a))) =
      normalCoordinates K ((normalCoordinates K).symm (algebraMap (MatrixField K) (PairField K) a))
  rw [AlgEquiv.apply_symm_apply]
  exact (leftActionHom K (MatrixField K) 3 g).commutes a

theorem pairAction_constant (g : GLn K 3) (c : K) :
    pairActionHom K g (algebraMap K (PairField K) c) = algebraMap K (PairField K) c := by
  apply (normalCoordinates K).injective
  rw [pairAction_relative]
  simp only [AlgEquiv.commutes]

@[instance_reducible] def pairAction : MulSemiringAction (GLn K 3) (PairField K) :=
  MulSemiringAction.compHom (PairField K) (pairActionHom K)

attribute [local instance] pairAction

def connectedFixedField : IntermediateField K (PairField K) where
  __ := FixedPoints.subfield (GLn K 3) (PairField K)
  algebraMap_mem' c g := pairAction_constant K g c

theorem mem_connectedFixedField_iff (f : PairField K) :
    f ∈ connectedFixedField K ↔ ∀ g : GLn K 3, pairActionHom K g f = f := Iff.rfl

/-- Invariants of the literal infinite connected frame group are exactly
rational functions of `HᵀF`; generic normalization is deduced from constant
invariance by the independently proved elimination theorem. -/
theorem connected_invariant_iff (f : PairField K) :
    f ∈ connectedFixedField K ↔ ∃ a : MatrixField K, invariantEmbedding K a = f := by
  rw [mem_connectedFixedField_iff]
  constructor
  · intro h
    have hn : ∀ g : GLn K 3,
        leftFractionEquiv K (MatrixField K) 3 g (normalCoordinates K f) = normalCoordinates K f := by
      intro g
      have he := congrArg (normalCoordinates K) (h g⁻¹)
      rw [pairAction_relative] at he
      rw [normalAction_apply, inv_inv] at he
      exact he
    obtain ⟨a,ha⟩ := invariant_fraction_is_constant K (MatrixField K) 3 (normalCoordinates K f) hn
    refine ⟨a, ?_⟩
    apply (normalCoordinates K).injective
    change normalCoordinates K ((normalCoordinates K).symm (algebraMap (MatrixField K) (PairField K) a)) = _
    rw [AlgEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a,rfl⟩ g
    exact pairAction_invariantEmbedding K g a

theorem invariantEmbedding_fieldRange : (invariantEmbedding K).fieldRange = connectedFixedField K := by
  ext f
  exact (connected_invariant_iff K f).symm

/-- The genuine connected invariant field of the affine pair-frame cover,
with the coefficient inclusion normalized to the literal `HᵀF` coordinates. -/
def connectedQuotientEquiv : MatrixField K ≃ₐ[K] connectedFixedField K :=
  (invariantEmbedding K).equivFieldRange.trans
    (IntermediateField.equivOfEq (invariantEmbedding_fieldRange K))

theorem connectedQuotientEquiv_coordinate (i j : Fin 3) :
    (connectedQuotientEquiv K (genericFieldMatrix K i j) : PairField K) = invariantMatrix K i j :=
  invariantEmbedding_coordinate K i j

theorem normalAction_frame_matrix (g : GLn K 3) :
    (normalActionHom K g).mapMatrix (normalFrame K) =
      (g⁻¹).val.map (algebraMap K (PairField K)) * normalFrame K := by
  ext i j
  change leftFractionEquiv K (MatrixField K) 3 g⁻¹
    (algebraMap (PolynomialRing (MatrixField K) 3) (PairField K) (X (i,j))) = _
  rw [leftFractionEquiv_polynomial, leftSubstitution_X, map_sum]
  change _ = ∑ k : Fin 3, algebraMap K (PairField K) ((g⁻¹).val i k) * normalFrame K k j
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul]
  change algebraMap (MatrixField K) (PairField K) (algebraMap K (MatrixField K) ((g⁻¹).val i k)) *
    normalFrame K k j = _
  rw [← IsScalarTower.algebraMap_apply K (MatrixField K) (PairField K)]

theorem pairAction_firstFrame (g : GLn K 3) :
    (pairActionHom K g).toRingHom.mapMatrix (firstFrame K) =
      (g⁻¹).val.map (algebraMap K (PairField K)) * firstFrame K := by
  ext i j
  apply (normalCoordinates K).injective
  change normalCoordinates K (pairActionHom K g (firstFrame K i j)) = _
  rw [pairAction_relative, normalCoordinates_firstFrame]
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) (PairField K) => M i j)
    (normalAction_frame_matrix K g)
  change normalActionHom K g (normalFrame K i j) = _ at he
  rw [he]
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul,
    AlgEquiv.commutes, normalCoordinates_firstFrame]

theorem pairAction_invariantMatrix (g : GLn K 3) :
    (pairActionHom K g).toRingHom.mapMatrix (invariantMatrix K) = invariantMatrix K := by
  ext i j
  change pairActionHom K g (invariantMatrix K i j) = invariantMatrix K i j
  rw [← invariantEmbedding_coordinate K i j]
  exact pairAction_invariantEmbedding K g (genericFieldMatrix K i j)


/-- The first generic matrix is an actual invertible matrix over the pair field. -/
def firstFrameUnit : GLn (PairField K) 3 :=
  Matrix.GeneralLinearGroup.map (algebraMap (MatrixField K) (PairField K)) (genericFrame K)

omit [Infinite K] in
@[simp] theorem firstFrameUnit_val : (firstFrameUnit K).val = firstFrame K := rfl

/-- On the original second frame, the constructed field action is exactly
inverse pullback of `H ↦ g⁻ᵀH`, with no substituted action premise. -/
theorem pairAction_secondFrame (g : GLn K 3) :
    (pairActionHom K g).toRingHom.mapMatrix (secondFrame K) =
      (g.val.map (algebraMap K (PairField K))).transpose * secondFrame K := by
  let φ := (pairActionHom K g).toRingHom
  let D : GLn (PairField K) 3 := Matrix.GeneralLinearGroup.map (algebraMap K (PairField K)) g
  let F := firstFrameUnit K
  have hfix := pairAction_invariantMatrix K g
  change ((secondFrame K).transpose * firstFrame K).map φ =
    (secondFrame K).transpose * firstFrame K at hfix
  rw [Matrix.map_mul] at hfix
  have hφF : (firstFrame K).map φ = (D⁻¹).val * F.val := pairAction_firstFrame K g
  rw [hφF] at hfix
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) (PairField K) => M * (F⁻¹).val) hfix
  change ((secondFrame K).map φ).transpose * ((D⁻¹).val * F.val) * (F⁻¹).val =
    (secondFrame K).transpose * F.val * (F⁻¹).val at he
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at he
  have he' := congrArg (fun M : Matrix (Fin 3) (Fin 3) (PairField K) => M * D.val) he
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at he'
  have ht := congrArg Matrix.transpose he'
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
  exact ht

/-- The actual field generated by the entries of `HᵀF`. -/
def invariantEntryField : IntermediateField K (PairField K) :=
  IntermediateField.adjoin K (Set.range fun ij : Index => invariantMatrix K ij.1 ij.2)

theorem invariantEmbedding_polynomial_mem (p : PolynomialRing K 3) :
    invariantEmbedding K (algebraMap (PolynomialRing K 3) (MatrixField K) p) ∈ invariantEntryField K := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    change invariantEmbedding K (algebraMap K (MatrixField K) a) ∈ _
    rw [(invariantEmbedding K).commutes]
    exact IntermediateField.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add, map_add]
    exact (invariantEntryField K).add_mem hp hq
  | mul_X p ij hp =>
    rw [map_mul, map_mul]
    apply (invariantEntryField K).mul_mem hp
    rw [show algebraMap (PolynomialRing K 3) (MatrixField K) (X ij) =
      genericFieldMatrix K ij.1 ij.2 from rfl, invariantEmbedding_coordinate]
    exact IntermediateField.subset_adjoin K _ ⟨ij,rfl⟩

theorem connectedFixedField_eq_invariantEntryField : connectedFixedField K = invariantEntryField K := by
  apply le_antisymm
  · intro f hf
    obtain ⟨a,rfl⟩ := (connected_invariant_iff K f).mp hf
    obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (PolynomialRing K 3) a
    rw [map_div₀]
    exact (invariantEntryField K).div_mem
      (invariantEmbedding_polynomial_mem K p) (invariantEmbedding_polynomial_mem K q)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ij,rfl⟩
    change invariantMatrix K ij.1 ij.2 ∈ connectedFixedField K
    exact (connected_invariant_iff K _).mpr
      ⟨genericFieldMatrix K ij.1 ij.2, invariantEmbedding_coordinate K ij.1 ij.2⟩

end M9.FrameFieldElimination
