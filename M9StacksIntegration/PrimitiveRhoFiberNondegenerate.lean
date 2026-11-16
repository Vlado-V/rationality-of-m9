module

public import M9StacksIntegration.PrimitiveRhoFiberChart

/-!
# The actual nondegenerate rho-fiber chart

The dual-coordinate evaluation formula retains the original symmetric-matrix
space and its actual dual. The nondegeneracy determinant is formed from the
original primitive wedge form, on the original lifted graph vectors.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical Matrix TensorProduct

namespace M9Native.PrimitiveRhoFiberNondegenerate
open Module M9.GraphBundleDescent M9.ExteriorPrimitive M9.PrimitiveBlockCoordinates
open PrimitiveRhoFiberChart

section ActualDualCoordinates
variable (K : Type*) [Field K]

/-- Literal evaluation in the actual symmetric-plane/dual-plane splitting. -/
theorem dualSymmetricSplit_evaluation (φ : Module.Dual K (M9.Symmetric3 K))
    (X : M9.Symmetric3 K) :
    φ X =
      (∑ i : Fin 4, (dualSymmetricSplit K φ).1 i * (symmetricSplit K X).1 i) +
      ∑ i : Fin 2, (dualSymmetricSplit K φ).2 i * (symmetricSplit K X).2 i := by
  let ψ := (symmetricSplit K).dualMap.symm φ
  let x := symmetricSplit K X
  have he : φ X = ψ x := by
    have h := congrArg (fun f : Module.Dual K (M9.Symmetric3 K) => f X)
      ((symmetricSplit K).dualMap.apply_symm_apply φ)
    exact h.symm
  rw [he]
  have hx := (ambientBasis K).sum_repr x
  conv_lhs => rw [← hx]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hd : (dualSymmetricSplit K φ).1 i = ψ (ambientBasis K (.inl i)) := by
      exact (ambientBasis K).dualBasis_equivFun ψ (.inl i)
    rw [hd]
    have hc : (ambientBasis K).repr x (.inl i) = x.1 i := by
      simp [ambientBasis]
      rfl
    rw [hc,mul_comm]
  · apply Finset.sum_congr rfl
    intro i _
    have hd : (dualSymmetricSplit K φ).2 i = ψ (ambientBasis K (.inr i)) := by
      exact (ambientBasis K).dualBasis_equivFun ψ (.inr i)
    rw [hd]
    have hc : (ambientBasis K).repr x (.inr i) = x.2 i := by
      simp [ambientBasis]
      rfl
    rw [hc,mul_comm]

end ActualDualCoordinates

local instance primitiveGroup : AddCommGroup (Primitive ℂ) :=
  { (Primitive ℂ).addCommGroup with toAddCommMonoid := (Primitive ℂ).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp ℂ) :=
  { (Perp ℂ).addCommGroup with toAddCommMonoid := (Perp ℂ).addCommMonoid }

/-- The original mixed vectors in the literal symmetric-space and dual-space coordinates. -/
def actualMixed (z : Ambient ℂ × Ambient ℂ) : Mixed ℂ :=
  (M9.PrimitiveTwistedReduced.mixedDualEquiv ℂ).symm
    ((symmetricSplit ℂ).symm z.1,(dualSymmetricSplit ℂ).symm z.2)

theorem actualMixed_coordinates (z : Ambient ℂ × Ambient ℂ) :
    mixedCoordinates (actualMixed z) = GraphGrassmannianChart.ambientCoordinates z := by
  simp only [mixedCoordinates,actualMixed,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply,LinearEquiv.prodCongr_apply]

/-- The actual wedge pairing on mixed vectors has its literal dual-evaluation normalization. -/
theorem mixed_pairing (z w : Ambient ℂ × Ambient ℂ) :
    primitivePairing ℂ
      (mixedCoordinateLift (GraphGrassmannianChart.ambientCoordinates z))
      (mixedCoordinateLift (GraphGrassmannianChart.ambientCoordinates w)) =
      ((dualSymmetricSplit ℂ).symm w.2) ((symmetricSplit ℂ).symm z.1) -
        ((dualSymmetricSplit ℂ).symm z.2) ((symmetricSplit ℂ).symm w.1) := by
  have hm (a b : Mixed ℂ) :
      primitivePairing ℂ (mixedCoordinateLift (mixedCoordinates a))
        (mixedCoordinateLift (mixedCoordinates b)) =
      M9.PrimitiveRepresentation.tracePair ℂ a.1 b.2 -
        M9.PrimitiveRepresentation.tracePair ℂ b.1 a.2 := by
    change primitivePairing ℂ
      (primitiveEquiv ℂ (0,(mixedCoordinates.symm (mixedCoordinates a)).1,
        (mixedCoordinates.symm (mixedCoordinates a)).2,0))
      (primitiveEquiv ℂ (0,(mixedCoordinates.symm (mixedCoordinates b)).1,
        (mixedCoordinates.symm (mixedCoordinates b)).2,0)) = _
    rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply,primitivePairing_equiv]
    simp [M9.PrimitiveRepresentation.pairing_apply,M9.PrimitiveRepresentation.tracePair,Matrix.trace_sub]
  have h := hm (actualMixed z) (actualMixed w)
  rw [actualMixed_coordinates,actualMixed_coordinates] at h
  rw [h]
  congr 1
  · exact congrArg (fun φ : Module.Dual ℂ (M9.Symmetric3 ℂ) => φ ((symmetricSplit ℂ).symm z.1))
      ((symmetricDualEquiv ℂ).apply_symm_apply ((dualSymmetricSplit ℂ).symm w.2))
  · exact congrArg (fun φ : Module.Dual ℂ (M9.Symmetric3 ℂ) => φ ((symmetricSplit ℂ).symm w.1))
      ((symmetricDualEquiv ℂ).apply_symm_apply ((dualSymmetricSplit ℂ).symm z.2))

/-- The same normalization written entirely in the original finite graph coordinates. -/
theorem mixed_pairing_coordinates (z w : Ambient ℂ × Ambient ℂ) :
    primitivePairing ℂ
      (mixedCoordinateLift (GraphGrassmannianChart.ambientCoordinates z))
      (mixedCoordinateLift (GraphGrassmannianChart.ambientCoordinates w)) =
      ((∑ i : Fin 4, w.2.1 i * z.1.1 i) + ∑ i : Fin 2, w.2.2 i * z.1.2 i) -
        ((∑ i : Fin 4, z.2.1 i * w.1.1 i) + ∑ i : Fin 2, z.2.2 i * w.1.2 i) := by
  rw [mixed_pairing,dualSymmetricSplit_evaluation,dualSymmetricSplit_evaluation,
    LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

section ActualGram
variable (R : Type*) [CommRing R] [Algebra ℂ R]

/-- The literal Gram matrix of the mixed lift in the original primitive exterior space. -/
def gramMatrix (P : Matrix (Fin 12) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  (liftMatrix.map (algebraMap ℂ R) * P).transpose *
    pairingMatrix.map (algebraMap ℂ R) * (liftMatrix.map (algebraMap ℂ R) * P)

end ActualGram

theorem gramMatrix_entry (P : Matrix (Fin 12) (Fin 4) ℂ) (i j : Fin 4) :
    gramMatrix ℂ P i j = primitivePairing ℂ
      (mixedCoordinateLift (fun k => P k i)) (mixedCoordinateLift (fun k => P k j)) := by
  have hJ : pairingMatrix.map (algebraMap ℂ ℂ) = pairingMatrix := by ext a b; simp
  have hL : liftMatrix.map (algebraMap ℂ ℂ) = liftMatrix := by ext a b; simp
  rw [gramMatrix,hJ,hL,Matrix.mul_assoc]
  change (liftMatrix *ᵥ (fun k => P k i)) ⬝ᵥ
    (pairingMatrix *ᵥ (liftMatrix *ᵥ (fun k => P k j))) = _
  rw [← Matrix.toBilin'_apply',pairingMatrix,Matrix.toBilin'_toMatrix']
  rw [liftMatrix,LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
  simp only [coordinatePairing,coordinateLift,LinearMap.comp_apply,LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

theorem graphMatrix_column {R : Type*} [CommRing R]
    (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R) (i : Fin 4) :
    (fun k => graphMatrix R A B X k i) =
      GraphGrassmannianChart.ambientCoordinates (graphFamilyEmbedding R A B X (Pi.single i 1)) := by
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply'] using graphMatrix_mulVec R A B X (Pi.single i 1)

/-- Exact Gram formula on the actual zero-base graph; no orbit multiplicities or rescaling. -/
theorem gramMatrix_zero_base (X : Matrix.GeneralLinearGroup (Fin 4) ℂ) :
    gramMatrix ℂ (graphMatrix ℂ 0 0 X) = X.val - X.val.transpose := by
  ext i j
  rw [gramMatrix_entry,graphMatrix_column,graphMatrix_column,mixed_pairing_coordinates,
    graphFamilyEmbedding_apply,graphFamilyEmbedding_apply]
  simp only [Matrix.zero_mul,Matrix.mulVec_single_one,Matrix.col_apply,Matrix.zero_apply,
    mul_zero,Finset.sum_const_zero,add_zero,Matrix.sub_apply,Matrix.transpose_apply]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

def skewMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) finSumFinEquiv (Matrix.J (Fin 2) ℂ)

theorem skewMatrix_det_unit : IsUnit skewMatrix.det := by
  rw [skewMatrix,Matrix.det_reindex_self]
  exact Matrix.isUnit_det_J (Fin 2) ℂ

theorem skewMatrix_transpose : skewMatrix.transpose = -skewMatrix := by
  rw [skewMatrix,Matrix.transpose_reindex,Matrix.J_transpose]
  rfl

def skewIsomorphism : Matrix.GeneralLinearGroup (Fin 4) ℂ :=
  Matrix.GeneralLinearGroup.mk'' skewMatrix skewMatrix_det_unit

theorem skew_graph_gram : gramMatrix ℂ (graphMatrix ℂ 0 0 skewIsomorphism) = (2 : ℂ) • skewMatrix := by
  rw [gramMatrix_zero_base]
  change skewMatrix - skewMatrix.transpose = _
  rw [skewMatrix_transpose,sub_neg_eq_add,two_smul]

theorem skew_graph_gram_det_ne_zero :
    (gramMatrix ℂ (graphMatrix ℂ 0 0 skewIsomorphism)).det ≠ 0 := by
  rw [skew_graph_gram,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (two_ne_zero : (2 : ℂ) ≠ 0))
    (isUnit_iff_ne_zero.mp skewMatrix_det_unit)

section Naturality
variable {R S : Type*} [CommRing R] [CommRing S]

theorem graphMatrix_entry (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R)
    (i : Fin 12) (j : Fin 4) : graphMatrix R A B X i j =
    Sum.elim (fun k => if k = j then 1 else 0)
      (fun k => GraphGrassmannianChart.blockRows A X.val (B * X.val) k j)
        (finSumFinEquiv.symm i) := by
  rw [show graphMatrix R A B X i j = (fun k => graphMatrix R A B X k j) i from rfl,
    graphMatrix_column,graphFamilyEmbedding_apply,GraphGrassmannianChart.ambientCoordinates_apply]
  obtain ⟨a,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective i
  simp only [Equiv.symm_apply_apply]
  rcases a with a | a
  · simp only [Sum.elim_inl,Pi.single_apply]
  · obtain ⟨a,rfl⟩ := GraphGrassmannianChart.rowEquiv.surjective a
    rcases a with a | (a | a) <;>
      simp only [Sum.elim_inr,Equiv.symm_apply_apply,Sum.elim_inl,
        GraphGrassmannianChart.blockRows,Matrix.mulVec_single_one,Matrix.col_apply]

theorem graphMatrix_map (f : R →+* S) (A B : BaseMatrix R)
    (X : Matrix.GeneralLinearGroup (Fin 4) R) :
    (graphMatrix R A B X).map f =
      graphMatrix S (A.map f) (B.map f) (Matrix.GeneralLinearGroup.map f X) := by
  have hX : (Matrix.GeneralLinearGroup.map f X).val = X.val.map f := rfl
  ext i j
  rw [Matrix.map_apply,graphMatrix_entry,graphMatrix_entry]
  obtain ⟨a,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective i
  simp only [Equiv.symm_apply_apply]
  rcases a with a | a
  · simp only [Sum.elim_inl]
    split_ifs <;> simp
  · simp only [Sum.elim_inr]
    obtain ⟨a,rfl⟩ := GraphGrassmannianChart.rowEquiv.surjective a
    rcases a with a | (a | a) <;>
      simp only [GraphGrassmannianChart.blockRows,Equiv.symm_apply_apply,Sum.elim_inl,
        Sum.elim_inr,Matrix.map_apply,hX,← Matrix.map_mul]

variable [Algebra ℂ R] [Algebra ℂ S]

theorem gramMatrix_map (f : R →ₐ[ℂ] S) (P : Matrix (Fin 12) (Fin 4) R) :
    (gramMatrix R P).map f = gramMatrix S (P.map f) := by
  have hL : (liftMatrix.map (algebraMap ℂ R)).map f = liftMatrix.map (algebraMap ℂ S) := by
    ext i j
    exact f.commutes (liftMatrix i j)
  have hJ : (pairingMatrix.map (algebraMap ℂ R)).map f = pairingMatrix.map (algebraMap ℂ S) := by
    ext i j
    exact f.commutes (pairingMatrix i j)
  have hT (M : Matrix (Fin 14) (Fin 4) R) : M.transpose.map f = (M.map f).transpose := rfl
  simp only [gramMatrix,Matrix.map_mul,hT,hL,hJ]

end Naturality

abbrev parameterRing := IsomChartRing ℂ

def parameterGraph : Matrix (Fin 12) (Fin 4) parameterRing :=
  graphMatrix parameterRing (universalBaseLocalized (K := ℂ) 0)
    (universalBaseLocalized (K := ℂ) 1) (universalIsomorphism (K := ℂ))

/-- Literal determinant of the actual reduced wedge form on the universal graph. -/
def nondegenerateDeterminant : parameterRing := (gramMatrix parameterRing parameterGraph).det

def skewEvaluation : parameterRing →ₐ[ℂ] ℂ := chartEvaluation 0 0 skewIsomorphism

theorem skewEvaluation_graph : parameterGraph.map skewEvaluation = graphMatrix ℂ 0 0 skewIsomorphism := by
  change parameterGraph.map (chartEvaluation 0 0 skewIsomorphism).toRingHom = _
  rw [parameterGraph,graphMatrix_map,chartEvaluation_base 0 0 skewIsomorphism 0,
    chartEvaluation_base 0 0 skewIsomorphism 1]
  have hX : Matrix.GeneralLinearGroup.map (chartEvaluation 0 0 skewIsomorphism).toRingHom
      (universalIsomorphism (K := ℂ)) = skewIsomorphism := by
    apply Units.ext
    have hv := congrArg (fun G : Matrix.GeneralLinearGroup (Fin 4) ℂ => G.val)
      (chartEvaluation_fiber (K := ℂ) 0 0 skewIsomorphism)
    exact hv
  rw [hX]
  rfl

theorem skewEvaluation_det_ne_zero : skewEvaluation nondegenerateDeterminant ≠ 0 := by
  change skewEvaluation.toRingHom (gramMatrix parameterRing parameterGraph).det ≠ 0
  rw [RingHom.map_det]
  change ((gramMatrix parameterRing parameterGraph).map skewEvaluation).det ≠ 0
  rw [gramMatrix_map,skewEvaluation_graph]
  exact skew_graph_gram_det_ne_zero

theorem nondegenerateDeterminant_ne_zero : nondegenerateDeterminant ≠ 0 := by
  intro h
  exact skewEvaluation_det_ne_zero (by rw [h,map_zero])

abbrev nondegenerateRing := Localization.Away nondegenerateDeterminant
abbrev nondegenerateDomain := Spec (.of nondegenerateRing)

instance nondegenerateRing_isDomain : IsDomain nondegenerateRing :=
  Localization.Away.isDomain nondegenerateDeterminant_ne_zero

/-- A genuine, proved nonempty open in the original native graph chart. -/
def inclusion : nondegenerateDomain ⟶ PrimitiveRhoFiberChart.domain :=
  Spec.map (CommRingCat.ofHom (algebraMap parameterRing nondegenerateRing))

instance inclusion_isOpenImmersion : IsOpenImmersion inclusion := by
  unfold inclusion nondegenerateRing
  infer_instance

theorem inclusion_dense : DenseRange inclusion :=
  inclusion.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

/-- The actual native rank-nine family restricted to the nondegenerate reduced graph open. -/
def map : nondegenerateDomain ⟶ GrassmannianCharts.space ℂ 9 14 :=
  inclusion ≫ PrimitiveRhoFiberChart.map

@[reassoc] theorem map_projection : map ≫ GrassmannianCharts.projection ℂ 9 14 =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ nondegenerateRing)) := by
  rw [map,Category.assoc,PrimitiveRhoFiberChart.map_projection,inclusion,
    ← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1

def localizationMap : parameterRing →ₐ[ℂ] nondegenerateRing :=
  IsScalarTower.toAlgHom ℂ parameterRing nondegenerateRing

def localizedGraph : Matrix (Fin 12) (Fin 4) nondegenerateRing :=
  parameterGraph.map localizationMap

theorem localized_gram_det_unit : IsUnit (gramMatrix nondegenerateRing localizedGraph).det := by
  rw [localizedGraph,← gramMatrix_map localizationMap]
  change IsUnit (localizationMap.toRingHom.mapMatrix (gramMatrix parameterRing parameterGraph)).det
  rw [← RingHom.map_det localizationMap.toRingHom]
  exact IsLocalization.Away.algebraMap_isUnit nondegenerateDeterminant

/-- Every actual field point of the displayed localization has nondegenerate literal Gram matrix. -/
theorem fieldPoint_gram_det_ne_zero {K : Type*} [Field K] [Algebra ℂ K]
    (f : nondegenerateRing →ₐ[ℂ] K) :
    (gramMatrix K (localizedGraph.map f)).det ≠ 0 := by
  rw [← gramMatrix_map f]
  change (f.toRingHom.mapMatrix (gramMatrix nondegenerateRing localizedGraph)).det ≠ 0
  rw [← RingHom.map_det f.toRingHom]
  exact isUnit_iff_ne_zero.mp (localized_gram_det_unit.map f.toMonoidHom)

end M9Native.PrimitiveRhoFiberNondegenerate
