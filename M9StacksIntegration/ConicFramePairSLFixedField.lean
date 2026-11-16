module

public import M9StacksIntegration.ConicFramePairSLAction
public import M9StacksIntegration.ConicFramePairSwap

/-! Exact comparison of the diagonal SL3 invariants of the actual native
Grassmannian product with the two tetrahedral invariants of the actual
native projective matrix quotient. Every embedding is the original
conic-frame pullback, and the original deck operators are retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

namespace M9Native.ConicFramePairSLFixedField

open ConicFramePairSLAction ConicFramePairRawPullback ConicFramePairFixedField
open PairProjectiveRatios
open M9.ProjectiveFrameQuotient
open M9.FrameQuotientActionComparison

abbrev GrassField := ConicFramePairFieldComparison.target.functionField
abbrev Gamma := ConicFrameGammaAction.Gamma
abbrev MatrixField := M9.ProjectiveFrameQuotient.NativeMatrixField
abbrev ProjectivePair := M9.ProjectiveFrameQuotient.projectivePairField

@[instance_reducible] def nativeSLAction : MulSemiringAction SL3 GrassField :=
  MulSemiringAction.compHom GrassField nativeFieldRepresentation

attribute [local instance] nativeSLAction

/-- Actual diagonal SL3 invariants of the actual native Grassmannian product. -/
def nativeSLFixedField : IntermediateField ℂ GrassField where
  __ := FixedPoints.subfield SL3 GrassField
  algebraMap_mem' c g := (nativeFieldRepresentation g).commutes c

theorem mem_nativeSLFixedField_iff (z : GrassField) : z ∈ nativeSLFixedField ↔
    ∀ g : SL3, nativeFieldRepresentation g z = z := Iff.rfl

/-- The original exact ratio embedding, retaining the actual native conic pullback. -/
def projectiveEmbedding : GrassField →ₐ[ℂ] ProjectivePair :=
  pairProjectiveEquiv.toAlgHom.comp ConicFramePairFixedField.functionFieldEmbedding

theorem projectiveEmbedding_coe (z : GrassField) :
    (projectiveEmbedding z : PairProjectiveRatios.PF) = rawEmbedding z := rfl

theorem projectiveEmbedding_equivariance (g : SL3) (z : GrassField) :
    projectiveEmbedding (nativeFieldRepresentation g z) =
      ProjectivePairSLFixedField.slActionHom g (projectiveEmbedding z) := by
  apply Subtype.ext
  change rawEmbedding (nativeFieldRepresentation g z) =
    rawFieldAutomorphism g (rawEmbedding z)
  exact rawEmbedding_equivariance g z

theorem projectiveEmbedding_deck_fixed (a b : Gamma) (z : GrassField) :
    pairDeck a b (rawEmbedding z) = rawEmbedding z := by
  change pairDeck a b (pairRatioEmbedding (ConicFramePairFixedField.functionFieldEmbedding z)) = _
  rw [← PairProjectiveEquivariance.pairRatioEmbedding_pairDeck,
    ConicFramePairFixedField.embedding_fixed]
  rfl

/-- Exact image criterion through the proved actual two-cover fixed-field theorem. -/
theorem exists_projectiveEmbedding (t : ProjectivePair)
    (ht : ∀ a b : Gamma, pairDeck a b (t : PairProjectiveRatios.PF) = t) :
    ∃ z : GrassField, projectiveEmbedding z = t := by
  let y := pairProjectiveEquiv.symm t
  have hy : y ∈ ConicFramePairFixedField.fixedField := by
    intro g
    apply pairRatioEmbedding.injective
    change pairRatioEmbedding (ConicFrameIndependentPairAction.pairRepresentation (g.1,g.2) y) =
      pairRatioEmbedding y
    rw [PairProjectiveEquivariance.pairRatioEmbedding_pairDeck]
    change pairDeck g.1 g.2 (pairRatioEmbedding (pairProjectiveEquiv.symm t)) =
      pairRatioEmbedding (pairProjectiveEquiv.symm t)
    have he : pairRatioEmbedding (pairProjectiveEquiv.symm t) = (t : PairProjectiveRatios.PF) := by
      change (pairProjectiveEquiv (pairProjectiveEquiv.symm t) : PairProjectiveRatios.PF) = _
      rw [AlgEquiv.apply_symm_apply]
    rw [he]
    exact ht g.1 g.2
  have hi : y ∈ ConicFramePairFixedField.imageField := by
    rw [ConicFramePairFixedField.image_eq_fixed]
    exact hy
  obtain ⟨z, hz⟩ := hi
  change ConicFramePairFixedField.functionFieldEmbedding z = y at hz
  refine ⟨z, ?_⟩
  change pairProjectiveEquiv (ConicFramePairFixedField.functionFieldEmbedding z) = t
  rw [hz]
  exact pairProjectiveEquiv.apply_symm_apply t

def toSLFixed : nativeSLFixedField →ₐ[ℂ] ProjectivePairSLFixedField.slFixedField where
  toFun z := ⟨projectiveEmbedding z.val, by
    intro g
    change ProjectivePairSLFixedField.slActionHom g (projectiveEmbedding z.val) = projectiveEmbedding z.val
    rw [← projectiveEmbedding_equivariance]
    exact congrArg projectiveEmbedding (z.property g)⟩
  map_zero' := Subtype.ext (map_zero projectiveEmbedding)
  map_one' := Subtype.ext (map_one projectiveEmbedding)
  map_add' x y := Subtype.ext (map_add projectiveEmbedding x.val y.val)
  map_mul' x y := Subtype.ext (map_mul projectiveEmbedding x.val y.val)
  commutes' c := Subtype.ext (projectiveEmbedding.commutes c)

/-- Only the proved equality SL3-fixed = PGL3-fixed is used here. -/
def toMatrix : nativeSLFixedField →ₐ[ℂ] MatrixField :=
  ProjectivePairSLFixedField.nativeSLQuotientEquiv.symm.toAlgHom.comp toSLFixed

theorem nativeSLQuotient_raw (y : MatrixField) :
    (((ProjectivePairSLFixedField.nativeSLQuotientEquiv y).val : ProjectivePair) :
      PairProjectiveRatios.PF) = projectiveInvariantEmbedding y := rfl

theorem toMatrix_raw (z : nativeSLFixedField) :
    projectiveInvariantEmbedding (toMatrix z) = rawEmbedding z.val := by
  calc
    projectiveInvariantEmbedding (toMatrix z) =
        (((ProjectivePairSLFixedField.nativeSLQuotientEquiv (toMatrix z)).val : ProjectivePair) :
          PairProjectiveRatios.PF) := (nativeSLQuotient_raw _).symm
    _ = (((toSLFixed z).val : ProjectivePair) : PairProjectiveRatios.PF) := by
      apply congrArg (fun y : ProjectivePairSLFixedField.slFixedField =>
        ((y.val : ProjectivePair) : PairProjectiveRatios.PF))
      exact ProjectivePairSLFixedField.nativeSLQuotientEquiv.apply_symm_apply (toSLFixed z)
    _ = rawEmbedding z.val := projectiveEmbedding_coe z.val

def matrixGammaRepresentation : (Gamma × Gamma) →* (MatrixField ≃ₐ[ℂ] MatrixField) :=
  M9.FrameProjectiveGeometry.fieldRepresentation.comp M9.FrameAction.FrameGroup.pairHom

@[instance_reducible] def matrixGammaAction : MulSemiringAction (Gamma × Gamma) MatrixField :=
  MulSemiringAction.compHom MatrixField matrixGammaRepresentation

attribute [local instance] matrixGammaAction

/-- Actual Γ×Γ invariants inside the native P(Mat3) generic stalk. -/
def matrixGammaFixedField : IntermediateField ℂ MatrixField where
  __ := FixedPoints.subfield (Gamma × Gamma) MatrixField
  algebraMap_mem' c g := (matrixGammaRepresentation g).commutes c

theorem mem_matrixGammaFixedField_iff (z : MatrixField) : z ∈ matrixGammaFixedField ↔
    ∀ g : Gamma × Gamma, matrixGammaRepresentation g z = z := Iff.rfl

theorem toMatrix_mem (z : nativeSLFixedField) : toMatrix z ∈ matrixGammaFixedField := by
  intro g
  apply projectiveInvariantEmbedding.injective
  change projectiveInvariantEmbedding
      (M9.FrameProjectiveGeometry.fieldRepresentation
        (M9.FrameAction.FrameGroup.pairHom (g.1,g.2)) (toMatrix z)) = _
  rw [← pairDeck_embedding, toMatrix_raw, projectiveEmbedding_deck_fixed]
  change rawEmbedding z.val = projectiveInvariantEmbedding (toMatrix z)
  exact (toMatrix_raw z).symm

def invariantComparison : nativeSLFixedField →ₐ[ℂ] matrixGammaFixedField where
  toFun z := ⟨toMatrix z, toMatrix_mem z⟩
  map_zero' := Subtype.ext (map_zero toMatrix)
  map_one' := Subtype.ext (map_one toMatrix)
  map_add' x y := Subtype.ext (map_add toMatrix x y)
  map_mul' x y := Subtype.ext (map_mul toMatrix x y)
  commutes' c := Subtype.ext (toMatrix.commutes c)

theorem invariantComparison_surjective : Function.Surjective invariantComparison := by
  intro y
  let t := ProjectivePairSLFixedField.nativeSLQuotientEquiv y.val
  have ht : ∀ a b : Gamma, pairDeck a b ((t.val : ProjectivePair) : PairProjectiveRatios.PF) = t.val := by
    intro a b
    rw [nativeSLQuotient_raw, pairDeck_embedding]
    exact congrArg projectiveInvariantEmbedding (y.property (a,b))
  obtain ⟨z, hz⟩ := exists_projectiveEmbedding t.val ht
  have hzSL : z ∈ nativeSLFixedField := by
    intro g
    apply projectiveEmbedding.injective
    change projectiveEmbedding (nativeFieldRepresentation g z) = projectiveEmbedding z
    rw [projectiveEmbedding_equivariance, hz]
    exact t.property g
  refine ⟨⟨z, hzSL⟩, ?_⟩
  apply Subtype.ext
  apply ProjectivePairSLFixedField.nativeSLQuotientEquiv.injective
  change ProjectivePairSLFixedField.nativeSLQuotientEquiv
      (ProjectivePairSLFixedField.nativeSLQuotientEquiv.symm (toSLFixed ⟨z, hzSL⟩)) =
    ProjectivePairSLFixedField.nativeSLQuotientEquiv y.val
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  exact hz

/-- Exact invariant-field comparison for the original native Grassmannian
product and the original native projective matrix quotient. -/
def nativeSLInvariantFieldEquiv : nativeSLFixedField ≃ₐ[ℂ] matrixGammaFixedField :=
  AlgEquiv.ofBijective invariantComparison ⟨invariantComparison.injective, invariantComparison_surjective⟩

theorem nativeSLInvariantFieldEquiv_raw (z : nativeSLFixedField) :
    projectiveInvariantEmbedding (nativeSLInvariantFieldEquiv z).val = rawEmbedding z.val :=
  toMatrix_raw z

theorem rawEmbedding_swap (z : GrassField) :
    rawEmbedding (ConicFramePairSwap.nativeSwap z) = pairSwap (rawEmbedding z) := by
  change pairRatioEmbedding
    (ConicFramePairFixedField.functionFieldEmbedding (ConicFramePairSwap.nativeSwap z)) = _
  rw [ConicFramePairSwap.embedding_swap]
  exact PairProjectiveEquivariance.pairRatioEmbedding_swap _

/-- The literal native symmetry exchanges the two dual ambient actions. -/
theorem nativeAction_swap (g : SL3) :
    nativeAction g ≫ ConicFramePairSwap.schemeSwap.hom =
      ConicFramePairSwap.schemeSwap.hom ≫ nativeAction (dualHom g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ConicFramePairSwap.schemeSwap, nativeAction,
      pullbackSymmetry_hom_comp_fst,
      GrassmannianPairLinearAction.action_fst, GrassmannianPairLinearAction.action_snd]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  · simp only [Category.assoc, ConicFramePairSwap.schemeSwap, nativeAction,
      pullbackSymmetry_hom_comp_snd,
      GrassmannianPairLinearAction.action_fst, GrassmannianPairLinearAction.action_snd,
      dualHom_involutive]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_snd]

theorem nativeFieldRepresentation_swap (g : SL3) (z : GrassField) :
    nativeFieldRepresentation g (ConicFramePairSwap.nativeSwap z) =
      ConicFramePairSwap.nativeSwap (nativeFieldRepresentation (dualHom g) z) := by
  have hh := GrassmannianLinearAction.dominantMap_congr (nativeAction_swap g)
  rw [NativeFunctionFieldFunctor.map_comp, NativeFunctionFieldFunctor.map_comp] at hh
  have hz := DFunLike.congr_fun hh z
  change (nativeFieldRepresentation g).toRingHom (ConicFramePairSwap.nativeSwap.toRingHom z) =
    ConicFramePairSwap.nativeSwap.toRingHom ((nativeFieldRepresentation (dualHom g)).toRingHom z)
  rw [nativeFieldRepresentation_eq_map, nativeFieldRepresentation_eq_map,
    ConicFramePairSwap.nativeSwap_eq_map]
  exact hz

theorem nativeSwap_mem (z : nativeSLFixedField) :
    ConicFramePairSwap.nativeSwap z.val ∈ nativeSLFixedField := by
  intro g
  change nativeFieldRepresentation g (ConicFramePairSwap.nativeSwap z.val) = _
  rw [nativeFieldRepresentation_swap]
  exact congrArg ConicFramePairSwap.nativeSwap (z.property (dualHom g))

/-- Actual restriction of the literal native product symmetry. -/
def nativeFixedSwap : nativeSLFixedField ≃ₐ[ℂ] nativeSLFixedField where
  toFun z := ⟨ConicFramePairSwap.nativeSwap z.val, nativeSwap_mem z⟩
  invFun z := ⟨ConicFramePairSwap.nativeSwap z.val, nativeSwap_mem z⟩
  left_inv z := by
    apply Subtype.ext
    exact AlgEquiv.congr_fun ConicFramePairSwap.nativeSwap_squared z.val
  right_inv z := by
    apply Subtype.ext
    exact AlgEquiv.congr_fun ConicFramePairSwap.nativeSwap_squared z.val
  map_mul' x y := Subtype.ext (map_mul ConicFramePairSwap.nativeSwap x.val y.val)
  map_add' x y := Subtype.ext (map_add ConicFramePairSwap.nativeSwap x.val y.val)
  commutes' c := Subtype.ext (ConicFramePairSwap.nativeSwap.commutes c)

def matrixSwap : MatrixField ≃ₐ[ℂ] MatrixField :=
  M9.FrameProjectiveGeometry.fieldRepresentation M9.FrameAction.FrameGroup.tau

theorem pairHom_mul_tau (a b : Gamma) :
    M9.FrameAction.FrameGroup.pairHom (a,b) * M9.FrameAction.FrameGroup.tau =
      M9.FrameAction.FrameGroup.tau * M9.FrameAction.FrameGroup.pairHom (b,a) := by
  have h := congrArg (fun w : M9.FrameAction.TetrahedralFrameGroup =>
      M9.FrameAction.FrameGroup.tau * w) (M9.FrameAction.FrameGroup.tau_pair_tau a b)
  simpa only [← mul_assoc, M9.FrameAction.FrameGroup.tau_squared, one_mul] using h

theorem matrixSwap_mem (z : matrixGammaFixedField) : matrixSwap z.val ∈ matrixGammaFixedField := by
  intro g
  change M9.FrameProjectiveGeometry.fieldRepresentation
      (M9.FrameAction.FrameGroup.pairHom (g.1,g.2))
      (M9.FrameProjectiveGeometry.fieldRepresentation M9.FrameAction.FrameGroup.tau z.val) = _
  rw [← AlgEquiv.mul_apply, ← map_mul, pairHom_mul_tau, map_mul, AlgEquiv.mul_apply]
  exact congrArg matrixSwap (z.property (g.2,g.1))

theorem matrixSwap_squared : matrixSwap * matrixSwap = 1 := by
  change M9.FrameProjectiveGeometry.fieldRepresentation M9.FrameAction.FrameGroup.tau *
    M9.FrameProjectiveGeometry.fieldRepresentation M9.FrameAction.FrameGroup.tau = _
  rw [← map_mul, M9.FrameAction.FrameGroup.tau_squared, map_one]

def matrixFixedSwap : matrixGammaFixedField ≃ₐ[ℂ] matrixGammaFixedField where
  toFun z := ⟨matrixSwap z.val, matrixSwap_mem z⟩
  invFun z := ⟨matrixSwap z.val, matrixSwap_mem z⟩
  left_inv z := by
    apply Subtype.ext
    exact AlgEquiv.congr_fun matrixSwap_squared z.val
  right_inv z := by
    apply Subtype.ext
    exact AlgEquiv.congr_fun matrixSwap_squared z.val
  map_mul' x y := Subtype.ext (map_mul matrixSwap x.val y.val)
  map_add' x y := Subtype.ext (map_add matrixSwap x.val y.val)
  commutes' c := Subtype.ext (matrixSwap.commutes c)

/-- Exact compatibility with native factor swap and the actual matrix transpose
field action from the frozen projective quotient. -/
theorem nativeSLInvariantFieldEquiv_swap (z : nativeSLFixedField) :
    nativeSLInvariantFieldEquiv (nativeFixedSwap z) =
      matrixFixedSwap (nativeSLInvariantFieldEquiv z) := by
  apply Subtype.ext
  apply projectiveInvariantEmbedding.injective
  change projectiveInvariantEmbedding (nativeSLInvariantFieldEquiv (nativeFixedSwap z)).val =
    projectiveInvariantEmbedding (matrixSwap (nativeSLInvariantFieldEquiv z).val)
  rw [nativeSLInvariantFieldEquiv_raw]
  change rawEmbedding (ConicFramePairSwap.nativeSwap z.val) =
    projectiveInvariantEmbedding (M9.FrameProjectiveGeometry.fieldRepresentation
      M9.FrameAction.FrameGroup.tau (nativeSLInvariantFieldEquiv z).val)
  rw [← pairSwap_embedding, nativeSLInvariantFieldEquiv_raw]
  exact rawEmbedding_swap z.val

end M9Native.ConicFramePairSLFixedField
