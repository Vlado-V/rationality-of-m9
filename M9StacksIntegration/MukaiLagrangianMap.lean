module

public import M9StacksIntegration.MukaiSemiExclusions
public import M9StacksIntegration.CompleteEvaluationGeneration
public import M9StacksIntegration.LagrangianGrassmannian
public import M9StacksIntegration.MukaiSkewNormalization

/-!
# The actual Lagrangian morphism from Mukai's evaluation quotient

The original complete evaluation is classified by the native Grassmannian.
Its actual exterior-square relation gives the morphism to the fixed native
Lagrangian zero scheme, with a literal universal-quotient pullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Matrix Module
open scoped BigOperators TensorProduct

universe u

namespace M9Native.MukaiLagrangianMap

open AlgebraicGeometry.Grassmannian

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) (E : X.Modules)

abbrev H0 := cohomologyOverField k f E 0

def liftedBasis (b : Module.Basis (Fin 6) k (H0 k f E)) :
    Module.Basis (ULift.{u} (Fin 6)) k (H0 k f E) :=
  b.reindex Equiv.ulift.symm

theorem completeEvaluation_eq_basisEvaluation (b : Module.Basis (Fin 6) k (H0 k f E)) :
    MukaiSemiIrreducible.evaluation k f E b =
      CompleteEvaluationGeneration.basisEvaluation f E (liftedBasis k f E b) := by
  unfold MukaiSemiIrreducible.evaluation CompleteEvaluationGeneration.basisEvaluation
  congr 1
  funext i
  simp [MukaiSemiIrreducible.sectionOfH0, CompleteEvaluationGeneration.basisSections,
    liftedBasis, Module.Basis.reindex_apply]

/-- Global generation of the actual sheaf makes its original complete
cohomology-basis evaluation an epimorphism. -/
theorem completeEvaluation_epi (b : Module.Basis (Fin 6) k (H0 k f E))
    (hgen : MukaiSemiIrreducible.GloballyGenerated E) :
    Epi (MukaiSemiIrreducible.evaluation k f E b) := by
  obtain ⟨g⟩ := hgen
  rw [completeEvaluation_eq_basisEvaluation]
  exact CompleteEvaluationGeneration.basisEvaluation_epi_of_freeEvaluation_epi
    f E (liftedBasis k f E b) g.s g.epi

/-- The genuine integral classifying morphism obtained by native
representability from the original quotient class. -/
def integralClassifying (q : QuotientPresentation X 3 6) : X ⟶ scheme.{u} 3 6 :=
  (schemeRepresentableBy 3 6).homEquiv.symm (((functorData 3 6).objEquiv X).symm ⟦q⟧)

def classifying (q : QuotientPresentation X 3 6) : X ⟶ LagrangianGrassmannian.grassmannian k :=
  pullback.lift f (integralClassifying q) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem classifying_projection (q : QuotientPresentation X 3 6) :
    classifying k f q ≫ LagrangianGrassmannian.grassmannianProjection k = f :=
  pullback.lift_fst _ _ _

theorem classifying_class (q : QuotientPresentation X 3 6) :
    (functorData 3 6).objEquiv X ((schemeRepresentableBy 3 6).homEquiv
      (classifying k f q ≫ pullback.snd _ _)) = ⟦q⟧ := by
  rw [classifying, pullback.lift_snd, integralClassifying,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem classifying_pullback_isomorphic (q : QuotientPresentation X 3 6) :
    (pullbackPresentation (classifying k f q) (LagrangianGrassmannian.universalQuotient k)).Isomorphic q :=
  LagrangianGrassmannian.pullbackUniversal_isomorphic k (classifying k f q) q
    (classifying_class k f q)

/-- The original universal quotient restricted along the actual native
LG closed immersion. -/
def lagrangianQuotient : QuotientPresentation (LagrangianGrassmannian.space k) 3 6 :=
  pullbackPresentation (LagrangianGrassmannian.inclusion k) (LagrangianGrassmannian.universalQuotient k)

/-- The zero-ideal universal property factors the actual classifying
morphism and recovers the original quotient by literal pullback. -/
theorem exists_lagrangianFactor (q : QuotientPresentation X 3 6)
    (hσ : LagrangianGrassmannian.AnnihilatesSigma X q.map) :
    ∃ g : X ⟶ LagrangianGrassmannian.space k,
      g ≫ LagrangianGrassmannian.projection k = f ∧
      Nonempty ((Scheme.Modules.pullback g).obj (lagrangianQuotient k).target ≅ q.target) := by
  obtain ⟨e, he⟩ := classifying_pullback_isomorphic k f q
  have hkill : LagrangianGrassmannian.AnnihilatesSigma X
      (pullbackPresentation (classifying k f q) (LagrangianGrassmannian.universalQuotient k)).map :=
    (LagrangianGrassmannian.annihilatesSigma_iff_of_iso X _ q.map e he).mpr hσ
  obtain ⟨g, hg⟩ := (LagrangianGrassmannian.factorsThrough_iff_pullbackQuotient_annihilates
    k (classifying k f q)).mpr hkill
  refine ⟨g, ?_, ?_⟩
  · change (g ≫ LagrangianGrassmannian.inclusion k) ≫
      LagrangianGrassmannian.grassmannianProjection k = f
    rw [hg, classifying_projection]
  · let ec := asIso ((Scheme.Modules.pullbackComp g (LagrangianGrassmannian.inclusion k)).hom.app
      (LagrangianGrassmannian.quotientBundle k))
    let eh := eqToIso (congrArg (fun h : X ⟶ LagrangianGrassmannian.grassmannian k =>
      (Scheme.Modules.pullback h).obj (LagrangianGrassmannian.quotientBundle k)) hg)
    exact ⟨ec ≪≫ eh ≪≫ e⟩

def basisSigma (b : Module.Basis (Fin 6) k (H0 k f E)) : ⋀[k]^2 (H0 k f E) :=
  ∑ i : Fin 3, exteriorPower.ιMulti k 2 ![b (i.castAdd 3), b (Fin.natAdd 3 i)]

theorem evaluation_freeVector (b : Module.Basis (Fin 6) k (H0 k f E)) (i : Fin 6) :
    (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation k f E b) ⊤)
      (LagrangianGrassmannian.freeVector X i) =
      (cohomologyOverFieldZeroLinearIso k f E).hom (b i) := by
  change (MukaiSemiIrreducible.evaluation k f E b).val.app (op ⊤)
    (LagrangianGrassmannian.freeVector X i) = _
  simpa [LagrangianGrassmannian.freeVector, SheafOfModules.freeSection,
    SheafOfModules.freeHomEquiv, Category.comp_id] using
      TupleEvaluationFiber.evaluation_freeSection_top k f E b i

/-- Annihilation of the fixed sheaf bivector is exactly the actual
native exterior-evaluation relation in the same H0 basis. -/
theorem evaluation_annihilatesSigma_iff (b : Module.Basis (Fin 6) k (H0 k f E)) :
    LagrangianGrassmannian.AnnihilatesSigma X (MukaiSemiIrreducible.evaluation k f E b) ↔
      ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0 := by
  have h : (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E 2)).hom
      (ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b)) =
      (LagrangianGrassmannian.exteriorPowerMap X (MukaiSemiIrreducible.evaluation k f E b) 2).app ⊤
        (LagrangianGrassmannian.sigmaSection X) := by
    calc
      _ = ∑ i : Fin 3, (cohomologyOverFieldZeroLinearIso k f
          (Scheme.Modules.exteriorPower E 2)).hom
          (ExteriorEvaluation.lambda k f E 2
            (exteriorPower.ιMulti k 2 ![b (i.castAdd 3), b (Fin.natAdd 3 i)])) := by
        simp only [basisSigma, map_sum]
      _ = ∑ i : Fin 3, LagrangianGrassmannian.wedgeSection X E
          ((cohomologyOverFieldZeroLinearIso k f E).hom (b (i.castAdd 3)))
          ((cohomologyOverFieldZeroLinearIso k f E).hom (b (Fin.natAdd 3 i))) := by
        apply Finset.sum_congr rfl
        intro i _
        refine (ExteriorEvaluation.lambda_ιMulti k f E 2
          ![b (i.castAdd 3), b (Fin.natAdd 3 i)]).trans ?_
        rw [ExteriorEvaluation.sectionComparison_ιMulti]
        congr 1
        funext j
        fin_cases j <;> rfl
      _ = _ := by
        simp only [LagrangianGrassmannian.sigmaSection, map_sum,
          LagrangianGrassmannian.exteriorPowerMap_wedgeSection, evaluation_freeVector]
  change _ = 0 ↔ _ = 0
  rw [← h]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E 2)).hom).injective)

def standardSigma : MukaiWedgeKernel.Bivector k 6 :=
  ∑ i : Fin 3, exteriorPower.ιMulti k 2
    ![Pi.single (i.castAdd 3) 1, Pi.single (Fin.natAdd 3 i) 1]

def standardMatrix : Matrix (Fin 6) (Fin 6) k :=
  -(Matrix.J (Fin 3) k).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem standardSigma_matrix : MukaiWedgeKernel.bivectorMatrix k 6 (standardSigma k) =
    standardMatrix k := by
  ext i j
  refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  all_goals
    simp only [standardMatrix, Matrix.neg_apply, Matrix.submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
    fin_cases i <;> fin_cases j <;>
    norm_num [standardSigma, map_sum, MukaiWedgeKernel.bivectorMatrix_ιMulti,
      Matrix.vecMulVec_apply, Matrix.J, Matrix.fromBlocks, Fin.sum_univ_succ, Pi.single_apply]

/-- The explicit skew normalization in the original first-three/last-three
coordinate order of the fixed native LG. -/
theorem exists_normalization_six [CharZero k]
    (B : Matrix (Fin 6) (Fin 6) k) (hB : B.det ≠ 0) (hskew : Bᵀ = -B)
    (A : Matrix (Fin 3) (Fin 6) k) (hA : Function.Surjective A.mulVec)
    (hiso : A * B * Aᵀ = 0) :
    ∃ P : Matrix (Fin 6) (Fin 6) k, IsUnit P ∧ P * standardMatrix k * Pᵀ = B := by
  let e : (Fin 3 ⊕ Fin 3) ≃ Fin 6 := finSumFinEquiv
  let R := Matrix.reindexAlgEquiv k k e.symm
  let Bs := B.submatrix e e
  let As := A.submatrix id e
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)
  have hBsu : IsUnit Bs := hBu.map R.toMonoidHom
  have hBs : Bs.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Bs).mp hBsu).ne_zero
  have hskews : Bsᵀ = -Bs := by
    calc
      _ = Bᵀ.submatrix e e := by
        change (B.submatrix e e)ᵀ = _
        rw [Matrix.transpose_submatrix]
      _ = (-B).submatrix e e := by rw [hskew]
      _ = _ := rfl
  have hAs : Function.Surjective As.mulVec := by
    intro w
    obtain ⟨v, hv⟩ := hA w
    refine ⟨v ∘ e, ?_⟩
    rw [show As = A.submatrix id e from rfl, Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def, Equiv.apply_symm_apply, id_eq] using hv
  have hisos : As * Bs * Asᵀ = 0 := by
    simp only [As, Bs, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    simpa only [Matrix.submatrix_id_id] using hiso
  obtain ⟨P, hPu, hP⟩ := MukaiSkewNormalization.exists_normalization Bs hBs hskews As hAs hisos
  refine ⟨R.symm P, hPu.map R.symm.toMonoidHom, ?_⟩
  have hh := congrArg R.symm hP
  simp only [map_mul] at hh
  have ht : R.symm Pᵀ = (R.symm P)ᵀ := by ext i j; rfl
  have hb : R.symm Bs = B := R.symm_apply_apply B
  have hj : R.symm (-Matrix.J (Fin 3) k) = standardMatrix k := rfl
  rw [ht, hb, hj] at hh
  exact hh

/-- The matrix normalization supplies an actual H0 basis whose standard
bivector is the prescribed original bivector. -/
theorem exists_basisSigma_of_matrix_normalization
    (b : Module.Basis (Fin 6) k (H0 k f E)) (w : ⋀[k]^2 (H0 k f E))
    (P : Matrix (Fin 6) (Fin 6) k) (hPu : IsUnit P)
    (hP : P * standardMatrix k * Pᵀ = MukaiWedgeKernel.kernelMatrix k f E b w) :
    ∃ a : Module.Basis (Fin 6) k (H0 k f E), basisSigma k f E a = w := by
  let eP : (Fin 6 → k) ≃ₗ[k] (Fin 6 → k) := LinearEquiv.ofBijective P.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hPu, Matrix.mulVec_surjective_iff_isUnit.mpr hPu⟩
  let a := (Pi.basisFun k (Fin 6)).map (eP.trans b.equivFun.symm)
  refine ⟨a, ?_⟩
  apply MukaiWedgeKernel.kernelMatrix_injective k f E b
  have hc : MukaiWedgeKernel.coordinateBivector k f E b (basisSigma k f E a) =
      ExteriorAlgebra.powMapₛₗ 2 (RingHom.id k) (MukaiWedgeKernel.matrixEvaluation (RingHom.id k) P)
        (standardSigma k) := by
    simp only [MukaiWedgeKernel.coordinateBivector, basisSigma, standardSigma, map_sum,
      exteriorPower.map_apply_ιMulti, ExteriorAlgebra.powMapₛₗ_ιMulti]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext j
    fin_cases j <;>
      simp [a, Module.Basis.map_apply, Module.Basis.equivFun_apply, eP,
        MukaiWedgeKernel.matrixEvaluation, MukaiWedgeKernel.coefficientVectorMap] <;>
      ext r <;> simp [Finset.sum_apply, Pi.smul_apply, Finsupp.single_apply, Matrix.col_apply]
  change MukaiWedgeKernel.bivectorMatrix k 6
      (MukaiWedgeKernel.coordinateBivector k f E b (basisSigma k f E a)) = _
  rw [hc, MukaiWedgeKernel.bivectorMatrix_naturality, standardSigma_matrix]
  rw [show (standardMatrix k).map (RingHom.id k) = standardMatrix k from rfl]
  exact hP

/-- Epimorphy of the original sheaf map gives surjectivity on its actual
residue fibres, by stalk surjectivity and right exact scalar extension. -/
theorem inducedFiberMap_surjective {F G : X.Modules} (q : F ⟶ G) [Epi q] (x : X) :
    Function.Surjective (TupleEvaluationFiber.inducedFiberMap q x) := by
  let := TupleEvaluationFiber.residueAlgebra x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) F x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) G x
  have hs : Function.Surjective
      (Stacks.SheafOfModules.FlatShortExact.stalkLinearMap (X := X.toRingedSpace) q x) :=
    (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap q).mp inferInstance x
  exact LinearMap.lTensor_surjective (X.residueField x) hs

theorem tupleMap_surjective {r : ℕ} (s : Fin r → H0 k f E)
    [Epi (MukaiSemiIrreducible.evaluation k f E s)] (x : X) :
    Function.Surjective (TupleEvaluationFiber.tupleMap k f E s x) := by
  rw [← TupleEvaluationFiber.evaluationFiber_comp_coordinates]
  exact (inducedFiberMap_surjective (MukaiSemiIrreducible.evaluation k f E s) x).comp
    (TupleEvaluationFiber.freeFiberCoordinates r x).surjective

variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- The actual quotient has literally `E` as target and the original
complete-basis evaluation as its map. -/
def evaluationQuotient (b : Module.Basis (Fin 6) k (H0 k f E))
    (hgen : MukaiSemiIrreducible.GloballyGenerated E) : QuotientPresentation X 3 6 where
  target := E
  map := MukaiSemiIrreducible.evaluation k f E b
  map_epi := completeEvaluation_epi k f E b hgen
  finiteLocallyFree := by simpa using
    (inferInstance : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3)

theorem completeEvaluation_rank (b : Module.Basis (Fin 6) k (H0 k f E))
    (hgen : MukaiSemiIrreducible.GloballyGenerated E) (x : X) :
    MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E b) x = 3 := by
  let := completeEvaluation_epi k f E b hgen
  rw [TupleEvaluationFiber.mapRankAt_evaluation_eq_finrank_tupleMap,
    LinearMap.range_eq_top.mpr (tupleMap_surjective k f E b x), finrank_top]
  exact TupleEvaluationFiber.finrank_fiber E 3 x

section ClosedPoint

variable [IsAlgClosed k] [LocallyOfFiniteType f]

def closedMatrix (b : Module.Basis (Fin 6) k (H0 k f E)) (x : X)
    (hx : IsClosed ({x} : Set X)) : Matrix (Fin 3) (Fin 6) k :=
  fun i j => MukaiSemiExclusions.closedEvaluation k f E x hx (b j) i

theorem closedMatrix_rank (b : Module.Basis (Fin 6) k (H0 k f E)) (x : X)
    (hx : IsClosed ({x} : Set X)) : (closedMatrix k f E b x hx).rank =
      MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E b) x := by
  rw [Matrix.rank_eq_finrank_span_cols, MukaiSemiExclusions.closedEvaluation_rank k f E x hx]
  rfl

theorem closedMatrix_surjective (b : Module.Basis (Fin 6) k (H0 k f E))
    (hgen : MukaiSemiIrreducible.GloballyGenerated E) (x : X)
    (hx : IsClosed ({x} : Set X)) : Function.Surjective (closedMatrix k f E b x hx).mulVec := by
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  rw [closedMatrix_rank, completeEvaluation_rank k f E b hgen x]
  rfl

/-- The original residue matrix is exactly scalar extension of the
closed-point matrix over the original base field. -/
theorem closedMatrix_map (b : Module.Basis (Fin 6) k (H0 k f E)) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (closedMatrix k f E b x hx).map (TupleEvaluationFiber.residueBaseRingMap k f x) =
      MukaiWedgeKernel.fiberMatrix k f E b x := by
  ext i j
  have hb : b.equivFun.symm (Pi.single j 1) = b j := by simp
  simp only [Matrix.map_apply, closedMatrix, MukaiWedgeKernel.fiberMatrix,
    MukaiWedgeKernel.semilinearMatrix, MukaiWedgeKernel.coordinateFiberEvaluation,
    LinearMap.comp_apply]
  change (MukaiSemiExclusions.closedFieldEquiv k f x hx)
      ((MukaiSemiExclusions.closedFieldEquiv k f x hx).symm
        ((TupleEvaluationFiber.fiberBasis E 3 x).equivFun
          (TupleEvaluationFiber.sectionValue k f E x (b j)) i)) = _
  rw [RingEquiv.apply_symm_apply]
  exact congrArg (fun v : H0 k f E => (TupleEvaluationFiber.fiberBasis E 3 x).equivFun
    (TupleEvaluationFiber.sectionValue k f E x v) i) hb.symm

/-- Actual exterior-evaluation vanishing gives the isotropic matrix
sandwich over the base field, with no isotropy hypothesis on the matrix. -/
theorem closedMatrix_isotropic (b : Module.Basis (Fin 6) k (H0 k f E)) (x : X)
    (hx : IsClosed ({x} : Set X)) (w : ⋀[k]^2 (H0 k f E))
    (hw : ExteriorEvaluation.lambda k f E 2 w = 0) :
    closedMatrix k f E b x hx * MukaiWedgeKernel.kernelMatrix k f E b w *
      (closedMatrix k f E b x hx)ᵀ = 0 := by
  let φ := TupleEvaluationFiber.residueBaseRingMap k f x
  have hκ := MukaiWedgeKernel.sandwich_zero_of_exterior_zero φ
    (MukaiWedgeKernel.fiberMatrix k f E b x) (MukaiWedgeKernel.coordinateBivector k f E b w)
    (MukaiWedgeKernel.coordinate_fiber_exterior_zero k f E b x w hw)
  have hm : (closedMatrix k f E b x hx * MukaiWedgeKernel.kernelMatrix k f E b w *
      (closedMatrix k f E b x hx)ᵀ).map φ = 0 := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, closedMatrix_map]
    exact hκ
  have hφ (z : k) : MukaiSemiExclusions.closedFieldEquiv k f x hx z = φ z := rfl
  ext i j
  apply (MukaiSemiExclusions.closedFieldEquiv k f x hx).injective
  simpa only [hφ, Matrix.map_apply, Matrix.zero_apply, map_zero] using congrFun (congrFun hm i) j

end ClosedPoint

section Construction

variable [IsIntegral X] [IsAlgClosed k] [CharZero k] [LocallyOfFiniteType f]
  [FiniteDimensional k (H0 k f E)]
  [FiniteDimensional k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0)]

/-- The nondegenerate generator of the actual native exterior kernel is
normalized using the actual closed-point evaluation of the original bundle. -/
theorem exists_kernel_basis
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    ∃ b : Module.Basis (Fin 6) k (H0 k f E),
      ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0 := by
  let b : Module.Basis (Fin 6) k (H0 k f E) :=
    (Module.finBasis k (H0 k f E)).reindex (finCongr h6)
  obtain ⟨hdim, _⟩ := MukaiSemiExclusions.lambdaTwo_kernel_line_and_surjective_of_semi
    k f E h6 h14 hsemi
  let := Module.nontrivial_of_finrank_eq_succ (n := 0) hdim
  obtain ⟨w, hw⟩ := exists_ne (0 : (MukaiWedgeKernel.LambdaTwo k f E).ker)
  have hw0 : w.val ≠ 0 := fun h => hw (Subtype.ext h)
  have hLambda : ExteriorEvaluation.lambda k f E 2 w.val = 0 := w.property
  obtain ⟨p, hp⟩ := BaseFieldPoints.exists_point f
  let c := pointEquivClosedPoint f ⟨p, hp⟩
  let x := c.val
  have hx : IsClosed ({x} : Set X) := c.property
  let B := MukaiWedgeKernel.kernelMatrix k f E b w.val
  have hB : B.det ≠ 0 := MukaiSemiExclusions.lambdaTwo_kernel_nondegenerate_of_semi
    k f E b hsemi w.val hw0 hLambda
  have hskew : Bᵀ = -B := MukaiWedgeKernel.bivectorMatrix_skew k 6
    (MukaiWedgeKernel.coordinateBivector k f E b w.val)
  obtain ⟨P, hPu, hP⟩ := exists_normalization_six k B hB hskew (closedMatrix k f E b x hx)
    (closedMatrix_surjective k f E b hgen x hx) (closedMatrix_isotropic k f E b x hx w.val hLambda)
  obtain ⟨a, ha⟩ := exists_basisSigma_of_matrix_normalization k f E b w.val P hPu hP
  exact ⟨a, by rw [ha]; exact hLambda⟩

/-- The actual morphism to the fixed native LG, with the actual
universal quotient pulling back to the original bundle `E`. -/
theorem exists_lagrangianMap
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    ∃ g : X ⟶ LagrangianGrassmannian.space k,
      g ≫ LagrangianGrassmannian.projection k = f ∧
      Nonempty ((Scheme.Modules.pullback g).obj (lagrangianQuotient k).target ≅ E) := by
  obtain ⟨b, hb⟩ := exists_kernel_basis k f E hgen h6 h14 hsemi
  exact exists_lagrangianFactor k f (evaluationQuotient k f E b hgen)
    ((evaluation_annihilatesSigma_iff k f E b).mpr hb)

def toLagrangian
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    X ⟶ LagrangianGrassmannian.space k :=
  Classical.choose (exists_lagrangianMap k f E hgen h6 h14 hsemi)

@[reassoc (attr := simp)] theorem toLagrangian_over
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    toLagrangian k f E hgen h6 h14 hsemi ≫ LagrangianGrassmannian.projection k = f :=
  (Classical.choose_spec (exists_lagrangianMap k f E hgen h6 h14 hsemi)).1

def universalQuotientPullbackIso
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    (Scheme.Modules.pullback (toLagrangian k f E hgen h6 h14 hsemi)).obj
      (lagrangianQuotient k).target ≅ E :=
  Classical.choice (Classical.choose_spec (exists_lagrangianMap k f E hgen h6 h14 hsemi)).2

end Construction

end M9Native.MukaiLagrangianMap
