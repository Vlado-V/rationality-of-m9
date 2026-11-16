module

public import M9StacksIntegration.LagrangianAdmissibleMinors
public import M9StacksIntegration.LagrangianTranslatedCharts

/-! The eight actual admissible symplectic-coordinate charts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianAdmissibleCharts

open M9Native.LagrangianAdmissibleMinors M9Native.LagrangianGrassmannian
open M9Native.LagrangianMatrixChart M9Native.LagrangianTransitivity
open M9Native.LagrangianSymplecticAction M9Native.LagrangianTranslatedCharts
open AlgebraicGeometry.Grassmannian

variable (R : Type u) [CommRing R]

def keep (s : Choice) (i : Fin 3) : R := if s i then 0 else 1
def take (s : Choice) (i : Fin 3) : R := if s i then 1 else 0

def swapMatrix (s : Choice) : Matrix SplitIndex SplitIndex R :=
  Matrix.fromBlocks (Matrix.diagonal (keep R s)) (-Matrix.diagonal (take R s))
    (Matrix.diagonal (take R s)) (Matrix.diagonal (keep R s))

theorem swapMatrix_symplectic (s : Choice) : swapMatrix R s ∈ Matrix.symplecticGroup (Fin 3) R := by
  unfold swapMatrix
  apply SymplecticGroup.fromBlocks_mem_iff.mpr
  refine ⟨?_,?_,?_⟩
  all_goals
    simp only [Matrix.diagonal_transpose,Matrix.transpose_neg,Matrix.neg_mul,Matrix.mul_neg,
      Matrix.diagonal_mul_diagonal,sub_neg_eq_add]
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hs : s i <;> simp [keep,take,hs]
    · simp [hij]

def swap (s : Choice) : Matrix.symplecticGroup (Fin 3) R := ⟨swapMatrix R s,swapMatrix_symplectic R s⟩

theorem matrixSix_apply_split (g : Matrix.symplecticGroup (Fin 3) R) (i j : SplitIndex) :
    matrixSix R g (splitIndex i) (splitIndex j)=(g : Matrix SplitIndex SplitIndex R) i j := by
  simp only [matrixSix,Matrix.submatrix_apply,Equiv.symm_apply_apply]

theorem swap_column (s : Choice) (j : Fin 3) :
    (matrixSix R (swap R s)).col (j.castAdd 3)=Pi.single (column s j) 1 := by
  funext i
  obtain ⟨i,rfl⟩ := splitIndex.surjective i
  cases i with
  | inl i =>
    change matrixSix R (swap R s) (splitIndex (Sum.inl i)) (splitIndex (Sum.inl j))=_
    rw [matrixSix_apply_split]
    change swapMatrix R s (Sum.inl i) (Sum.inl j)=_
    fin_cases i <;> fin_cases j
    all_goals
      simp [swapMatrix,Matrix.fromBlocks,keep,take,column,
        splitIndex,finSumFinEquiv,Pi.single_apply]; try (split_ifs <;> simp_all)
  | inr i =>
    change matrixSix R (swap R s) (splitIndex (Sum.inr i)) (splitIndex (Sum.inl j))=_
    rw [matrixSix_apply_split]
    change swapMatrix R s (Sum.inr i) (Sum.inl j)=_
    fin_cases i <;> fin_cases j
    all_goals
      simp [swapMatrix,Matrix.fromBlocks,take,column,
        splitIndex,finSumFinEquiv,Pi.single_apply]; try (split_ifs <;> simp_all)

theorem mul_swap_firstColumns (M : Matrix (Fin 3) (Fin 6) R) (s : Choice) :
    (M*matrixSix R (swap R s)).submatrix id firstPivot=M.submatrix id (embedding s) := by
  ext i j
  change (M.mulVec ((matrixSix R (swap R s)).col (j.castAdd 3))) i=M i (column s j)
  rw [swap_column,Matrix.mulVec_single_one]
  rfl

section Geometry

variable (K : Type u) [Field K]

theorem constantSwap_column {T : Scheme.{u}} (b : T ⟶ Spec (.of K)) (s : Choice) (j : Fin 3) :
    (constantMatrix K b (swap K s)).col (j.castAdd 3)=Pi.single (column s j) 1 := by
  funext i
  have h := congrFun (swap_column K s j) i
  change matrixSix K (swap K s) i (j.castAdd 3)=((Pi.single (column s j) (1 : K)) : Fin 6 → K) i at h
  change scalarMap K b (matrixSix K (swap K s) i (j.castAdd 3))=_
  rw [h]
  by_cases hi : i=column s j <;> simp [hi]

theorem firstSubmap_matrix {T : Scheme.{u}} (q : freeOn T 6 ⟶ freeOn T 3) :
    Stacks.FreeSheafMatrix.toMatrix (coordinateSubmap T 3 6 firstPivot ≫ q)=
      (Stacks.FreeSheafMatrix.toMatrix q).submatrix id firstPivot := by
  change Stacks.FreeSheafMatrix.toMatrix
    (SheafOfModules.freeMap (R:=T.ringCatSheaf)
      (fun i : ULift.{u} (Fin 3) => ULift.up (firstPivot i.down)) ≫ q)=_
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,Stacks.FreeSheafMatrix.toMatrix_freeMap]
  ext i j
  rw [Matrix.mul_apply,Matrix.submatrix_apply]
  simp only [Matrix.of_apply,id,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]

theorem firstSubmap_swap_matrix {T : Scheme.{u}} (b : T ⟶ Spec (.of K))
    (q : freeOn T 6 ⟶ freeOn T 3) (s : Choice) :
    Stacks.FreeSheafMatrix.toMatrix
      (coordinateSubmap T 3 6 firstPivot ≫ (constantFreeIso K b (swap K s)).hom ≫ q)=
        (Stacks.FreeSheafMatrix.toMatrix q).submatrix id (embedding s) := by
  rw [firstSubmap_matrix,Stacks.FreeSheafMatrix.toMatrix_comp,constantFreeIso_matrix]
  ext i j
  change ((Stacks.FreeSheafMatrix.toMatrix q).mulVec
    ((constantMatrix K b (swap K s)).col (j.castAdd 3))) i=
      Stacks.FreeSheafMatrix.toMatrix q i (column s j)
  rw [constantSwap_column,Matrix.mulVec_single_one]
  rfl

def chart (s : Choice) : Spec (.of (MvPolynomial (Fin 6) K)) ⟶ space K :=
  translatedBigCell K (swap K s)⁻¹

instance chart_isOpenImmersion (s : Choice) : IsOpenImmersion (chart K s) := by
  dsimp [chart]
  infer_instance

@[reassoc (attr := simp)] theorem chart_projection (s : Choice) :
    chart K s ≫ projection K=Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ:=Fin 6) (R:=K))) :=
  translatedBigCell_projection K _

/-- An actual unit admissible minor yields a factor through the corresponding actual affine-six chart. -/
theorem exists_chart_factor_of_isUnit_minor {T : Scheme.{u}} (p : T ⟶ space K)
    (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅ freeOn T 3)
    (s : Choice)
    (hu : IsUnit (admissibleMinor
      (Stacks.FreeSheafMatrix.toMatrix
        ((pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom)) s)) :
    ∃ z : T ⟶ Spec (.of (MvPolynomial (Fin 6) K)),z ≫ chart K s=p := by
  let q0 := pullbackPresentation (p ≫ inclusion K) (universalQuotient K)
  let q := q0.map ≫ e.hom
  let acted := p ≫ action K (swap K s)
  let qa := pullbackPresentation (acted ≫ inclusion K) (universalQuotient K)
  obtain ⟨a,ha⟩ := pullback_action_isomorphic K p (swap K s)
  let e' : qa.target ≅ freeOn T 3 := a ≪≫ e
  have hacted : qa.map ≫ e'.hom=(constantFreeIso K (p ≫ projection K) (swap K s)).hom ≫ q := by
    rw [Iso.trans_hom,← Category.assoc,ha]
    exact Category.assoc _ _ _
  let r := coordinateSubmap T 3 6 firstPivot ≫ (constantFreeIso K (p ≫ projection K) (swap K s)).hom ≫ q
  have hdet : IsUnit (Stacks.FreeSheafMatrix.toMatrix r).det := by
    rw [firstSubmap_swap_matrix]
    exact hu
  have : IsIso r := (Stacks.FreeSheafMatrix.isIso_iff_isUnit_det r).mpr hdet
  have hce : Epi ((coordinateSubmap T 3 6 firstPivot ≫ qa.map) ≫ e'.hom) := by
    rw [Category.assoc,hacted]
    exact IsIso.epi_of_iso r
  have hc : Epi (coordinateSubmap T 3 6 firstPivot ≫ qa.map) :=
    (epi_comp_iff_of_isIso _ e'.hom).mp hce
  obtain ⟨a0,ha0⟩ := exists_matrixChart_factor_of_epi K (acted ≫ inclusion K) hc
  let l : T ⟶ lagrangianChart K := pullback.lift a0 acted ha0
  let z := l ≫ (lagrangianChartIsoPolynomialSix K).hom
  have hz : z ≫ bigCell K=acted := by
    rw [bigCell,Category.assoc,(lagrangianChartIsoPolynomialSix K).hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  refine ⟨z,?_⟩
  rw [chart,translatedBigCell,← Category.assoc,hz]
  change (p ≫ action K (swap K s)) ≫ action K (swap K s)⁻¹=p
  rw [Category.assoc,action_mul,mul_inv_cancel,action_one,Category.comp_id]

theorem omega_matrix_map {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (M : Matrix (Fin 3) (Fin 6) A) (i j : Fin 3) :
    M9Native.LagrangianRing.omega B (M.map ρ i) (M.map ρ j)=
      ρ (M9Native.LagrangianRing.omega A (M i) (M j)) := by
  simp [M9Native.LagrangianRing.omegaValue,Matrix.map_apply,map_sum,map_sub,map_mul]

/-- Every actual field-valued point factors through one of the eight charts,
including points valued in arbitrary extensions of the structural field. -/
theorem exists_chart_factor_point (L : Type u) [Field L] (p : Spec (.of L) ⟶ space K) :
    ∃ (s : Choice) (z : Spec (.of L) ⟶ Spec (.of (MvPolynomial (Fin 6) K))),z ≫ chart K s=p := by
  obtain ⟨ι,h,e,hh,he⟩ := exists_native_chart_presentation K L p
  let q := chartQuotientMap 3 6 ι h
  let MΓ := Stacks.FreeSheafMatrix.toMatrix q
  let ρ := (Scheme.ΓSpecIso (.of L)).hom.hom
  let M := MΓ.map ρ
  have hpivΓ : MΓ.submatrix id ι=1 := by
    change (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι h)).submatrix id ι=1
    rw [toMatrix_chartQuotientMap]
    ext i j
    simpa only [Matrix.submatrix_apply,id_eq,Matrix.one_apply] using
      (chartMatrix_apply_self (k:=3) (n:=6) (R:=Γ(Spec (.of L),⊤)) ι
        (AffineSpace.toSpecMvPolyIntEquiv _ h) i j)
  have hpiv : M.submatrix id ι=1 := by
    change (MΓ.submatrix id ι).map ρ=1
    rw [hpivΓ]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hsurj := matrix_surjective_of_pivots L M ι hpiv
  have hσ := (factorsThrough_iff_pullbackQuotient_annihilates K (p ≫ inclusion K)).mp ⟨p,rfl⟩
  have hq : AnnihilatesSigma (Spec (.of L)) q :=
    (annihilatesSigma_iff_of_iso (Spec (.of L)) _ _ e he).mp hσ
  have hωΓ := M9Native.LagrangianPlucker.rows_isotropic_of_annihilatesSigma (Spec (.of L)) q hq
  have hω (i j : Fin 3) : M9Native.LagrangianRing.omega L (M i) (M j)=0 := by
    rw [omega_matrix_map, hωΓ,map_zero]
  obtain ⟨s,hs⟩ := exists_isUnit_admissibleMinor M hsurj hω
  have hdet : admissibleMinor M s=ρ (admissibleMinor MΓ s) := by
    change ((MΓ.submatrix id (embedding s)).map ρ).det=ρ (MΓ.submatrix id (embedding s)).det
    exact (RingHom.map_det ρ _).symm
  have hu := hs.map (Scheme.ΓSpecIso (.of L)).inv.hom.toMonoidHom
  rw [hdet] at hu
  change IsUnit ((Scheme.ΓSpecIso (.of L)).inv
    ((Scheme.ΓSpecIso (.of L)).hom (admissibleMinor MΓ s))) at hu
  rw [(Scheme.ΓSpecIso (.of L)).hom_inv_id_apply] at hu
  refine ⟨s,exists_chart_factor_of_isUnit_minor K p e s ?_⟩
  rw [he]
  exact hu

/-- The eight admissible affine-six open charts cover all actual scheme points over any field. -/
theorem charts_cover (x : space K) : ∃ s : Choice,x ∈ Set.range (chart K s) := by
  obtain ⟨s,z,hz⟩ := exists_chart_factor_point K ((space K).residueField x)
    ((space K).fromSpecResidueField x)
  refine ⟨s,z (IsLocalRing.closedPoint ((space K).residueField x)),?_⟩
  exact (congrArg (fun f : Spec (.of ((space K).residueField x)) ⟶ space K =>
    f (IsLocalRing.closedPoint ((space K).residueField x))) hz).trans
      ((space K).fromSpecResidueField_apply x _)

def admissibleCover : (space K).OpenCover :=
  Scheme.Cover.mkOfCovers Choice (fun _ => Spec (.of (MvPolynomial (Fin 6) K))) (chart K)
    (fun x => by obtain ⟨s,y,hy⟩ := charts_cover K x; exact ⟨s,y,hy⟩)

end Geometry

end M9Native.LagrangianAdmissibleCharts

end
