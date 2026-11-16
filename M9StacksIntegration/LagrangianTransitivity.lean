module

public import M9StacksIntegration.LagrangianSymplecticMatrix
public import M9StacksIntegration.LagrangianRingCoordinates
public import M9StacksIntegration.LagrangianPlucker
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Actual symplectic normal form in the six native coordinates

The matrix completion is transported from Mathlib's `Fin 3 ⊕ Fin 3` convention
to the native `e₀,e₁,e₂,f₀,f₁,f₂` convention. The resulting automorphism
preserves the actual alternating form and sends a surjective quotient
annihilating the actual bivector to the first-three-coordinate projection.
No complement or normal-form hypothesis is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open Matrix Module exteriorPower
open scoped BigOperators

universe u

namespace M9Native.LagrangianTransitivity

variable (R : Type u) [CommRing R]

abbrev SplitIndex := Fin 3 ⊕ Fin 3

/-- The native first-three/last-three order on the six coordinates. -/
def splitIndex : SplitIndex ≃ Fin 6 := finSumFinEquiv

def splitMatrix (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) SplitIndex R :=
  M.submatrix id splitIndex

def firstBlock (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M i (j.castAdd 3)

def lastBlock (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M i (Fin.natAdd 3 j)

omit [CommRing R] in
theorem splitMatrix_eq (M : Matrix (Fin 3) (Fin 6) R) :
    splitMatrix R M = Matrix.fromCols (firstBlock R M) (lastBlock R M) := by
  ext i (j | j) <;> rfl

theorem splitMatrix_gram (M : Matrix (Fin 3) (Fin 6) R) :
    splitMatrix R M * Matrix.J (Fin 3) R * (splitMatrix R M)ᵀ =
      lastBlock R M * (firstBlock R M)ᵀ - firstBlock R M * (lastBlock R M)ᵀ := by
  rw [splitMatrix_eq,Matrix.J,Matrix.fromCols_mul_fromBlocks,
    Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero,Matrix.mul_one,Matrix.mul_neg,Matrix.neg_mul,zero_add,add_zero]
  abel

theorem splitMatrix_gram_entry (M : Matrix (Fin 3) (Fin 6) R) (i j : Fin 3) :
    (splitMatrix R M * Matrix.J (Fin 3) R * (splitMatrix R M)ᵀ) i j =
      -M9Native.LagrangianRing.omega R (M i) (M j) := by
  rw [splitMatrix_gram]
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,firstBlock,lastBlock,
    M9Native.LagrangianRing.omega_apply,M9Native.LagrangianRing.omegaValue,
    M9Native.LagrangianRing.eIndex,M9Native.LagrangianRing.fIndex,← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem splitMatrix_isotropic (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j, M9Native.LagrangianRing.omega R (M i) (M j)=0) :
    splitMatrix R M * Matrix.J (Fin 3) R * (splitMatrix R M)ᵀ=0 := by
  ext i j
  rw [splitMatrix_gram_entry,hM,neg_zero]
  rfl

theorem splitMatrix_surjective (M : Matrix (Fin 3) (Fin 6) R)
    (hM : Function.Surjective M.mulVec) : Function.Surjective (splitMatrix R M).mulVec := by
  intro w
  obtain ⟨v,hv⟩ := hM w
  refine ⟨v ∘ splitIndex,?_⟩
  rw [splitMatrix,Matrix.submatrix_mulVec_equiv]
  simpa only [Function.comp_def,Equiv.apply_symm_apply,id_eq] using hv

/-- The quotient `[I|0]` in the paper's actual coordinate order. -/
def standardQuotient : Matrix (Fin 3) (Fin 6) R :=
  (Matrix.fromCols (1 : Matrix (Fin 3) (Fin 3) R) 0).submatrix id splitIndex.symm

@[simp] theorem standardQuotient_first (i j : Fin 3) :
    standardQuotient R i (j.castAdd 3) = if i=j then 1 else 0 := by
  change Matrix.fromCols (1 : Matrix (Fin 3) (Fin 3) R) 0 i
    (finSumFinEquiv.symm (j.castAdd 3)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem standardQuotient_last (i j : Fin 3) :
    standardQuotient R i (Fin.natAdd 3 j)=0 := by
  change Matrix.fromCols (1 : Matrix (Fin 3) (Fin 3) R) 0 i
    (finSumFinEquiv.symm (Fin.natAdd 3 j)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- A native Mathlib symplectic matrix in the paper's six-coordinate order. -/
def matrixSix (g : Matrix.symplecticGroup (Fin 3) R) : Matrix (Fin 6) (Fin 6) R :=
  (g : Matrix SplitIndex SplitIndex R).submatrix splitIndex.symm splitIndex.symm

/-- The native standard form in six-coordinate order; its sign is opposite to `omega`. -/
def standardForm : Matrix (Fin 6) (Fin 6) R :=
  (Matrix.J (Fin 3) R).submatrix splitIndex.symm splitIndex.symm

theorem matrixSix_isUnit (g : Matrix.symplecticGroup (Fin 3) R) : IsUnit (matrixSix R g) := by
  have hg : IsUnit (g : Matrix SplitIndex SplitIndex R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (SymplecticGroup.symplectic_det g.property)
  exact hg.map (Matrix.reindexAlgEquiv R R splitIndex).toMonoidHom

theorem matrixSix_preserves_standardForm (g : Matrix.symplecticGroup (Fin 3) R) :
    (matrixSix R g)ᵀ * standardForm R * matrixSix R g=standardForm R := by
  unfold matrixSix standardForm
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  exact congrArg (fun A : Matrix SplitIndex SplitIndex R =>
    A.submatrix splitIndex.symm splitIndex.symm) (SymplecticGroup.mem_iff'.mp g.property)

theorem standardForm_bilin (v w : Fin 6 → R) :
    (standardForm R).toBilin' v w = -M9Native.LagrangianRing.omega R v w := by
  calc
    _ = ∑ i : SplitIndex, ∑ j : SplitIndex,
        v (splitIndex i) * Matrix.J (Fin 3) R i j * w (splitIndex j) := by
      rw [Matrix.toBilin'_apply]
      symm
      refine Fintype.sum_equiv splitIndex _ _ fun i => ?_
      refine Fintype.sum_equiv splitIndex _ _ fun j => ?_
      simp [standardForm]
    _ = _ := by
      simp [Fintype.sum_sum_type,Matrix.J,Matrix.fromBlocks,Matrix.one_apply,splitIndex,finSumFinEquiv,
        M9Native.LagrangianRing.omegaValue,M9Native.LagrangianRing.eIndex,
        M9Native.LagrangianRing.fIndex,Fin.sum_univ_succ]
      ring

theorem matrixSix_preserves_omega (g : Matrix.symplecticGroup (Fin 3) R)
    (v w : Fin 6 → R) :
    M9Native.LagrangianRing.omega R ((matrixSix R g).mulVec v) ((matrixSix R g).mulVec w)=
      M9Native.LagrangianRing.omega R v w := by
  apply neg_injective
  rw [← standardForm_bilin,← standardForm_bilin]
  have h := LinearMap.BilinForm.congr_fun
    (Matrix.toBilin'_comp (standardForm R) (matrixSix R g) (matrixSix R g)) v w
  rw [LinearMap.BilinForm.comp_apply,Matrix.toLin'_apply,Matrix.toLin'_apply,
    matrixSix_preserves_standardForm] at h
  exact h

/-- The actual six-dimensional linear symplectic automorphism. -/
def symplecticEquiv (g : Matrix.symplecticGroup (Fin 3) R) :
    (Fin 6 → R) ≃ₗ[R] (Fin 6 → R) :=
  LinearEquiv.ofBijective (Matrix.mulVecLin (matrixSix R g))
    (by
      change Function.Bijective (matrixSix R g).mulVec
      exact ⟨Matrix.mulVec_injective_of_isUnit (matrixSix_isUnit R g),
        Matrix.mulVec_surjective_iff_isUnit.mpr (matrixSix_isUnit R g)⟩)

@[simp] theorem symplecticEquiv_apply (g : Matrix.symplecticGroup (Fin 3) R) (v : Fin 6 → R) :
    symplecticEquiv R g v=(matrixSix R g).mulVec v := rfl

theorem symplecticEquiv_preserves_omega (g : Matrix.symplecticGroup (Fin 3) R)
    (v w : Fin 6 → R) :
    M9Native.LagrangianRing.omega R (symplecticEquiv R g v) (symplecticEquiv R g w)=
      M9Native.LagrangianRing.omega R v w := matrixSix_preserves_omega R g v w

theorem quotient_matrixSix (M : Matrix (Fin 3) (Fin 6) R)
    (g : Matrix.symplecticGroup (Fin 3) R)
    (hg : splitMatrix R M * (g : Matrix SplitIndex SplitIndex R)=Matrix.fromCols 1 0) :
    M * matrixSix R g=standardQuotient R := by
  have h := congrArg (fun A : Matrix (Fin 3) SplitIndex R =>
    A.submatrix id splitIndex.symm) hg
  have hM : (splitMatrix R M).submatrix id splitIndex.symm=M := by
    ext i j
    simp [splitMatrix]
  rw [← Matrix.submatrix_mul_equiv _ _ id splitIndex.symm splitIndex.symm,hM] at h
  exact h

/-- Actual surjective row-isotropic matrices have a constructed native symplectic normal form. -/
theorem exists_matrix_normalForm (M : Matrix (Fin 3) (Fin 6) R)
    (hsurj : Function.Surjective M.mulVec)
    (hiso : ∀ i j, M9Native.LagrangianRing.omega R (M i) (M j)=0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) R, M * matrixSix R g=standardQuotient R := by
  obtain ⟨g,hg⟩ := M9Native.LagrangianSymplecticMatrix.exists_symplectic_normalForm
    (splitMatrix R M) (splitMatrix_surjective R M hsurj) (splitMatrix_isotropic R M hiso)
  exact ⟨g,quotient_matrixSix R M g hg⟩

/-- Actual annihilation of the native quotient bivector gives the symplectic normal form. -/
theorem exists_matrix_normalForm_of_quotientSigma_zero (M : Matrix (Fin 3) (Fin 6) R)
    (hsurj : Function.Surjective M.mulVec) (hiso : M9Native.LagrangianRing.quotientSigma R M=0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) R, M * matrixSix R g=standardQuotient R :=
  exists_matrix_normalForm R M hsurj (M9Native.LagrangianRing.rows_isotropic_of_quotientSigma_zero R M hiso)

/-- The actual standard bivector, over an arbitrary commutative ring. -/
def standardBivector : ⋀[R]^2 (Fin 6 → R) :=
  ∑ i : Fin 3, exteriorPower.ιMulti R 2
    ![M9Native.LagrangianRing.e R i,M9Native.LagrangianRing.f R i]

theorem quotientSigma_eq_map (M : Matrix (Fin 3) (Fin 6) R) :
    M9Native.LagrangianRing.quotientSigma R M =
      exteriorPower.map 2 (Matrix.mulVecLin M) (standardBivector R) := by
  simp only [standardBivector,map_sum,exteriorPower.map_apply_ιMulti,
    M9Native.LagrangianRing.quotientSigma]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (exteriorPower.ιMulti R 2)
  funext j
  fin_cases j <;>
    simp [M9Native.LagrangianRing.e,M9Native.LagrangianRing.f,
      M9Native.LagrangianRing.basisVector,M9Native.LagrangianRing.eIndex,
      M9Native.LagrangianRing.fIndex] <;> rfl

theorem mulVecLin_toMatrix (q : (Fin 6 → R) →ₗ[R] (Fin 3 → R)) :
    Matrix.mulVecLin (LinearMap.toMatrix' q)=q := by
  rw [← Matrix.toLin'_apply',Matrix.toLin'_toMatrix']

/-- Normal form of a genuine linear quotient annihilating the actual bivector. -/
theorem exists_linear_normalForm (q : (Fin 6 → R) →ₗ[R] (Fin 3 → R))
    (hq : Function.Surjective q) (hσ : exteriorPower.map 2 q (standardBivector R)=0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) R,
      ∀ v : Fin 6 → R, q (symplecticEquiv R g v)=(standardQuotient R).mulVec v := by
  let M := LinearMap.toMatrix' q
  have hM : Matrix.mulVecLin M=q := mulVecLin_toMatrix R q
  have hs : Function.Surjective M.mulVec := by
    change Function.Surjective (Matrix.mulVecLin M)
    rw [hM]
    exact hq
  have hi : M9Native.LagrangianRing.quotientSigma R M=0 := by
    rw [quotientSigma_eq_map,hM]
    exact hσ
  obtain ⟨g,hg⟩ := exists_matrix_normalForm_of_quotientSigma_zero R M hs hi
  refine ⟨g,fun v => ?_⟩
  rw [symplecticEquiv_apply,← hM]
  change M.mulVec ((matrixSix R g).mulVec v)=_
  rw [Matrix.mulVec_mulVec,hg]

section ChangeCoefficients

variable {S : Type u} [CommRing S]

/-- Actual change of coefficients of the native symplectic matrix. -/
def mapSymplectic (ρ : R →+* S) (g : Matrix.symplecticGroup (Fin 3) R) :
    Matrix.symplecticGroup (Fin 3) S := ⟨(g : Matrix SplitIndex SplitIndex R).map ρ,
      SymplecticGroup.map_mem g.property ρ⟩

theorem matrixSix_map (ρ : R →+* S) (g : Matrix.symplecticGroup (Fin 3) R) :
    matrixSix S (mapSymplectic R ρ g)=(matrixSix R g).map ρ := rfl

theorem standardQuotient_map (ρ : R →+* S) :
    (standardQuotient R).map ρ=standardQuotient S := by
  ext i j
  obtain ⟨j,rfl⟩ := splitIndex.surjective j
  cases j with
  | inl j =>
    change ρ (standardQuotient R i (j.castAdd 3))=standardQuotient S i (j.castAdd 3)
    simp only [standardQuotient_first]
    split_ifs <;> simp
  | inr j =>
    change ρ (standardQuotient R i (Fin.natAdd 3 j))=standardQuotient S i (Fin.natAdd 3 j)
    rw [standardQuotient_last,standardQuotient_last,map_zero]

end ChangeCoefficients

section Field

variable (K : Type u) [Field K]

theorem standardBivector_eq_native : standardBivector K=M9Native.LagrangianField.sigma K := rfl

/-- The fixed-target result uses literally the native field bivector. -/
theorem exists_linear_normalForm_native (q : (Fin 6 → K) →ₗ[K] (Fin 3 → K))
    (hq : Function.Surjective q)
    (hσ : exteriorPower.map 2 q (M9Native.LagrangianField.sigma K)=0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K,
      ∀ v : Fin 6 → K, q (symplecticEquiv K g v)=(standardQuotient K).mulVec v :=
  exists_linear_normalForm K q hq hσ

/-- A genuine rank-three target is also transported by an actual linear isomorphism. -/
theorem exists_target_and_symplectic_normalForm {Q : Type u} [AddCommGroup Q] [Module K Q]
    [Module.Finite K Q] (hQ : Module.finrank K Q=3)
    (q : (Fin 6 → K) →ₗ[K] Q) (hq : Function.Surjective q)
    (hσ : exteriorPower.map 2 q (M9Native.LagrangianField.sigma K)=0) :
    ∃ (e : Q ≃ₗ[K] (Fin 3 → K)) (g : Matrix.symplecticGroup (Fin 3) K),
      ∀ v : Fin 6 → K, e (q (symplecticEquiv K g v))=(standardQuotient K).mulVec v := by
  let e : Q ≃ₗ[K] (Fin 3 → K) := (Module.finBasisOfFinrankEq K Q hQ).equivFun
  have heq : Function.Surjective (e.toLinearMap.comp q) := e.surjective.comp hq
  have hσ' : exteriorPower.map 2 (e.toLinearMap.comp q) (M9Native.LagrangianField.sigma K)=0 := by
    rw [exteriorPower.map_comp,LinearMap.comp_apply,hσ,map_zero]
  obtain ⟨g,hg⟩ := exists_linear_normalForm_native K (e.toLinearMap.comp q) heq hσ'
  exact ⟨e,g,hg⟩

end Field

section NativePoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9Native.LagrangianMatrixChart M9Native.LagrangianGrassmannian
open AlgebraicGeometry.Grassmannian

/-- A normalized pivot minor supplies an actual right inverse, over any ring. -/
theorem matrix_surjective_of_pivots (M : Matrix (Fin 3) (Fin 6) R)
    (ι : Fin 3 ↪ Fin 6) (hι : M.submatrix id ι=1) : Function.Surjective M.mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨(1 : Matrix (Fin 6) (Fin 6) R).submatrix id ι,?_⟩
  exact (Matrix.mul_submatrix_one (Equiv.refl (Fin 6)) ι M).trans hι

/-- The literal symplectic matrix gives an actual automorphism of the free sheaf. -/
def freeSymplecticIso (X : Scheme.{u}) (g : Matrix.symplecticGroup (Fin 3) Γ(X,⊤)) :
    freeOn X 6 ≅ freeOn X 6 := by
  let a := Stacks.FreeSheafMatrix.ofMatrix (matrixSix Γ(X,⊤) g)
  have ha : IsIso a := (Stacks.FreeSheafMatrix.isIso_iff_isUnit_det a).mpr (by
    rw [Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (matrixSix_isUnit Γ(X,⊤) g))
  exact asIso a

@[simp] theorem freeSymplecticIso_matrix (X : Scheme.{u})
    (g : Matrix.symplecticGroup (Fin 3) Γ(X,⊤)) :
    Stacks.FreeSheafMatrix.toMatrix (freeSymplecticIso X g).hom=matrixSix Γ(X,⊤) g :=
  Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

variable (K L : Type u) [Field K] [Field L]

/-- Every actual field-valued LG point admits a true normalized quotient presentation.
The target isomorphism comes from the native representability classifier. -/
theorem exists_native_chart_presentation (p : Spec (.of L) ⟶ space K) :
    ∃ (ι : Fin 3 ↪ Fin 6)
      (h : Spec (.of L) ⟶ Spec (.of
        (MvPolynomial (ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))))
      (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of L)) 3),
      (p ≫ inclusion K) ≫ pullback.snd _ _=h ≫ chart 3 6 ι ∧
      (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom=
        chartQuotientMap 3 6 ι h := by
  let f := p ≫ inclusion K
  let a₀ := IsLocalRing.closedPoint L
  obtain ⟨ι,y,hy⟩ := GrassmannianCharts.charts_cover K 3 6 (f a₀)
  have hrange : Set.range f ⊆ Set.range (GrassmannianCharts.chartOver K 3 6 ι) := by
    rintro _ ⟨a,rfl⟩
    have ha : a=a₀ := Subsingleton.elim _ _
    subst a
    exact ⟨y,hy⟩
  let g := IsOpenImmersion.lift (GrassmannianCharts.chartOver K 3 6 ι) f hrange
  have hg : g ≫ GrassmannianCharts.chartOver K 3 6 ι=f :=
    IsOpenImmersion.lift_fac _ _ hrange
  let h := g ≫ AffineSpace.toSpecMvPoly (ChartIndex.{u} (k:=3) (n:=6) ι) (Spec (.of K))
  have hh : f ≫ pullback.snd _ _=h ≫ chart 3 6 ι := by
    calc
      _ = g ≫ (GrassmannianCharts.chartOver K 3 6 ι ≫
          GrassmannianCharts.toIntegral K 3 6) := by rw [← Category.assoc,hg]
      _ = _ := by rw [GrassmannianCharts.chartOver_toIntegral]; rfl
  obtain ⟨e,he⟩ := pullbackUniversal_chart_isomorphic K f ι h hh
  exact ⟨ι,h,e,hh,he⟩

/-- The actual quotient bundle of every field-valued LG point has a constructed
symplectic normal form. Both arrows are genuine isomorphisms of native sheaves. -/
theorem exists_pullbackUniversal_normalForm (p : Spec (.of L) ⟶ space K) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) Γ(Spec (.of L),⊤))
      (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of L)) 3),
      (freeSymplecticIso (Spec (.of L)) g).hom ≫
          (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom=
        Stacks.FreeSheafMatrix.ofMatrix (standardQuotient Γ(Spec (.of L),⊤)) := by
  obtain ⟨ι,h,e,hh,he⟩ := exists_native_chart_presentation K L p
  let q := chartQuotientMap 3 6 ι h
  let M := Stacks.FreeSheafMatrix.toMatrix q
  have hpiv : M.submatrix id ι=1 := by
    change (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 3 6 ι h)).submatrix id ι=1
    rw [toMatrix_chartQuotientMap]
    ext i j
    simpa only [Matrix.submatrix_apply,id_eq,Matrix.one_apply] using
      (chartMatrix_apply_self (k:=3) (n:=6) (R:=Γ(Spec (.of L),⊤)) ι
        (AffineSpace.toSpecMvPolyIntEquiv _ h) i j)
  have hsurj : Function.Surjective M.mulVec := matrix_surjective_of_pivots Γ(Spec (.of L),⊤) M ι hpiv
  have hσ := (factorsThrough_iff_pullbackQuotient_annihilates K (p ≫ inclusion K)).mp ⟨p,rfl⟩
  have hq : AnnihilatesSigma (Spec (.of L)) q :=
    (annihilatesSigma_iff_of_iso (Spec (.of L)) _ _ e he).mp hσ
  obtain ⟨g,hg⟩ := exists_matrix_normalForm Γ(Spec (.of L),⊤) M hsurj
    (M9Native.LagrangianPlucker.rows_isotropic_of_annihilatesSigma (Spec (.of L)) q hq)
  refine ⟨g,e,?_⟩
  rw [he]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,freeSymplecticIso_matrix,
    Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
  exact hg

/-- Evaluating the actual quotient's coefficients on `Spec L` yields a genuine
symplectic normal form over the field `L` itself. -/
theorem exists_pullbackUniversal_field_normalForm (p : Spec (.of L) ⟶ space K) :
    ∃ (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of L)) 3)
      (g : Matrix.symplecticGroup (Fin 3) L),
      (Stacks.FreeSheafMatrix.toMatrix
        ((pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom)).map
          (Scheme.ΓSpecIso (.of L)).hom.hom * matrixSix L g=standardQuotient L := by
  obtain ⟨g,e,he⟩ := exists_pullbackUniversal_normalForm K L p
  let ρ := (Scheme.ΓSpecIso (.of L)).hom.hom
  have hM : Stacks.FreeSheafMatrix.toMatrix
      ((pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom) *
        matrixSix Γ(Spec (.of L),⊤) g=standardQuotient Γ(Spec (.of L),⊤) := by
    have h := congrArg Stacks.FreeSheafMatrix.toMatrix he
    rw [Stacks.FreeSheafMatrix.toMatrix_comp,freeSymplecticIso_matrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix] at h
    exact h
  refine ⟨e,mapSymplectic Γ(Spec (.of L),⊤) ρ g,?_⟩
  rw [matrixSix_map,← Matrix.map_mul,hM,standardQuotient_map]

end NativePoints

end M9Native.LagrangianTransitivity

end
