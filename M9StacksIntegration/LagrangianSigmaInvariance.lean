module

public import M9StacksIntegration.LagrangianTransitivity

/-!
# Preservation of the actual standard bivector

The native symplectic matrices preserve the actual exterior bivector over
every commutative ring. The canonical finite-free section comparison then
gives preservation of the literal native sheaf section `sigmaSection`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open Matrix Module exteriorPower
open scoped BigOperators

universe u

namespace M9Native.LagrangianSigmaInvariance

open M9Native.LagrangianTransitivity

variable (R : Type u) [CommRing R]

theorem matrixSix_det_eq_one (g : Matrix.symplecticGroup (Fin 3) R) :
    (matrixSix R g).det=1 := by
  rw [matrixSix,Matrix.det_submatrix_equiv_self]
  exact SymplecticGroup.det_eq_one g.property

def bivectorCoordinate (i j : Fin 6) : (⋀[R]^2 (Fin 6 → R)) →ₗ[R] R :=
  exteriorPower.pairingDual R (Fin 6 → R) 2
    (exteriorPower.ιMulti R 2 ![LinearMap.proj i,LinearMap.proj j])

@[simp] theorem bivectorCoordinate_wedge (i j : Fin 6) (v w : Fin 6 → R) :
    bivectorCoordinate R i j (exteriorPower.ιMulti R 2 ![v,w])=v i*w j-v j*w i := by
  simp [bivectorCoordinate,Matrix.det_fin_two]

theorem multiDual_eq_coordinate (s : Set.powersetCard (Fin 6) 2) :
    exteriorPower.ιMultiDual R 2 (Pi.basisFun R (Fin 6)) s =
      bivectorCoordinate R (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.ιMultiDual R 2 (Pi.basisFun R (Fin 6)) s
    (exteriorPower.ιMulti R 2 v)=
      bivectorCoordinate R (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1) (exteriorPower.ιMulti R 2 v)
  have hv : v=![v 0,v 1] := by funext i; fin_cases i <;> rfl
  rw [hv,exteriorPower.ιMultiDual_apply_ιMulti,bivectorCoordinate_wedge]
  simp [Matrix.det_fin_two,Basis.coord_apply,Pi.basisFun_repr]

theorem bivectorCoordinate_ext (x y : ⋀[R]^2 (Fin 6 → R))
    (h : ∀ i j,bivectorCoordinate R i j x=bivectorCoordinate R i j y) : x=y := by
  apply ((Pi.basisFun R (Fin 6)).exteriorPower 2).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply,exteriorPower.basis_repr_apply,
    multiDual_eq_coordinate]
  exact h _ _

theorem coordinate_map_standardBivector (M : Matrix (Fin 6) (Fin 6) R) (i j : Fin 6) :
    bivectorCoordinate R i j (exteriorPower.map 2 M.mulVecLin (standardBivector R))=
      M9Native.LagrangianRing.omega R (M i) (M j) := by
  simp [standardBivector,bivectorCoordinate,exteriorPower.map_apply_ιMulti,Matrix.det_fin_two,
    M9Native.LagrangianRing.e,M9Native.LagrangianRing.f,
    M9Native.LagrangianRing.basisVector,M9Native.LagrangianRing.omegaValue,
    M9Native.LagrangianRing.eIndex,M9Native.LagrangianRing.fIndex,
    Matrix.col_apply,Fin.sum_univ_succ]
  ring

theorem coordinate_standardBivector (i j : Fin 6) :
    bivectorCoordinate R i j (standardBivector R)=
      M9Native.LagrangianRing.omega R (M9Native.LagrangianRing.basisVector R i)
        (M9Native.LagrangianRing.basisVector R j) := by
  have hrow (i : Fin 6) : (1 : Matrix (Fin 6) (Fin 6) R) i=
      M9Native.LagrangianRing.basisVector R i := by
    funext k
    simp [Matrix.one_apply,M9Native.LagrangianRing.basisVector,Pi.single_apply,eq_comm]
  simpa only [Matrix.mulVecLin_one,exteriorPower.map_id,LinearMap.id_apply,hrow] using
    coordinate_map_standardBivector R (1 : Matrix (Fin 6) (Fin 6) R) i j

def transposeSymplectic (g : Matrix.symplecticGroup (Fin 3) R) :
    Matrix.symplecticGroup (Fin 3) R :=
  ⟨(g : Matrix SplitIndex SplitIndex R)ᵀ,SymplecticGroup.transpose_mem_iff.mpr g.property⟩

theorem matrixSix_transpose (g : Matrix.symplecticGroup (Fin 3) R) :
    matrixSix R (transposeSymplectic R g)=(matrixSix R g)ᵀ := rfl

theorem rows_omega_matrixSix (g : Matrix.symplecticGroup (Fin 3) R) (i j : Fin 6) :
    M9Native.LagrangianRing.omega R (matrixSix R g i) (matrixSix R g j)=
      M9Native.LagrangianRing.omega R (M9Native.LagrangianRing.basisVector R i)
        (M9Native.LagrangianRing.basisVector R j) := by
  have h := matrixSix_preserves_omega R (transposeSymplectic R g)
    (M9Native.LagrangianRing.basisVector R i) (M9Native.LagrangianRing.basisVector R j)
  have hcol (k : Fin 6) : ((matrixSix R g)ᵀ).col k=matrixSix R g k := rfl
  simpa only [matrixSix_transpose,M9Native.LagrangianRing.basisVector,
    Matrix.mulVec_single_one,hcol] using h

/-- The actual exterior-square map of the symplectic matrix fixes the literal bivector. -/
theorem map_standardBivector (g : Matrix.symplecticGroup (Fin 3) R) :
    exteriorPower.map 2 (matrixSix R g).mulVecLin (standardBivector R)=standardBivector R := by
  apply bivectorCoordinate_ext R
  intro i j
  rw [coordinate_map_standardBivector,coordinate_standardBivector]
  exact rows_omega_matrixSix R g i j

/-- The actual linear symplectic equivalence fixes the literal native field bivector. -/
theorem symplecticEquiv_preserves_sigma (K : Type u) [Field K]
    (g : Matrix.symplecticGroup (Fin 3) K) :
    exteriorPower.map 2 (symplecticEquiv K g).toLinearMap (M9Native.LagrangianField.sigma K)=
      M9Native.LagrangianField.sigma K := by
  change exteriorPower.map 2 (matrixSix K g).mulVecLin (M9Native.LagrangianField.sigma K)=_
  rw [← standardBivector_eq_native,map_standardBivector]

section NativeSheaves

open AlgebraicGeometry CategoryTheory Opposite
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart

theorem wedgeSection_eq_comparison (X : Scheme.{u}) (F : X.Modules) (s t : Γ(F,⊤)) :
    wedgeSection X F s t=M9Native.ExteriorEvaluation.sectionComparison F 2 ⊤
      (exteriorPower.ιMulti Γ(X,⊤) 2 ![s,t]) := by
  rw [M9Native.ExteriorEvaluation.sectionComparison_ιMulti]
  apply congrArg ((Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd
    (op ⊤) 2)
  funext i
  fin_cases i <;> rfl

/-- Canonical coordinates of the actual exterior image of the native section. -/
theorem exteriorPowerMap_sigma_eq (X : Scheme.{u}) {r : ℕ} (q : freeOn X 6 ⟶ freeOn X r) :
    (M9Native.LagrangianGrassmannian.exteriorPowerMap X q 2).app ⊤ (sigmaSection X)=
      freeExteriorSectionsEquiv X 2 r
        (exteriorPower.map 2 (Stacks.FreeSheafMatrix.toMatrix q).mulVecLin
          (standardBivector Γ(X,⊤))) := by
  unfold sigmaSection standardBivector
  simp only [map_sum,exteriorPower.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  rw [M9Native.LagrangianGrassmannian.exteriorPowerMap_wedgeSection,
    wedgeSection_eq_comparison,freeExteriorSectionsEquiv_ιMulti]
  apply congrArg (M9Native.ExteriorEvaluation.sectionComparison (freeOn X r) 2 ⊤)
  apply congrArg (exteriorPower.ιMulti Γ(X,⊤) 2)
  funext j
  fin_cases j
  · apply (freeSectionCoordinates X r).injective
    funext k
    rw [LinearEquiv.apply_symm_apply]
    change freeSectionCoordinates X r (q.app ⊤ (freeVector X (i.castAdd 3))) k=
      ((Stacks.FreeSheafMatrix.toMatrix q).mulVec (Pi.single (i.castAdd 3) 1)) k
    rw [Matrix.mulVec_single_one]
    exact freeCoordinates_map_basis q k _
  · apply (freeSectionCoordinates X r).injective
    funext k
    rw [LinearEquiv.apply_symm_apply]
    change freeSectionCoordinates X r (q.app ⊤ (freeVector X (Fin.natAdd 3 i))) k=
      ((Stacks.FreeSheafMatrix.toMatrix q).mulVec (Pi.single (Fin.natAdd 3 i) 1)) k
    rw [Matrix.mulVec_single_one]
    exact freeCoordinates_map_basis q k _

theorem sigmaSection_eq_comparison (X : Scheme.{u}) :
    sigmaSection X=freeExteriorSectionsEquiv X 2 6 (standardBivector Γ(X,⊤)) := by
  have h := exteriorPowerMap_sigma_eq X (𝟙 (freeOn X 6))
  rw [M9Native.LagrangianGrassmannian.exteriorPowerMap_eq_native,
    Scheme.Modules.exteriorPowerMap_id,Stacks.FreeSheafMatrix.toMatrix_id,
    Matrix.mulVecLin_one,exteriorPower.map_id] at h
  exact h

/-- The actual free-six sheaf automorphism fixes the literal native bivector section. -/
theorem freeSymplecticIso_preserves_sigma (X : Scheme.{u})
    (g : Matrix.symplecticGroup (Fin 3) Γ(X,⊤)) :
    (M9Native.LagrangianGrassmannian.exteriorPowerMap X (freeSymplecticIso X g).hom 2).app ⊤
      (sigmaSection X)=sigmaSection X := by
  rw [exteriorPowerMap_sigma_eq,freeSymplecticIso_matrix,map_standardBivector,
    ← sigmaSection_eq_comparison]

theorem exteriorPowerMap_precomp_sigma (X : Scheme.{u}) {E : X.Modules}
    (q : freeOn X 6 ⟶ E) (g : Matrix.symplecticGroup (Fin 3) Γ(X,⊤)) :
    (M9Native.LagrangianGrassmannian.exteriorPowerMap X ((freeSymplecticIso X g).hom ≫ q) 2).app ⊤
        (sigmaSection X)=
      (M9Native.LagrangianGrassmannian.exteriorPowerMap X q 2).app ⊤ (sigmaSection X) := by
  rw [M9Native.LagrangianGrassmannian.exteriorPowerMap_eq_native,
    Scheme.Modules.exteriorPowerMap_comp]
  change (Scheme.Modules.exteriorPowerMap q 2).app ⊤
      ((Scheme.Modules.exteriorPowerMap (freeSymplecticIso X g).hom 2).app ⊤ (sigmaSection X))=_
  have hσ := freeSymplecticIso_preserves_sigma X g
  change (Scheme.Modules.exteriorPowerMap (freeSymplecticIso X g).hom 2).app ⊤
    (sigmaSection X)=sigmaSection X at hσ
  rw [hσ]
  rfl

/-- The true native LG equation is invariant under precomposition by the constructed symmetry. -/
theorem annihilatesSigma_precomp_iff (X : Scheme.{u}) {E : X.Modules}
    (q : freeOn X 6 ⟶ E) (g : Matrix.symplecticGroup (Fin 3) Γ(X,⊤)) :
    AnnihilatesSigma X ((freeSymplecticIso X g).hom ≫ q) ↔ AnnihilatesSigma X q := by
  unfold AnnihilatesSigma
  rw [exteriorPowerMap_precomp_sigma]

open AlgebraicGeometry.Grassmannian

/-- Actual native field-point normal form with literal sheaf-bivector preservation recorded. -/
theorem exists_pullbackUniversal_sigma_normalForm (K L : Type u) [Field K] [Field L]
    (p : Spec (.of L) ⟶ space K) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) Γ(Spec (.of L),⊤))
      (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of L)) 3),
      (M9Native.LagrangianGrassmannian.exteriorPowerMap (Spec (.of L))
        (freeSymplecticIso (Spec (.of L)) g).hom 2).app ⊤ (sigmaSection (Spec (.of L)))=
          sigmaSection (Spec (.of L)) ∧
      (freeSymplecticIso (Spec (.of L)) g).hom ≫
          (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom=
        Stacks.FreeSheafMatrix.ofMatrix (standardQuotient Γ(Spec (.of L),⊤)) := by
  obtain ⟨g,e,he⟩ := exists_pullbackUniversal_normalForm K L p
  exact ⟨g,e,freeSymplecticIso_preserves_sigma (Spec (.of L)) g,he⟩

end NativeSheaves

end M9Native.LagrangianSigmaInvariance

end
