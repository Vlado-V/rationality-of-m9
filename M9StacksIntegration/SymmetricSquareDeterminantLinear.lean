module

public import M9StacksIntegration.LagrangianSymmetricSquareEquivariance
public import M9StacksIntegration.LagrangianSymmetricDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerTopBasis

/-! The actual symmetric-square determinant character and its top line. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.SymmetricSquareDeterminantLinear

open LagrangianSymmetricSquare LagrangianSymmetricCongruence

variable (R : Type*) [CommRing R]

/-- The determinant of the actual native Sym² map, derived by the
proved normalization and the actual symmetric-matrix determinant. -/
theorem det_symMap [Invertible (2 : R)] (P : Matrix (Fin 3) (Fin 3) R) :
    LinearMap.det (SymPow.symMap 2 P.mulVecLin) = P.det ^ 4 := by
  let e := (squareEquivMatrices R).trans (coordinates R)
  have hconj : e.toLinearMap.comp
      ((SymPow.symMap 2 P.mulVecLin).comp e.symm.toLinearMap) =
      (representation R P).mulVecLin := by
    apply LinearMap.ext
    intro v
    change coordinates R (squareEquivMatrices R
      (SymPow.symMap 2 P.mulVecLin (e.symm v))) = representation R P *ᵥ v
    rw [squareEquivMatrices_symMap, coordinates_congruence]
    exact congrArg (fun w => representation R P *ᵥ w) (e.apply_symm_apply v)
  have hdet := LinearMap.det_conj (SymPow.symMap 2 P.mulVecLin) e
  rw [hconj] at hdet
  exact hdet.symm.trans ((LinearMap.det_toLin' (representation R P)).trans
    (det_representation R P))

/-- Its action on the actual ordered top wedge has the fourth-power
character, with the literal six monomials as its basis. -/
theorem topSquare_map [Invertible (2 : R)] (P : Matrix (Fin 3) (Fin 3) R) :
    exteriorPower.map 6 (SymPow.symMap 2 P.mulVecLin)
      (exteriorPower.ιMulti R 6 (monomialBasis R)) =
      P.det ^ 4 • exteriorPower.ιMulti R 6 (monomialBasis R) := by
  rw [Stacks.ExteriorPower.map_ιMulti_eq_det_smul, LinearMap.det_toMatrix, det_symMap]

/-- The actual determinant line of the standard rank-three module. -/
abbrev DetLine := ⋀[R]^3 (Fin 3 → R)

/-- The actual determinant basis is the literal wedge of the original
three standard coordinate vectors. -/
def detBasis : Basis (Fin 1) R (DetLine R) :=
  Stacks.ExteriorPower.topBasis (Pi.basisFun R (Fin 3))

/-- The original determinant line transforms by the actual determinant. -/
theorem detBasis_map (P : Matrix (Fin 3) (Fin 3) R) :
    exteriorPower.map 3 P.mulVecLin (detBasis R 0) = P.det • detBasis R 0 := by
  rw [detBasis, Stacks.ExteriorPower.topBasis_apply,
    Stacks.ExteriorPower.map_ιMulti_eq_det_smul, LinearMap.det_toMatrix]
  exact congrArg (fun r : R => r • exteriorPower.ιMulti R 3 (Pi.basisFun R (Fin 3)))
    (LinearMap.det_toLin' P)

section RankOnePowers

def powerIndex (n : ℕ) : {d : Fin 1 →₀ ℕ // d.degree = n} :=
  ⟨Finsupp.single 0 n, by rw [Finsupp.degree_single]⟩

theorem powerIndex_unique (n : ℕ) (d : {d : Fin 1 →₀ ℕ // d.degree = n}) :
    d = powerIndex n := by
  have hd := d.property
  simp only [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hd
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa [powerIndex] using hd

def powerIndexEquiv (n : ℕ) : Fin 1 ≃ {d : Fin 1 →₀ ℕ // d.degree = n} where
  toFun _ := powerIndex n
  invFun _ := 0
  left_inv i := by fin_cases i; rfl
  right_inv d := (powerIndex_unique n d).symm

variable {L : Type*} [AddCommGroup L] [Module R L]

/-- The literal nth power of the sole line-basis vector is again a
genuine basis, without any division or polarization. -/
def powerBasis (n : ℕ) (b : Basis (Fin 1) R L) :
    Basis (Fin 1) R (SymPow.symmetricPower n R L) :=
  (SymPow.basisSymmetricPower b n).reindex (powerIndexEquiv n).symm

theorem powerBasis_coe (n : ℕ) (b : Basis (Fin 1) R L) :
    (powerBasis R n b 0 : SymmetricAlgebra R L) = SymmetricAlgebra.ι R L (b 0) ^ n := by
  simp only [powerBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change (SymPow.basisSymmetricPower b n (powerIndex n) : SymmetricAlgebra R L) = _
  rw [SymPow.coe_basisSymmetricPower_apply_eq_prod_univ]
  simp [powerIndex, Fin.prod_univ_succ]

end RankOnePowers

def standardIso : (⋀[R]^6 (Square R)) ≃ₗ[R] SymPow.symmetricPower 4 R (DetLine R) :=
  (Stacks.ExteriorPower.topBasis (monomialBasis R)).equiv
    (powerBasis R 4 (detBasis R)) (Equiv.refl _)

@[simp] theorem standardIso_generator :
    standardIso R (Stacks.ExteriorPower.topBasis (monomialBasis R) 0) =
      powerBasis R 4 (detBasis R) 0 :=
  Module.Basis.equiv_apply _ _ _ _

theorem fourthDetBasis_map (P : Matrix (Fin 3) (Fin 3) R) :
    SymPow.symMap 4 (exteriorPower.map 3 P.mulVecLin) (powerBasis R 4 (detBasis R) 0) =
      P.det ^ 4 • powerBasis R 4 (detBasis R) 0 := by
  apply Subtype.ext
  change SymPow.symAlgMap (exteriorPower.map 3 P.mulVecLin)
      (powerBasis R 4 (detBasis R) 0 : SymmetricAlgebra R (DetLine R)) =
      P.det ^ 4 • (powerBasis R 4 (detBasis R) 0 : SymmetricAlgebra R (DetLine R))
  rw [powerBasis_coe, map_pow, SymPow.symAlgMap_ι, detBasis_map, map_smul]
  exact smul_pow _ _ _

/-- The actual standard top-line isomorphism is equivariant for every
coefficient matrix, derived from its genuine determinant character. -/
theorem standardIso_naturality [Invertible (2 : R)]
    (P : Matrix (Fin 3) (Fin 3) R) (w : ⋀[R]^6 (Square R)) :
    standardIso R (exteriorPower.map 6 (SymPow.symMap 2 P.mulVecLin) w) =
      SymPow.symMap 4 (exteriorPower.map 3 P.mulVecLin) (standardIso R w) := by
  have h : (standardIso R).toLinearMap.comp (exteriorPower.map 6 (SymPow.symMap 2 P.mulVecLin)) =
      (SymPow.symMap 4 (exteriorPower.map 3 P.mulVecLin)).comp (standardIso R).toLinearMap := by
    apply (Stacks.ExteriorPower.topBasis (monomialBasis R)).ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hs : exteriorPower.map 6 (SymPow.symMap 2 P.mulVecLin)
        (Stacks.ExteriorPower.topBasis (monomialBasis R) 0) =
        P.det ^ 4 • Stacks.ExteriorPower.topBasis (monomialBasis R) 0 := by
      simpa only [Stacks.ExteriorPower.topBasis_apply] using topSquare_map R P
    change standardIso R
      (exteriorPower.map 6 (SymPow.symMap 2 P.mulVecLin)
        (Stacks.ExteriorPower.topBasis (monomialBasis R) 0)) =
      SymPow.symMap 4 (exteriorPower.map 3 P.mulVecLin)
        (standardIso R (Stacks.ExteriorPower.topBasis (monomialBasis R) 0))
    rw [hs, map_smul, standardIso_generator, fourthDetBasis_map]
  exact DFunLike.congr_fun h w

section GeneralModules

variable {M N T : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T]

abbrev Source (M : Type*) [AddCommGroup M] [Module R M] :=
  ⋀[R]^6 (SymPow.symmetricPower 2 R M)

abbrev Target (M : Type*) [AddCommGroup M] [Module R M] :=
  SymPow.symmetricPower 4 R (⋀[R]^3 M)

def sourceMap (f : M →ₗ[R] N) : Source R M →ₗ[R] Source R N :=
  exteriorPower.map 6 (SymPow.symMap 2 f)

def targetMap (f : M →ₗ[R] N) : Target R M →ₗ[R] Target R N :=
  SymPow.symMap 4 (exteriorPower.map 3 f)

theorem sourceMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] T) :
    sourceMap R (g.comp f) = (sourceMap R g).comp (sourceMap R f) := by
  simp only [sourceMap, SymPow.symMap_comp, exteriorPower.map_comp]

theorem targetMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] T) :
    targetMap R (g.comp f) = (targetMap R g).comp (targetMap R f) := by
  simp only [targetMap, exteriorPower.map_comp, SymPow.symMap_comp]

@[simp] theorem sourceMap_id : sourceMap R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  simp only [sourceMap, SymPow.symMap_id, exteriorPower.map_id]

@[simp] theorem targetMap_id : targetMap R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  simp only [targetMap, exteriorPower.map_id, SymPow.symMap_id]

def sourceCongr (e : M ≃ₗ[R] N) : Source R M ≃ₗ[R] Source R N :=
  LinearEquiv.ofLinearMap (sourceMap R e.toLinearMap) (sourceMap R e.symm.toLinearMap)
    (by rw [← sourceMap_comp]; simp only [LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, sourceMap_id])
    (by rw [← sourceMap_comp]; simp only [LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, sourceMap_id])

def targetCongr (e : M ≃ₗ[R] N) : Target R M ≃ₗ[R] Target R N :=
  LinearEquiv.ofLinearMap (targetMap R e.toLinearMap) (targetMap R e.symm.toLinearMap)
    (by rw [← targetMap_comp]; simp only [LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, targetMap_id])
    (by rw [← targetMap_comp]; simp only [LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, targetMap_id])

@[simp] theorem sourceCongr_apply (e : M ≃ₗ[R] N) (x : Source R M) :
    sourceCongr R e x = sourceMap R e.toLinearMap x := rfl

@[simp] theorem targetCongr_apply (e : M ≃ₗ[R] N) (x : Target R M) :
    targetCongr R e x = targetMap R e.toLinearMap x := rfl

@[simp] theorem sourceCongr_symm (e : M ≃ₗ[R] N) :
    (sourceCongr R e).symm = sourceCongr R e.symm := by ext; rfl

@[simp] theorem targetCongr_symm (e : M ≃ₗ[R] N) :
    (targetCongr R e).symm = targetCongr R e.symm := by ext; rfl

theorem sourceCongr_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] T) (x : Source R M) :
    sourceCongr R (e.trans f) x = sourceCongr R f (sourceCongr R e x) := by
  change sourceMap R (f.toLinearMap.comp e.toLinearMap) x = _
  rw [sourceMap_comp]
  rfl

theorem targetCongr_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] T) (x : Target R M) :
    targetCongr R (e.trans f) x = targetCongr R f (targetCongr R e x) := by
  change targetMap R (f.toLinearMap.comp e.toLinearMap) x = _
  rw [targetMap_comp]
  rfl

/-- The actual top-line isomorphism defined from an actual rank-three
basis. Its independence is proved below from the actual determinant. -/
def basisIso (b : Basis (Fin 3) R M) : Source R M ≃ₗ[R] Target R M :=
  (sourceCongr R b.equivFun).trans ((standardIso R).trans (targetCongr R b.equivFun).symm)

theorem standardIso_equivariance [Invertible (2 : R)]
    (e : (Fin 3 → R) ≃ₗ[R] (Fin 3 → R)) (x : Source R (Fin 3 → R)) :
    standardIso R (sourceCongr R e x) = targetCongr R e (standardIso R x) := by
  have h : (LinearMap.toMatrix' e.toLinearMap).mulVecLin = e.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  simpa only [sourceCongr_apply, sourceMap, targetCongr_apply, targetMap, h] using
    standardIso_naturality R (LinearMap.toMatrix' e.toLinearMap) x

/-- Independence of the chosen actual basis follows from the checked
Sym² determinant character; no change-of-frame compatibility is assumed. -/
theorem basisIso_independent [Invertible (2 : R)]
    (b c : Basis (Fin 3) R M) : basisIso R b = basisIso R c := by
  apply LinearEquiv.ext
  intro x
  apply (targetCongr R c.equivFun).injective
  let e := b.equivFun.symm.trans c.equivFun
  have he : b.equivFun.trans e = c.equivFun := by
    ext v
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  have hs : sourceCongr R e (sourceCongr R b.equivFun x) = sourceCongr R c.equivFun x := by
    rw [← sourceCongr_trans, he]
  change targetCongr R c.equivFun
      ((targetCongr R b.equivFun).symm (standardIso R (sourceCongr R b.equivFun x))) =
    targetCongr R c.equivFun
      ((targetCongr R c.equivFun).symm (standardIso R (sourceCongr R c.equivFun x)))
  rw [LinearEquiv.apply_symm_apply, targetCongr_symm, ← targetCongr_trans]
  change targetCongr R e (standardIso R (sourceCongr R b.equivFun x)) = _
  rw [← standardIso_equivariance, hs]

end GeneralModules

end M9Native.SymmetricSquareDeterminantLinear
