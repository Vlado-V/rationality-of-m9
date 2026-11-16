module

public import M9StacksIntegration.SymmetricSquareDeterminantLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange

/-! Naturality of the actual symmetric-square top line under restriction. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module

namespace M9Native.SymmetricSquareDeterminantLinear

open LagrangianSymmetricSquare LagrangianSymmetricCongruence

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The six actual ordered quadratic monomials in any given basis. -/
def quadraticBasis (b : Basis (Fin 3) R M) :
    Basis (Fin 6) R (SymPow.symmetricPower 2 R M) :=
  (SymPow.basisSymmetricPower b 2).reindex quadraticIndexEquiv.symm

theorem quadraticBasis_coe (b : Basis (Fin 3) R M) (i : Fin 6) :
    (quadraticBasis R b i : SymmetricAlgebra R M) =
      SymmetricAlgebra.ι R M (b (upperPair i).1) *
        SymmetricAlgebra.ι R M (b (upperPair i).2) := by
  simp only [quadraticBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change (SymPow.basisSymmetricPower b 2 (quadraticIndex i) : SymmetricAlgebra R M) = _
  rw [SymPow.coe_basisSymmetricPower_apply_eq_prod_univ]
  fin_cases i <;>
    simp [quadraticIndex, upperPair, Fin.prod_univ_succ, Finsupp.single_apply, pow_two]

def sourceFrame (b : Basis (Fin 3) R M) : Source R M :=
  exteriorPower.ιMulti R 6 (quadraticBasis R b)

def targetFrame (b : Basis (Fin 3) R M) : Target R M :=
  powerBasis R 4 (Stacks.ExteriorPower.topBasis b) 0

theorem equivFun_basis (b : Basis (Fin 3) R M) (i : Fin 3) :
    b.equivFun (b i) = Pi.single i 1 := by
  funext j
  simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

theorem sourceFrame_equivFun (b : Basis (Fin 3) R M) :
    sourceCongr R b.equivFun (sourceFrame R b) =
      Stacks.ExteriorPower.topBasis (monomialBasis R) 0 := by
  change exteriorPower.map 6 (SymPow.symMap 2 b.equivFun.toLinearMap)
    (exteriorPower.ιMulti R 6 (quadraticBasis R b)) = _
  rw [exteriorPower.map_apply_ιMulti, Stacks.ExteriorPower.topBasis_apply]
  congr 1
  funext i
  apply Subtype.ext
  change (SymPow.symMap 2 b.equivFun.toLinearMap (quadraticBasis R b i) :
    SymmetricAlgebra R (Fin 3 → R)) = _
  rw [SymPow.symMap_coe, quadraticBasis_coe, map_mul,
    SymPow.symAlgMap_ι, SymPow.symAlgMap_ι]
  have hb (j : Fin 3) : b.equivFun.toLinearMap (b j) = Pi.single j 1 := equivFun_basis R b j
  rw [hb, hb]
  exact (monomialBasis_coe R i).symm

theorem targetFrame_equivFun (b : Basis (Fin 3) R M) :
    targetCongr R b.equivFun (targetFrame R b) = powerBasis R 4 (detBasis R) 0 := by
  have hb : exteriorPower.map 3 b.equivFun.toLinearMap
      (Stacks.ExteriorPower.topBasis b 0) = detBasis R 0 := by
    rw [Stacks.ExteriorPower.topBasis_apply, exteriorPower.map_apply_ιMulti,
      detBasis, Stacks.ExteriorPower.topBasis_apply]
    congr 1
    funext i
    simpa only [Function.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply] using
      equivFun_basis R b i
  apply Subtype.ext
  change SymPow.symAlgMap (exteriorPower.map 3 b.equivFun.toLinearMap)
      (powerBasis R 4 (Stacks.ExteriorPower.topBasis b) 0 :
        SymmetricAlgebra R (⋀[R]^3 M)) = _
  rw [powerBasis_coe, map_pow, SymPow.symAlgMap_ι, hb]
  exact (powerBasis_coe R 4 (detBasis R)).symm

/-- The basis-independent top-line map sends the literal monomial
top wedge to the actual fourth power of the determinant wedge. -/
theorem basisIso_generator (b : Basis (Fin 3) R M) :
    basisIso R b (sourceFrame R b) = targetFrame R b := by
  apply (targetCongr R b.equivFun).injective
  change targetCongr R b.equivFun
      ((targetCongr R b.equivFun).symm
        (standardIso R (sourceCongr R b.equivFun (sourceFrame R b)))) = _
  rw [LinearEquiv.apply_symm_apply, sourceFrame_equivFun, standardIso_generator,
    targetFrame_equivFun]

section Semilinear

variable {R} {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]
  (φ : R →+* S) (f : M →ₛₗ[φ] N)

def sourceMapSL : Source R M →ₛₗ[φ] Source S N :=
  ExteriorAlgebra.powMapₛₗ 6 φ (SymPow.symMapₛₗ 2 φ f)

def targetMapSL : Target R M →ₛₗ[φ] Target S N :=
  SymPow.symMapₛₗ 4 φ (ExteriorAlgebra.powMapₛₗ 3 φ f)

theorem quadraticBasis_semilinear (b : Basis (Fin 3) R M) (c : Basis (Fin 3) S N)
    (hf : ∀ i, f (b i) = c i) (i : Fin 6) :
    SymPow.symMapₛₗ 2 φ f (quadraticBasis R b i) = quadraticBasis S c i := by
  apply Subtype.ext
  change SymmetricAlgebra.mapₛₗ φ f (quadraticBasis R b i : SymmetricAlgebra R M) =
    (quadraticBasis S c i : SymmetricAlgebra S N)
  rw [quadraticBasis_coe, quadraticBasis_coe, map_mul,
    SymmetricAlgebra.mapₛₗ_ι, SymmetricAlgebra.mapₛₗ_ι, hf, hf]

theorem sourceFrame_semilinear (b : Basis (Fin 3) R M) (c : Basis (Fin 3) S N)
    (hf : ∀ i, f (b i) = c i) :
    sourceMapSL φ f (sourceFrame R b) = sourceFrame S c := by
  change ExteriorAlgebra.powMapₛₗ 6 φ (SymPow.symMapₛₗ 2 φ f)
    (exteriorPower.ιMulti R 6 (quadraticBasis R b)) = _
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti]
  congr 1
  funext i
  exact quadraticBasis_semilinear φ f b c hf i

theorem targetFrame_semilinear (b : Basis (Fin 3) R M) (c : Basis (Fin 3) S N)
    (hf : ∀ i, f (b i) = c i) :
    targetMapSL φ f (targetFrame R b) = targetFrame S c := by
  have hb : ExteriorAlgebra.powMapₛₗ 3 φ f (Stacks.ExteriorPower.topBasis b 0) =
      Stacks.ExteriorPower.topBasis c 0 := by
    rw [Stacks.ExteriorPower.topBasis_apply, Stacks.ExteriorPower.topBasis_apply,
      ExteriorAlgebra.powMapₛₗ_ιMulti]
    congr 1
    exact funext hf
  apply Subtype.ext
  change SymmetricAlgebra.mapₛₗ φ (ExteriorAlgebra.powMapₛₗ 3 φ f)
      (powerBasis R 4 (Stacks.ExteriorPower.topBasis b) 0 : SymmetricAlgebra R (⋀[R]^3 M)) =
    (powerBasis S 4 (Stacks.ExteriorPower.topBasis c) 0 : SymmetricAlgebra S (⋀[S]^3 N))
  rw [powerBasis_coe, powerBasis_coe, map_pow, SymmetricAlgebra.mapₛₗ_ι, hb]

/-- Restriction compatibility follows from the actual images of the
original frame; no overlap or gluing equation is supplied. -/
theorem basisIso_semilinear (b : Basis (Fin 3) R M) (c : Basis (Fin 3) S N)
    (hf : ∀ i, f (b i) = c i) (x : Source R M) :
    basisIso S c (sourceMapSL φ f x) = targetMapSL φ f (basisIso R b x) := by
  have h : (basisIso S c).toLinearMap.comp (sourceMapSL φ f) =
      (targetMapSL φ f).comp (basisIso R b).toLinearMap := by
    apply (Stacks.ExteriorPower.topBasis (quadraticBasis R b)).ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Stacks.ExteriorPower.topBasis_apply]
    change basisIso S c (sourceMapSL φ f (sourceFrame R b)) =
      targetMapSL φ f (basisIso R b (sourceFrame R b))
    rw [sourceFrame_semilinear φ f b c hf, basisIso_generator, basisIso_generator,
      targetFrame_semilinear φ f b c hf]
  exact DFunLike.congr_fun h x

end Semilinear

section CommutingSquares

variable {R} {S : Type*} [CommRing S]
  {M' N N' : Type*} [AddCommGroup M'] [Module R M']
  [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S N']
  (φ : R →+* S) (f : M →ₛₗ[φ] N) (g : M' →ₛₗ[φ] N')
  (a : M →ₗ[R] M') (b : N →ₗ[S] N') (h : ∀ x, g (a x) = b (f x))

include h

/-- The genuine exterior functor carries an actual semilinear
commuting square to the corresponding square on every power. -/
theorem exterior_commutingSquare (n : ℕ) (x : ⋀[R]^n M) :
    ExteriorAlgebra.powMapₛₗ n φ g (exteriorPower.map n a x) =
      exteriorPower.map n b (ExteriorAlgebra.powMapₛₗ n φ f x) := by
  have hs : (ExteriorAlgebra.powMapₛₗ n φ g).comp (exteriorPower.map n a) =
      (exteriorPower.map n b).comp (ExteriorAlgebra.powMapₛₗ n φ f) := by
    apply ExteriorAlgebra.powExtₛₗ
    intro s
    simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
      ExteriorAlgebra.powMapₛₗ_ιMulti]
    congr 1
    exact funext (fun i => h (s i))
  exact DFunLike.congr_fun hs x

/-- The same actual square for every native symmetric power. -/
theorem symmetric_commutingSquare (n : ℕ) (x : SymPow.symmetricPower n R M) :
    SymPow.symMapₛₗ n φ g (SymPow.symMap n a x) =
      SymPow.symMap n b (SymPow.symMapₛₗ n φ f x) := by
  have hs : (SymPow.symMapₛₗ n φ g).comp (SymPow.symMap n a) =
      (SymPow.symMap n b).comp (SymPow.symMapₛₗ n φ f) := by
    apply SymPow.ext_of_prod_ι
    intro s
    apply Subtype.ext
    change SymmetricAlgebra.mapₛₗ φ g
        (SymPow.symAlgMap a (∏ i, SymmetricAlgebra.ι R M (s i))) =
      SymPow.symAlgMap b (SymmetricAlgebra.mapₛₗ φ f
        (∏ i, SymmetricAlgebra.ι R M (s i)))
    simp only [map_prod, SymPow.symAlgMap_ι, SymmetricAlgebra.mapₛₗ_ι]
    exact Finset.prod_congr rfl (fun i _ => congrArg (SymmetricAlgebra.ι S N') (h (s i)))
  exact DFunLike.congr_fun hs x

end CommutingSquares

end M9Native.SymmetricSquareDeterminantLinear
