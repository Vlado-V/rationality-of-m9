module

public import M9StacksIntegration.SymmetricSquareLocalSections
public import M9StacksIntegration.SymmetricSquareDeterminantLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictGlue

/-!
# Actual free frames for native symmetric and exterior powers

The source is the actual degree-two native symmetric-algebra sheaf.
Its local top-line character is derived from the checked normalized
symmetric-matrix action and its actual fourth-power determinant.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open M9Native.MukaiBundleDeterminant
open scoped TensorProduct

universe u

namespace M9Native.SymmetricSquareBundleDeterminant

variable {X : Scheme.{u}}

/-- The actual native symmetric algebra, paired with the native tensor
and exterior algebras using the genuine quotient universal property. -/
def nativeAlgebras (F : X.Modules) :
    SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X) F :=
  let A := SheafOfModules.algebras (Opens.grothendieckTopology X) F
  { A with
    symmetric := Scheme.Modules.symmetricAlgebra X F
    symmetricGenerator := Scheme.Modules.symmetricAlgebraGen X F
    symmetric_isSymmetricAlgebra := Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F
    symmetricPiece_eq_zero_of_neg := Scheme.Modules.symmetricAlgebra_piece_eq_zero X F
    tensorToSymmetric := A.tensor_isTensorAlgebra.descAny
      (Scheme.Modules.symmetricAlgebra X F) (Scheme.Modules.symmetricAlgebraGen X F)
    tensorToSymmetric_extends := A.tensor_isTensorAlgebra.descAny_extends
      (Scheme.Modules.symmetricAlgebra X F) (Scheme.Modules.symmetricAlgebraGen X F) }

/-- Actual freeness of the native symmetric power on the original
finite-free open, derived from its actual universal presentation. -/
def symmetricPowerFreeOn (F : X.Modules) (W : X.Opens) (n : ℕ)
    (I : Type u) [DecidableEq I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    ((Scheme.Modules.symmetricAlgebra X F).piece (n : ℤ)).over W ≅
      SheafOfModules.free (R := X.ringCatSheaf.over W) {d : I →₀ ℕ | d.degree = n} :=
  let B := SheafOfModules.algebras (Osharp := X.sheaf.over W)
    ((Opens.grothendieckTopology X).over W) (F.over W)
  Stacks.SheafOfModules.symmetricPowerOverIso F W n
    (Scheme.Modules.symmetricAlgebra X F) (Scheme.Modules.symmetricAlgebraGen X F)
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F)
    B.symmetric B.symmetricGenerator B.symmetric_isSymmetricAlgebra ≪≫
      Stacks.SheafOfModules.symmetricPowerFreeIsoOfIsoAnyIndex
        ((Opens.grothendieckTopology X).over W) I n B e

/-- The actual exterior power is free on the same original free open. -/
def exteriorPowerFreeOn (F : X.Modules) (W : X.Opens) (n : ℕ)
    (I : Type u)
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    (topExterior F n).over W ≅
      SheafOfModules.free (R := X.ringCatSheaf.over W) (Set.powersetCard I n) := by
  classical
  letI : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  exact Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree
    (SheafOfModules.algebras (Opens.grothendieckTopology X) F) W n I e

section LinearEquivalences

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Functoriality of the actual exterior power at a genuine linear equivalence. -/
def exteriorCongr (n : ℕ) (e : M ≃ₗ[R] N) : (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp only [LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp only [LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, exteriorPower.map_id])

end LinearEquivalences

/-- The actual rank-three basis on an open inside a free trivialization.
The original index equivalence is used rather than an assumed basis. -/
def frameBasis (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) : Module.Basis (Fin 3) Γ(X, U) Γ(F, U) := by
  letI : DecidableEq I := Classical.decEq I
  let V := op (Over.mk (homOfLE h))
  let eV := ((SheafOfModules.evaluation (X.ringCatSheaf.over W) V).mapIso e).toLinearEquiv
  exact ((Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj) (ι := I)
    (X.ringCatSheaf.over W).property V).map
    eV.symm).reindex η

theorem frameBasis_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) (i : Fin 3) :
    letI : DecidableEq I := Classical.decEq I
    frameBasis F W U h I e η i = e.inv.val.app (op (Over.mk (homOfLE h)))
      (Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj) (ι := I)
        (X.ringCatSheaf.over W).property (op (Over.mk (homOfLE h))) (η.symm i)) := by
  letI : DecidableEq I := Classical.decEq I
  let V := op (Over.mk (homOfLE h))
  let B := Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj) (ι := I)
    (X.ringCatSheaf.over W).property V
  let E := ((SheafOfModules.evaluation (X.ringCatSheaf.over W) V).mapIso e).toLinearEquiv
  change (B.map E.symm).reindex η i = E.symm (B (η.symm i))
  exact (Module.Basis.reindex_apply (B.map E.symm) η i).trans
    (Module.Basis.map_apply B E.symm (η.symm i))

/-- Actual sections of the original native determinant of Sym² F,
compared with the actual polynomial operations on the original sections. -/
def sourceSectionsEquiv (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    SymmetricSquareDeterminantLinear.Source Γ(X, U) Γ(F, U) ≃ₗ[Γ(X, U)]
      Γ(topExterior (symmetricSquare F) 6, U) := by
  classical
  exact (exteriorCongr 6 (symmetricSectionsEquivOn F W U h I e 2)).trans
    (exteriorSectionsEquivOn (symmetricSquare F) W U h
      {d : I →₀ ℕ | d.degree = 2} (symmetricPowerFreeOn F W 2 I e) 6)

/-- Actual sections of Sym⁴(det F), compared with the polynomial
operations on the same original sections of F. -/
def targetSectionsEquiv (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    SymmetricSquareDeterminantLinear.Target Γ(X, U) Γ(F, U) ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.symmetricAlgebra X (topExterior F 3)).piece 4, U) := by
  classical
  exact (SymPow.symmetricPowerCongr 4 (exteriorSectionsEquivOn F W U h I e 3)).trans
    (symmetricSectionsEquivOn (topExterior F 3) W U h
      (Set.powersetCard I 3) (exteriorPowerFreeOn F W 3 I e) 4)

@[simp] theorem sourceSectionsEquiv_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (x : SymmetricSquareDeterminantLinear.Source Γ(X, U) Γ(F, U)) :
    sourceSectionsEquiv F W U h I e x = exteriorSectionComparison (symmetricSquare F) 6 U
      (exteriorPower.map 6 (symmetricSectionComparison F 2 U) x) := rfl

@[simp] theorem targetSectionsEquiv_apply (F : X.Modules) (W U : X.Opens) (h : U ≤ W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (x : SymmetricSquareDeterminantLinear.Target Γ(X, U) Γ(F, U)) :
    targetSectionsEquiv F W U h I e x = symmetricSectionComparison (topExterior F 3) 4 U
      (SymPow.symMap 4 (exteriorSectionComparison F 3 U) x) := rfl

/-- The actual basis obtained from the original free trivialization
commutes with every restriction inside that same open. -/
theorem frameBasis_restrict (F : X.Modules) (W U V : X.Opens)
    (hVU : V ≤ U) (hUW : U ≤ W) (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (η : I ≃ Fin 3) (i : Fin 3) :
    F.presheaf.map (homOfLE hVU).op (frameBasis F W U hUW I e η i) =
      frameBasis F W V (hVU.trans hUW) I e η i := by
  letI : DecidableEq I := Classical.decEq I
  let A := Over.mk (homOfLE hUW)
  let B := Over.mk (homOfLE (hVU.trans hUW))
  let g : B ⟶ A := Over.homMk (homOfLE hVU) (by cat_disch)
  have hn := PresheafOfModules.naturality_apply e.inv.val g.op
    (Stacks.SheafOfModules.freeCoordBasis (O := (X.sheaf.over W).obj) (ι := I)
      (X.ringCatSheaf.over W).property (op A) (η.symm i))
  have hf := Stacks.SheafOfModules.freeCoordBasis_map
    (O := (X.sheaf.over W).obj) (ι := I) (X.ringCatSheaf.over W).property g.op (η.symm i)
  rw [frameBasis_apply, frameBasis_apply]
  exact hn.symm.trans (congrArg (fun z => e.inv.val.app (op B) z) hf)

/-- The original symmetric comparison commutes with restriction of
the original sections and the original scalar homomorphism. -/
theorem symmetricSectionComparison_restrict (F : X.Modules) (n : ℕ)
    (U V : X.Opens) (h : V ≤ U)
    (x : SymPow.symmetricPower n Γ(X, U) Γ(F, U)) :
    (show X.Modules from (Scheme.Modules.symmetricAlgebra X F).piece (n : ℤ)).presheaf.map
      (homOfLE h).op
        (symmetricSectionComparison F n U x) =
      symmetricSectionComparison F n V
        (SymPow.symMapₛₗ n (X.presheaf.map (homOfLE h).op).hom
          (F.val.restrictₛₗ (homOfLE h).op) x) :=
  Stacks.GradedAlgebra.cmpSections_naturality
    (Scheme.Modules.symmetricAlgebra X F).toPresheafGradedAlgebra
    (Scheme.Modules.symmetricAlgebraGen X F).val
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).1 n (homOfLE h).op x

/-- The same genuine restriction square for the original exterior comparison. -/
theorem exteriorSectionComparison_restrict (F : X.Modules) (n : ℕ)
    (U V : X.Opens) (h : V ≤ U) (x : ⋀[Γ(X, U)]^n Γ(F, U)) :
    (topExterior F n).presheaf.map (homOfLE h).op
        (exteriorSectionComparison F n U x) =
      exteriorSectionComparison F n V
        (ExteriorAlgebra.powMapₛₗ n (X.presheaf.map (homOfLE h).op).hom
          (F.val.restrictₛₗ (homOfLE h).op) x) :=
  Stacks.GradedAlgebra.extCmpSections_naturality
    (Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra
    (Scheme.Modules.exteriorGenerator F).val
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F).1 n (homOfLE h).op x

end M9Native.SymmetricSquareBundleDeterminant
