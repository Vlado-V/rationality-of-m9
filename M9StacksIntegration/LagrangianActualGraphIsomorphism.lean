module

public import M9StacksIntegration.LagrangianAffineGraphCotangent
public import M9StacksIntegration.LagrangianAffineIsomorphism
public import M9StacksIntegration.LagrangianSymmetricSquareRank
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite

/-! Invertibility of the actual intrinsic map for the original affine quotient graph. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace M9Native.LagrangianActualGraphIsomorphism

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianCotangentSections LagrangianAffineGraphCotangent
open LagrangianChartCotangent LagrangianSymmetricSquareRank LagrangianAffineIsomorphism
open Stacks.AlgebraicGeometry.ReflexiveModules

variable (K : Type u) [Field K]

/-- An actual quotient graph in the original native affine coordinates
has an invertible actual sheaf cotangent map. -/
theorem actualGraph_cotangentMap_isIso
    (q : freeOn (chart K) 6 ⟶ freeOn (chart K) 3)
    (hq : AnnihilatesSigma (chart K) q)
    (hfirst : ∀ i j : Fin 3,Stacks.FreeSheafMatrix.toMatrix q i (j.castAdd 3)=
      if i=j then 1 else 0)
    (hlast : ∀ i j : Fin 3,Stacks.FreeSheafMatrix.toMatrix q i (Fin.natAdd 3 j)=
      (sectionMatrix K).val i j) :
    IsIso (cotangentMap (X := chart K) (S := Spec (.of K))
      (Q := freeOn (chart K) 3) (chartProjection K) q hq) := by
  let I := ULift.{u} (Fin 3)
  let e : (dualSheaf (freeOn (chart K) 3)).over ⊤ ≅
      SheafOfModules.free (R := (chart K).ringCatSheaf.over ⊤) I :=
    (freeIsoDualSheafOver (chart K) ⊤ (freeOn (chart K) 3)
      (Stacks.SheafOfModules.SliceFinite.freeOverIso
        (Rs := (chart K).ringCatSheaf) ⊤ I)).symm
  letI hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn (chart K) 3) 3 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv I 3 Equiv.ulift
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (dualSheaf (freeOn (chart K) 3)) 3 :=
    isFiniteLocallyFreeOfRank_dualSheaf _ 3 hF
  letI : (symmetricSquare (dualSheaf (freeOn (chart K) 3))).IsQuasicoherent :=
    symmetricSquare_isQuasicoherent _
  letI : (Scheme.Hom.relativeDifferentials (chartProjection K)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (chart K).ringCatSheaf).prop_of_iso
      (affineCotangentIso K).symm inferInstance
  apply isIso_of_globalSections_bijective
  refine cotangentMap_app_bijective_of_localSquareMap
    (X := chart K) (S := Spec (.of K)) (Q := freeOn (chart K) 3)
    (chartProjection K) q hq ⊤ ⊤ le_rfl I e
      ?_
  refine LagrangianGraphSectionMap.localSquareMap_graph_bijective
    (X := chart K) (S := Spec (.of K)) (chartProjection K) q (sectionMatrix K)
    hfirst hlast hq
    ((LagrangianPolynomialDifferentials.sectionsBasis K).reindex
      LagrangianNativeGraphCotangent.nativeVariableEquiv.{u}.symm) ?_
  intro i
  rw [sectionMatrix_upper]
  change (Scheme.Hom.universalRelativeDerivation (chartProjection K)).d
    (LagrangianPolynomialDifferentials.scalarEquiv K
      (MvPolynomial.X (LagrangianNativeGraphCotangent.nativeVariableEquiv.{u} i))) = _
  simp only [Module.Basis.reindex_apply, Equiv.symm_symm,
    LagrangianPolynomialDifferentials.sectionsBasis_apply]

end M9Native.LagrangianActualGraphIsomorphism
