module

public import M9StacksIntegration.LagrangianLocalTripleRank
public import M9StacksIntegration.FiniteRankAffineFrame
public import M9StacksIntegration.FieldPointFiberInjectivity
public import M9StacksIntegration.FieldPointDualPairing
public import M9StacksIntegration.FieldPointAdjunctionSections

/-!
# Actual transversality excludes rank-one original three-section evaluations

The original nonzero five-row relation supplies its actual conormal
line map. A genuine local quotient frame gives the original local dual
section paired to one. Actual field-point pullback and the original
adjunction identify its nonzero image with the native local determinant
derivative. The genuine determinant identity therefore forces rank at
least two at every original residue point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianTransverseTripleRank

open SpecFieldStalkSections SpecFieldPullbackSections
open LagrangianMatrixChart LagrangianUniversalSections LagrangianUniversalTriples
open LagrangianLocalTripleDeterminant LagrangianFiveSectionModel
open Stacks.AlgebraicGeometry.ReflexiveModules

variable (k : Type u) [Field k] [CharZero k]
  (M : Matrix (Fin 5) (Fin 14) k) (hM : Function.Surjective M.mulVec)
  [hSmooth : SmoothOfRelativeDimension 1
    (structureMap k (LagrangianFibreFiveSection.fiveSection k M hM))]
  (a : Fin 5 → k) (ha : a ≠ 0) (s : Fin 3 → (Fin 6 → k))
  (h : PrimitiveDecomposableNonzero.coefficients k s = Matrix.vecMul a M)
  (K : Type u) [Field K]
  (p : Spec (.of K) ⟶ curve k (LagrangianFibreFiveSection.fiveSection k M hM))
  (U : (LagrangianGrassmannian.space k).affineOpens)
  (hp : (p ≫ inclusion k (LagrangianFibreFiveSection.fiveSection k M hM)).base (point K) ∈
    (U : (LagrangianGrassmannian.space k).Opens))
  (e : bundle k (U : (LagrangianGrassmannian.space k).Opens).ι ≅ freeOn (U : Scheme.{u}) 3)

include hSmooth ha h

/-- The literal actual local determinant derivative is nonzero by genuine original transversality. -/
theorem local_determinant_derivative_ne_zero :
    FieldPointLocalDerivation.derivativeOn K (LagrangianGrassmannian.projection k)
      (p ≫ inclusion k (LagrangianFibreFiveSection.fiveSection k M hM))
      (U : (LagrangianGrassmannian.space k).Opens) hp (localMatrix k U e s).det ≠ 0 := by
  let i := inclusion k (LagrangianFibreFiveSection.fiveSection k M hM)
  let L := LagrangianPluckerQuotient.determinantLine k
  let D := dualSheaf L
  let N := Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection k)
  let tau := localFunctional k U e
  let t := LagrangianRowDifferential.rowDifferential k
    (LagrangianFibreFiveSection.fiveSection k M hM) a
  let A := (Scheme.Modules.pullbackComp p i).app D
  let B := (Scheme.Modules.pullbackComp p i).app N
  let T := A.inv ≫ (Scheme.Modules.pullback p).map t ≫ B.hom
  have hA : Function.Injective (moduleSpecΓFunctor.map A.inv).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hB : Function.Injective (moduleSpecΓFunctor.map B.hom).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have ht := FieldPointFiberInjectivity.rowDifferential_pullbackSections_injective
    K k (LagrangianFibreFiveSection.fiveSection k M hM) a ha p
  have hT : Function.Injective (moduleSpecΓFunctor.map T).hom := hB.comp (ht.comp hA)
  obtain ⟨m,hm⟩ := exists_local_pairing_one k U e
  have hn := FieldPointDualPairing.pulledSection_ne_zero_of_pairing_one K (p ≫ i) L
    (U : (LagrangianGrassmannian.space k).Opens) hp tau m hm
  have he := FieldPointAdjunctionSections.image_of_adjoint K i p D N t
    (U : (LagrangianGrassmannian.space k).Opens) hp tau
    ((Scheme.Hom.universalRelativeDerivation (LagrangianGrassmannian.projection k)).d
      (localMatrix k U e s).det)
    (rowDifferential_adjunction_matrix k U e M hM a s h)
  intro hz
  apply hn
  apply hT
  exact he.trans (hz.trans (map_zero _).symm)

/-- Genuine transversality forces rank at least two in the actual local triple matrix. -/
theorem two_le_rank_localMatrix :
    ((localMatrix k U e s).map
      (FieldPointLocalDerivation.valueOnRingHom K
        (p ≫ inclusion k (LagrangianFibreFiveSection.fiveSection k M hM))
        (U : (LagrangianGrassmannian.space k).Opens) hp)).rank ≥ 2 := by
  by_contra hn
  exact local_determinant_derivative_ne_zero k M hM a ha s h K p U hp e
    (FieldPointLocalDerivation.derivativeOn_det_eq_zero_of_rank_le_one K
      (LagrangianGrassmannian.projection k)
      (p ≫ inclusion k (LagrangianFibreFiveSection.fiveSection k M hM))
      (U : (LagrangianGrassmannian.space k).Opens) hp (localMatrix k U e s) (by omega))

omit K [Field K] p U hp e in
/-- Every original residue fibre of the actual original triple has rank at least two. -/
theorem two_le_mapRankAt_of_relation
    (x : curve k (LagrangianFibreFiveSection.fiveSection k M hM)) :
    2 ≤ MukaiSemiIrreducible.mapRankAt
      (evaluation k (structureMap k (LagrangianFibreFiveSection.fiveSection k M hM))
        (inclusion k (LagrangianFibreFiveSection.fiveSection k M hM)) s) x := by
  let C := curve k (LagrangianFibreFiveSection.fiveSection k M hM)
  let i := inclusion k (LagrangianFibreFiveSection.fiveSection k M hM)
  let K := C.residueField x
  let p := C.fromSpecResidueField x
  have hpx : p (point K) = x := Scheme.fromSpecResidueField_apply x _
  obtain ⟨U,hxU,⟨e⟩⟩ := FiniteRankAffineFrame.exists_affine_lagrangian_quotient_frame k (i x)
  have hp : (p ≫ i).base (point K) ∈ (U : (LagrangianGrassmannian.space k).Opens) := by
    simpa only [Scheme.Hom.comp_apply,hpx] using hxU
  have hr := two_le_rank_localMatrix k M hM a ha s h K p U hp e
  rw [LagrangianLocalTripleRank.rank_localMatrix_eq_mapRankAt k U e s K i p hp] at hr
  change 2 ≤ MukaiSemiIrreducible.mapRankAt
    (evaluation k (i ≫ LagrangianGrassmannian.projection k) i s) (p (point K)) at hr
  exact (congrArg (fun z : C => 2 ≤ MukaiSemiIrreducible.mapRankAt
    (evaluation k (i ≫ LagrangianGrassmannian.projection k) i s) z) hpx).mp hr

end M9Native.LagrangianTransverseTripleRank
