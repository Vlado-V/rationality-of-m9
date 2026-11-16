module

public import M9StacksIntegration.RelativeOriginalFamilyCoarseValue
public import M9StacksIntegration.AdjoinFinsetBaseMapFactorization
public import M9StacksIntegration.AllTestAffineClassifierExtension

/-! The actual Spec A chosen coarse values commute with EVERY K-algebra
map and every full-original Cartesian family arrow. Neither algebra has
to belong to the selected site. Zero rings and nonschematic totals remain
included. The finite-stage factorization and family model are constructed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9Native.RelativeOriginalFamilyCoarseNaturality
open RelativeOriginalFamilyCoarseValue
  M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AdjoinFinsetBaseMapFactorization
  M9StacksIntegration.AllTestOriginalFamilyCategory
  M9StacksIntegration.AllTestFamilyPullback
  M9StacksIntegration.AllTestAffineClassifierExtension

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)
  (A R : Type u) [CommRing A] [CommRing R] [Algebra K A] [Algebra K R]

/-- Actual chosen coarse values are natural under all algebra maps and all
original Cartesian family arrows, with no containment or comparison input. -/
theorem valueSpec_naturality (φ : A →ₐ[K] R)
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g)
    (G : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)))) g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ))) :
    (coarsePresheaf B hZ K hK g hg).map (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ).op
      (valueSpec B hZ K hK g hg A F) = valueSpec B hZ K hK g hg R G := by
  let m := finiteModel B K hK g A F
  obtain ⟨j, a, htri⟩ := exists_stageMap φ m.index
  let X : CurveObject K g := ⟨(AdjoinFinset.specOverDiagram K A).obj m.index, m.family⟩
  let Φ := pullbackMap K g X a
  let Fobj : CurveObject K g :=
    ⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))), F⟩
  let Gobj : CurveObject K g :=
    ⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R))), G⟩
  let fm : Fobj ⟶ X :=
    ⟨(AdjoinFinset.specOverCone K A).π.app m.index, m.totalMap, m.cartesian⟩
  let rg : Gobj ⟶ Fobj := ⟨M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ, r, hcart⟩
  let χ := cartesianFactor K g Φ (rg ≫ fm)
    ((AdjoinFinset.specOverCone K R).π.app j) (by
      change (AdjoinFinset.specOverCone K R).π.app j ≫ a =
        M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ ≫
          (AdjoinFinset.specOverCone K A).π.app m.index
      exact htri.symm)
  let Hj := pullbackFamily K m.family a
  let mG : FiniteModel K g R G := ⟨j, Hj, χ.totalMap, χ.cartesian⟩
  have hG := valueSpec_eq_model B hZ K hK g hg R G mG
  let M := coarsePresheaf B hZ K hK g hg
  let v := stageValue B hZ K hK g hg A m.index m.family
  have hn : M.map a.op v = stageValue B hZ K hK g hg R j Hj :=
    BoundedOriginalFamilyCoarseValue.originalValue_naturality B hZ K hK g hg
      (U := stageObject K R B hK j) (T := stageObject K A B hK m.index)
      (boundedPreimage B K hK a) m.family Hj Φ.totalMap Φ.cartesian
  have hcomp₁ : M.map (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ).op
      (M.map ((AdjoinFinset.specOverCone K A).π.app m.index).op v) =
      M.map (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ ≫ (AdjoinFinset.specOverCone K A).π.app m.index).op v :=
    (ConcreteCategory.congr_hom (M.map_comp _ _) v).symm
  have hcomp₂ :
      M.map ((AdjoinFinset.specOverCone K R).π.app j ≫ a).op v =
        M.map ((AdjoinFinset.specOverCone K R).π.app j).op (M.map a.op v) :=
    ConcreteCategory.congr_hom (M.map_comp _ _) v
  rw [htri] at hcomp₁
  calc
    M.map (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ).op (valueSpec B hZ K hK g hg A F) =
        M.map ((AdjoinFinset.specOverCone K R).π.app j).op (M.map a.op v) :=
      hcomp₁.trans hcomp₂
    _ = modelValue B hZ K hK g hg R j Hj :=
      congrArg (M.map ((AdjoinFinset.specOverCone K R).π.app j).op) hn
    _ = valueSpec B hZ K hK g hg R G := hG.symm

/-- In particular the formula applies to the actual full-original pullback
family, with no family comparison supplied. -/
theorem valueSpec_pullback (φ : A →ₐ[K] R)
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    (coarsePresheaf B hZ K hK g hg).map (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ).op
      (valueSpec B hZ K hK g hg A F) =
      valueSpec B hZ K hK g hg R (pullbackFamily K F (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ)) := by
  let δ := pullbackMap K g
    (⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))), F⟩ : CurveObject K g)
    (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ)
  exact valueSpec_naturality B hZ K hK g hg A R φ F
    (pullbackFamily K F (M9StacksIntegration.AdjoinFinsetBaseMapFactorization.specOverMap φ)) δ.totalMap δ.cartesian

end M9Native.RelativeOriginalFamilyCoarseNaturality
