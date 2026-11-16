module

public import M9StacksIntegration.AllTestRelativeFamilyModel
public import M9StacksIntegration.AllTestOriginalFamilyCommonModel
public import M9StacksIntegration.BoundedOriginalFamilyCoarseValue

/-! Actual chosen coarse values for EVERY original family over Spec A.
An actual finite K-stage model exists without containing Spec A in the
selected site. Genuine original common models prove independence of every
model choice, with all nonschematic total spaces and original maps kept. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9Native.RelativeOriginalFamilyCoarseValue
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.NativeRelativeAffineModels
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestRelativeFamilyModel
  M9StacksIntegration.AllTestOriginalFamilyCommonModel

universe u

/-- The literal full-original presheaf of the actual chosen native coarse space. -/
abbrev coarsePresheaf (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g) :=
  (originalPresheafFunctor K B hK).obj
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)

/-- Every actual finite K-stage is an object of the selected site. -/
def stageObject (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) (i : (Finset A)ᵒᵖ) :
    BigFppfOver B (Spec (.of K)) hK :=
  (BigAffineFppf.inclusion B (Spec (.of K)) hK).obj
    ((M9StacksIntegration.NativeRelativeAffineModels.diagram K A B hK).obj i)

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)
  (A : Type u) [CommRing A] [Algebra K A]

/-- The actual chosen coarse value of an original family at a finite K-stage. -/
def stageValue (i : (Finset A)ᵒᵖ)
    (Fi : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj i) g) :
    (coarsePresheaf B hZ K hK g hg).obj
      (op ((AdjoinFinset.specOverDiagram K A).obj i)) :=
  BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg
    (T := stageObject K A B hK i) Fi

/-- These values commute with every full-original Cartesian transition map. -/
theorem stageValue_naturality {i j : (Finset A)ᵒᵖ} (a : i ⟶ j)
    (Fi : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj i) g)
    (Fj : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj j) g)
    (r : Fi.total.obj ⟶ Fj.total.obj)
    (hcart : IsPullback r Fi.projection Fj.projection
      (yoneda.map ((AdjoinFinset.specOverDiagram K A).map a))) :
    (coarsePresheaf B hZ K hK g hg).map ((AdjoinFinset.specOverDiagram K A).map a).op
      (stageValue B hZ K hK g hg A j Fj) = stageValue B hZ K hK g hg A i Fi :=
  BoundedOriginalFamilyCoarseValue.originalValue_naturality B hZ K hK g hg
    (U := stageObject K A B hK i) (T := stageObject K A B hK j)
    ((BigAffineFppf.inclusion B (Spec (.of K)) hK).map
      ((M9StacksIntegration.NativeRelativeAffineModels.diagram K A B hK).map a))
    Fj Fi r hcart

/-- Pull the actual finite-stage value along the literal original cone map. -/
def modelValue (i : (Finset A)ᵒᵖ)
    (Fi : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj i) g) :
    (coarsePresheaf B hZ K hK g hg).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))))) :=
  (coarsePresheaf B hZ K hK g hg).map ((AdjoinFinset.specOverCone K A).π.app i).op
    (stageValue B hZ K hK g hg A i Fi)

/-- A genuine stage transition leaves its pulled original coarse value unchanged. -/
theorem modelValue_transition {i j : (Finset A)ᵒᵖ} (a : i ⟶ j)
    (Fi : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj i) g)
    (Fj : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj j) g)
    (r : Fi.total.obj ⟶ Fj.total.obj)
    (hcart : IsPullback r Fi.projection Fj.projection
      (yoneda.map ((AdjoinFinset.specOverDiagram K A).map a))) :
    modelValue B hZ K hK g hg A j Fj = modelValue B hZ K hK g hg A i Fi := by
  let M := coarsePresheaf B hZ K hK g hg
  have hn := stageValue_naturality B hZ K hK g hg A a Fi Fj r hcart
  have hcomp :
      M.map (((AdjoinFinset.specOverCone K A).π.app i ≫
          (AdjoinFinset.specOverDiagram K A).map a).op) (stageValue B hZ K hK g hg A j Fj) =
        M.map ((AdjoinFinset.specOverCone K A).π.app i).op
          (M.map ((AdjoinFinset.specOverDiagram K A).map a).op
            (stageValue B hZ K hK g hg A j Fj)) :=
    ConcreteCategory.congr_hom (M.map_comp _ _) _
  rw [(AdjoinFinset.specOverCone K A).w a] at hcomp
  exact hcomp.trans (congrArg (M.map ((AdjoinFinset.specOverCone K A).π.app i).op) hn)

/-- Any two actual finite-stage models of the same FULL original family
produce the same literal chosen coarse value. The common model is derived. -/
theorem modelValue_eq
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g)
    (i j : (Finset A)ᵒᵖ)
    (Fi : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj i) g)
    (Fj : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj j) g)
    (ri : F.total.obj ⟶ Fi.total.obj) (rj : F.total.obj ⟶ Fj.total.obj)
    (hri : IsPullback ri F.projection Fi.projection
      (yoneda.map ((AdjoinFinset.specOverCone K A).π.app i)))
    (hrj : IsPullback rj F.projection Fj.projection
      (yoneda.map ((AdjoinFinset.specOverCone K A).π.app j))) :
    modelValue B hZ K hK g hg A i Fi = modelValue B hZ K hK g hg A j Fj := by
  obtain ⟨l, a, b, H, si, sj, _, hsi, hsj⟩ :=
    exists_common_original_stage K A B hK g F i j Fi Fj ri rj hri hrj
  exact (modelValue_transition B hZ K hK g hg A a H Fi si hsi).trans
    (modelValue_transition B hZ K hK g hg A b H Fj sj hsj).symm

/-- Actual original family model data; no native membership or comparison is stored. -/
structure FiniteModel
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) where
  index : (Finset A)ᵒᵖ
  family : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj index) g
  totalMap : F.total.obj ⟶ family.total.obj
  cartesian : IsPullback totalMap F.projection family.projection
    (yoneda.map ((AdjoinFinset.specOverCone K A).π.app index))

include B hK in
/-- Real finite-stage approximation produces this data for every original family. -/
theorem exists_finiteModel
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    Nonempty (FiniteModel K g A F) := by
  obtain ⟨i, Fi, r, _, hr⟩ := exists_original_family_model_in_field_site K A B hK g F
  exact ⟨⟨i, Fi, r, hr⟩⟩

include B hK in
/-- A chosen actual model, whose effect on coarse values is proved independent. -/
def finiteModel
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    FiniteModel K g A F :=
  Classical.choice (exists_finiteModel B K hK g A F)

/-- The literal chosen-coarse section of ANY original family over Spec A. -/
def valueSpec
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    (coarsePresheaf B hZ K hK g hg).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))))) :=
  modelValue B hZ K hK g hg A (finiteModel B K hK g A F).index
    (finiteModel B K hK g A F).family

/-- Every actual model gives the same section; no equality premise is required. -/
theorem valueSpec_eq_model
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g)
    (m : FiniteModel K g A F) :
    valueSpec B hZ K hK g hg A F = modelValue B hZ K hK g hg A m.index m.family :=
  modelValue_eq B hZ K hK g hg A F _ _ _ _
    (finiteModel B K hK g A F).totalMap m.totalMap
    (finiteModel B K hK g A F).cartesian m.cartesian

/-- On a contained affine base this is exactly the original bounded chosen
value, rather than a new classifier assumed compatible with it. -/
theorem valueSpec_eq_originalValue (hA : B.Contains (Spec (.of A)))
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    valueSpec B hZ K hK g hg A F =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg
        (T := siteObject B (Spec (.of K)) hK hA
          (Spec.map (CommRingCat.ofHom (algebraMap K A)))) F := by
  let m := finiteModel B K hK g A F
  let TA := siteObject B (Spec (.of K)) hK hA
    (Spec.map (CommRingCat.ofHom (algebraMap K A)))
  let a : TA ⟶ stageObject K A B hK m.index :=
    boundedPreimage B K hK ((AdjoinFinset.specOverCone K A).π.app m.index)
  exact BoundedOriginalFamilyCoarseValue.originalValue_naturality B hZ K hK g hg
    (U := TA) (T := stageObject K A B hK m.index) a m.family F m.totalMap m.cartesian

end M9Native.RelativeOriginalFamilyCoarseValue
