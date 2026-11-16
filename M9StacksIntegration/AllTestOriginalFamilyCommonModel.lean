module

public import M9StacksIntegration.NativeCurveFamilyCommonStageRefinement
public import M9StacksIntegration.NativeRelativeAffineRebase
public import M9StacksIntegration.AllTestNativeFamilyMembership
public import M9StacksIntegration.AllTestNativeOriginalFamily
public import M9StacksIntegration.AllTestNativeFamilyFull

/-! Two actual finite-stage models of the SAME original family admit a
common actual ORIGINAL later-stage model. All original Cartesian squares,
coefficient maps, and nonschematic total spaces are retained. The auxiliary
site is constructed internally; no fixed site contains the full base A. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestOriginalFamilyCommonModel
open AllTestBoundedCharts AllTestNativeCurveFamily AllTestNativeCurveNaturality
  AllTestNativeOriginalFamily
universe u

/-- Actual original-family choices share an actual original later stage.
The native unconditional0D55 fullness is used through its checked common
refinement theorem, and native fullness recovers both full-original arrows. -/
theorem exists_common_original_stage
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (B₀ : BigFppfSite.{u}) (hK₀ : B₀.Contains (Spec (.of K))) (g : ℕ)
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
    ∃ (l : (Finset A)ᵒᵖ) (a : l ⟶ i) (b : l ⟶ j)
      (H : M9StandaloneDraft.Family K ((AdjoinFinset.specOverDiagram K A).obj l) g)
      (si : H.total.obj ⟶ Fi.total.obj) (sj : H.total.obj ⟶ Fj.total.obj),
      B₀.Contains ((AdjoinFinset.specDiagram K A).obj l) ∧
      IsPullback si H.projection Fi.projection
        (yoneda.map ((AdjoinFinset.specOverDiagram K A).map a)) ∧
      IsPullback sj H.projection Fj.projection
        (yoneda.map ((AdjoinFinset.specOverDiagram K A).map b)) := by
  obtain ⟨B₁, hB₁⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), Spec (.of A), integerBase} : Set Scheme.{u})
  have hK₁ : B₁.Contains (Spec (.of K)) := hB₁ _ (by simp)
  have hA₁ : B₁.Contains (Spec (.of A)) := hB₁ _ (by simp)
  have hZ₁ : B₁.Contains integerBase := hB₁ _ (by simp)
  let k := fieldToInteger B₁ hZ₁ K hK₁
  let D := NativeRelativeAffineRebase.diagramOver K A B₁ hK₁ integerBase hZ₁ k
  let c := NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁
  let TA := siteObject B₁ (Spec (.of K)) hK₁ hA₁
    (Spec.map (CommRingCat.ofHom (algebraMap K A)))
  let Ti := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).obj
    ((NativeRelativeAffineModels.diagram K A B₁ hK₁).obj i)
  let Tj := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).obj
    ((NativeRelativeAffineModels.diagram K A B₁ hK₁).obj j)
  let ai : TA ⟶ Ti := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).map
    ((NativeRelativeAffineModels.cone K A B₁ hK₁ hA₁).π.app i)
  let aj : TA ⟶ Tj := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).map
    ((NativeRelativeAffineModels.cone K A B₁ hK₁ hA₁).π.app j)
  let G := nativeCurveFamily B₁ hZ₁ K hK₁ (T := TA) (g := g) F
  let Gi := nativeCurveFamily B₁ hZ₁ K hK₁ (T := Ti) (g := g) Fi
  let Gj := nativeCurveFamily B₁ hZ₁ K hK₁ (T := Tj) (g := g) Fj
  let δ := nativeCartesianMap B₁ hZ₁ K hK₁ (U := TA) (T := Ti) (g := g) ai Fi F ri hri
  let ε := nativeCartesianMap B₁ hZ₁ K hK₁ (U := TA) (T := Tj) (g := g) aj Fj F rj hrj
  have hG : G.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj c.pt := rfl
  have hGi : Gi.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj (D.obj i) := rfl
  have hGj : Gj.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj (D.obj j) := rfl
  have hδ : δ.baseMap = eqToHom hG ≫
      (BigAffineFppf.inclusion B₁ integerBase hZ₁).map (c.π.app i) ≫ eqToHom hGi.symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hε : ε.baseMap = eqToHom hG ≫
      (BigAffineFppf.inclusion B₁ integerBase hZ₁).map (c.π.app j) ≫ eqToHom hGj.symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨l, a, b, Q, hQ, χ, η, θ, _, hη, hθ, _, _⟩ :=
    M9Native.NativeCurveFamilyCommonStageRefinement.exists_common_stage_of_isLimit c
      (NativeRelativeAffineRebase.isLimit_toScheme_coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁)
      G hG i j Gi Gj hGi hGj δ ε hδ hε
  let Tl := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).obj
    ((NativeRelativeAffineModels.diagram K A B₁ hK₁).obj l)
  have hbaseQ : Q.base = nativeBase B₁ hZ₁ K hK₁ Tl := hQ
  have hPGi : IsSmoothH0FamilyOfFibreGenus B₁ hZ₁ g Gi :=
    AllTestNativeFamilyMembership.nativeCurveFamily_membership B₁ hZ₁ K hK₁ (T := Ti) (g := g) Fi
  have hPQ : IsSmoothH0FamilyOfFibreGenus B₁ hZ₁ g Q :=
    (AllTestNativeFamilyMembership.intrinsic_isOpen B₁ hZ₁ g).prop_of_hom η hPGi
  let H := originalFamily B₁ hZ₁ K hK₁ Tl Q hbaseQ g hPQ
  let e := originalFamilyNativeIso B₁ hZ₁ K hK₁ Tl Q hbaseQ g hPQ
  let ai' : Tl ⟶ Ti := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).map
    ((NativeRelativeAffineModels.diagram K A B₁ hK₁).map a)
  let aj' : Tl ⟶ Tj := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).map
    ((NativeRelativeAffineModels.diagram K A B₁ hK₁).map b)
  let η' : nativeCurveFamily B₁ hZ₁ K hK₁ (T := Tl) (g := g) H ⟶ Gi := e.hom ≫ η
  let θ' : nativeCurveFamily B₁ hZ₁ K hK₁ (T := Tl) (g := g) H ⟶ Gj := e.hom ≫ θ
  have hη' : η'.baseMap = (Over.map k).map ai' := by
    change e.hom.baseMap ≫ η.baseMap = _
    rw [originalFamilyNativeIso_baseMap B₁ hZ₁ K hK₁ Tl Q hbaseQ g hPQ, hη]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl
  have hθ' : θ'.baseMap = (Over.map k).map aj' := by
    change e.hom.baseMap ≫ θ.baseMap = _
    rw [originalFamilyNativeIso_baseMap B₁ hZ₁ K hK₁ Tl Q hbaseQ g hPQ, hθ]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨si, ⟨hsi, _⟩, _⟩ :=
    AllTestNativeFamilyFull.existsUnique_original_cartesian_lift B₁ hZ₁ K hK₁
      (U := Tl) (T := Ti) (g := g) ai' Fi H η' hη'
  obtain ⟨sj, ⟨hsj, _⟩, _⟩ :=
    AllTestNativeFamilyFull.existsUnique_original_cartesian_lift B₁ hZ₁ K hK₁
      (U := Tl) (T := Tj) (g := g) aj' Fj H θ' hθ'
  exact ⟨l, a, b, H, si, sj,
    NativeRelativeAffineModels.contains_stage K A B₀ hK₀ l.unop, hsi, hsj⟩

end M9StacksIntegration.AllTestOriginalFamilyCommonModel
