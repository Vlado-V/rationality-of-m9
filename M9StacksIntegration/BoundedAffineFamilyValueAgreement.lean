module

public import M9StacksIntegration.AllTestBoundedCharts
public import M9StacksIntegration.AllTestFamilyPullback
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Bounded family values agree once they agree on affine bases

The actual affine open cover of a bounded base has bounded members by
the size theorem for open immersions. Its original field maps give actual
native base arrows. The two genuine Cartesian naturality laws compare
values after every cover arrow; full original fppf sheaf separatedness
then gives equality on the entire base. The cover index is unrestricted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.BoundedAffineFamilyValueAgreement

open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestFamilyPullback

/-- Actual affine agreement and actual bounded Cartesian naturality
imply agreement on every bounded base, with no affine or quasi-compact
condition on that base and no bound on either total space. -/
theorem bounded_value_agreement_of_affine
    (B : BigFppfSite.{u}) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (g : ℕ)
    {M : M9StandaloneDraft.Presheaves K}
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (v : ∀ T : BigFppfOver B (Spec (.of K)) hK,
      M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g →
        M.obj (op ((boundedInclusion B K hK).obj T)))
    (hv : ∀ (T U : BigFppfOver B (Spec (.of K)) hK) (a : U ⟶ T)
      (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
      (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
      (r : G.total.obj ⟶ F.total.obj),
      IsPullback r G.projection F.projection (yoneda.map ((boundedInclusion B K hK).map a)) →
        M.map ((boundedInclusion B K hK).map a).op (v T F) = v U G)
    (c : M9StandaloneDraft.Classifier K g M)
    (haff : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
      (_ : IsAffine ((boundedInclusion B K hK).obj T).left)
      (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
      c.value ((boundedInclusion B K hK).obj T) F = v T F)
    (T : BigFppfOver B (Spec (.of K)) hK)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    c.value ((boundedInclusion B K hK).obj T) F = v T F := by
  let incl := boundedInclusion B K hK
  let X := (incl.obj T).left
  let U : X.affineCover.I₀ → BigFppfOver B (Spec (.of K)) hK := fun i =>
    siteObject B (Spec (.of K)) hK
      (Scheme.size_lt_of_isOpenImmersion (X.affineCover.f i) T.left.property)
      (X.affineCover.f i ≫ (incl.obj T).hom)
  let a : ∀ i, U i ⟶ T := fun i =>
    boundedPreimage B K hK (Over.homMk (X.affineCover.f i) rfl)
  let J := Scheme.fppfTopology.over (M9StandaloneDraft.Base K)
  have hcover : Sieve.ofArrows (fun i => incl.obj (U i)) (fun i => incl.map (a i)) ∈
      J (incl.obj T) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows (fun i => X.affineCover.X i) (fun i => X.affineCover.f i) ∈
      Scheme.fppfTopology X
    apply Precoverage.generate_mem_toGrothendieck
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ X.affineCover.mem₀
  have htype : Presieve.IsSheaf J M := (isSheaf_iff_isSheaf_of_type J M).mp hM
  apply (htype.isSheafFor
    (Presieve.ofArrows (fun i => incl.obj (U i)) (fun i => incl.map (a i))) hcover).isSeparatedFor.ext
  intro V f hf
  obtain ⟨i⟩ := hf
  let a₀ := incl.map (a i)
  letI : HasPullback F.projection (yoneda.map a₀) :=
    originalPresheafPullback K F.projection (yoneda.map a₀)
  let G := pullbackFamily K F a₀
  let r : G.total.obj ⟶ F.total.obj := pullback.fst F.projection (yoneda.map a₀)
  have hcart : IsPullback r G.projection F.projection (yoneda.map a₀) :=
    pullbackFamily_isPullback K F a₀
  have hU : IsAffine (incl.obj (U i)).left := by
    change IsAffine (X.affineCover.X i)
    infer_instance
  exact (c.naturality (incl.obj T) (incl.obj (U i)) a₀ F G r hcart).trans
    ((haff (U i) hU G).trans (hv T (U i) (a i) F G r hcart).symm)

end M9Native.BoundedAffineFamilyValueAgreement
