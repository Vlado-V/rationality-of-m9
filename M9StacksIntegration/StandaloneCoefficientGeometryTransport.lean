module

public import M9StacksIntegration.StandaloneCoefficientSpaceTransport
public import M9StacksIntegration.StandaloneAffineCoefficientTransport

/-! Genuine same-universe coefficient transport of common-open rationality
and variety geometry, tested on every original scheme chart. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.StandaloneCoefficientGeometryTransport

open StandaloneCoefficientFamilyTransport

variable {K L : Type u} [Field K] [Field L]
    (e : Spec (.of K) ≅ Spec (.of L))

/-- A transported represented chart uses the same underlying test scheme. -/
def chartForward {G : M9StandaloneDraft.Presheaves K}
    (V : M9StandaloneDraft.Schemes K) (v : yoneda.obj V ⟶ G) :
    yoneda.obj ((forward e).obj V) ⟶ presheafForward e G :=
  (yonedaForwardIso e V).inv ≫ presheafForwardMap e v

theorem chartForward_property (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {G : M9StandaloneDraft.Presheaves K}
    (V : M9StandaloneDraft.Schemes K) (v : yoneda.obj V ⟶ G)
    (hv : (P.inverseImage (Over.forget (Spec (.of K)))).presheaf v) :
    (P.inverseImage (Over.forget (Spec (.of L)))).presheaf (chartForward e V v) := by
  let a : Arrow.mk (chartForward e V v) ≅ Arrow.mk (presheafForwardMap e v) :=
    Arrow.isoMk (yonedaForwardIso e V).symm (Iso.refl _) (by simp [chartForward])
  exact ((P.inverseImage (Over.forget (Spec (.of L)))).presheaf.arrow_mk_iso_iff a).mpr
    (presheafProperty_forward e P v hv)

/-- Recover an arbitrary original chart over the inverse base map. -/
def chartBackward {G : M9StandaloneDraft.Presheaves K}
    (V : M9StandaloneDraft.Schemes L) (v : yoneda.obj V ⟶ presheafForward e G) :
    yoneda.obj ((backward e).obj V) ⟶ G :=
  (yonedaForwardIso e.symm V).inv ≫ presheafForwardMap e.symm v ≫
    ((presheafEquivalence e).unitIso.app G).inv

theorem chartBackward_property (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {G : M9StandaloneDraft.Presheaves K}
    (V : M9StandaloneDraft.Schemes L) (v : yoneda.obj V ⟶ presheafForward e G)
    (hv : (P.inverseImage (Over.forget (Spec (.of L)))).presheaf v) :
    (P.inverseImage (Over.forget (Spec (.of K)))).presheaf (chartBackward e V v) := by
  let a : Arrow.mk (chartBackward e V v) ≅ Arrow.mk (presheafForwardMap e.symm v) :=
    Arrow.isoMk (yonedaForwardIso e.symm V).symm
      ((presheafEquivalence e).unitIso.app G) (by
        simp [chartBackward]
        exact (Category.comp_id _).symm)
  exact ((P.inverseImage (Over.forget (Spec (.of K)))).presheaf.arrow_mk_iso_iff a).mpr
    (presheafProperty_forward e.symm P v hv)

/-- The inverse chart square is actually Cartesian. Its scheme arrow is
literally the original physical arrow of the given square. -/
theorem chartBackward_pullback
    {F G : M9StandaloneDraft.Presheaves K}
    (j : F ⟶ G) {V P : M9StandaloneDraft.Schemes L}
    (v : yoneda.obj V ⟶ presheafForward e G) (a : P ⟶ V)
    (b : yoneda.obj P ⟶ presheafForward e F)
    (h : IsPullback b (yoneda.map a) (presheafForwardMap e j) v) :
    IsPullback (chartBackward e P b) (yoneda.map ((backward e).map a)) j
      (chartBackward e V v) := by
  apply (representedPullback_forward e.symm b a (presheafForwardMap e j) v h).of_iso'
    (Iso.refl _) ((presheafEquivalence e).unitIso.app F)
    (Iso.refl _) ((presheafEquivalence e).unitIso.app G)
  · simp [chartBackward]
    exact (Category.comp_id _).symm
  · rfl
  · exact ((presheafEquivalence e).unitIso.hom.naturality j).symm
  · simp [chartBackward]
    exact (Category.comp_id _).symm

/-- Density is checked against every original etale chart, whose inverse
transport retains the same physical scheme map. -/
theorem denseOpen_forward
    {F G : M9StandaloneDraft.Presheaves K} (j : F ⟶ G)
    (h : M9StandaloneDraft.DenseOpen K j) :
    M9StandaloneDraft.DenseOpen L (presheafForwardMap e j) := by
  refine ⟨presheafProperty_forward e (@IsOpenImmersion.{u}) j h.1, ?_⟩
  intro V v hv P a b hcart
  exact h.2 ((backward e).obj V) (chartBackward e V v)
    (chartBackward_property e (@Etale.{u}) V v hv) ((backward e).obj P)
    ((backward e).map a) (chartBackward e P b)
    (chartBackward_pullback e j v a b hcart)

/-- Replacing the domain by an actual isomorphic presheaf preserves the
same dense open and its physical pullback maps. -/
theorem denseOpen_precompIso
    {F F' G : M9StandaloneDraft.Presheaves K} (a : F' ≅ F) (j : F ⟶ G)
    (h : M9StandaloneDraft.DenseOpen K j) :
    M9StandaloneDraft.DenseOpen K (a.hom ≫ j) := by
  let z : Arrow.mk (a.hom ≫ j) ≅ Arrow.mk j :=
    Arrow.isoMk a (Iso.refl _) (by simp)
  refine ⟨((MorphismProperty.inverseImage (@IsOpenImmersion.{u})
    (Over.forget (Spec (.of K)))).presheaf.arrow_mk_iso_iff z).mpr h.1, ?_⟩
  intro V v hv P q b hb
  apply h.2 V v hv P q (b ≫ a.hom)
  apply hb.of_iso' (Iso.refl _) a.symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp

theorem chartForward_denseOpen
    {G : M9StandaloneDraft.Presheaves K}
    (V : M9StandaloneDraft.Schemes K) (v : yoneda.obj V ⟶ G)
    (hv : M9StandaloneDraft.DenseOpen K v) :
    M9StandaloneDraft.DenseOpen L (chartForward e V v) :=
  denseOpen_precompIso (yonedaForwardIso e V).symm (presheafForwardMap e v)
    (denseOpen_forward e v hv)

/-- The full variety condition is retained, including arbitrary etale
charts and an actual finite-type atlas over the relabeled base. -/
theorem varietySpace_forward (M : M9StandaloneDraft.Space K)
    (h : M9StandaloneDraft.VarietySpace K M) :
    M9StandaloneDraft.VarietySpace L (spaceForward e M) := by
  refine ⟨?_, ?_, ?_⟩
  · have hd := presheafProperty_forward e (@IsClosedImmersion.{u}) (diag M.obj) h.1
    exact ((MorphismProperty.inverseImage (@IsClosedImmersion.{u})
      (Over.forget (Spec (.of L)))).presheaf.arrow_mk_iso_iff
        (diagonalForwardArrowIso e M.obj)).mp hd
  · intro V v hv
    exact h.2.1 ((backward e).obj V) (chartBackward e V v)
      (chartBackward_property e (@Etale.{u}) V v hv)
  · obtain ⟨V, v, he, hs, hft, hqc⟩ := h.2.2
    let _ := hft
    let _ := hqc
    refine ⟨(forward e).obj V, chartForward e V v,
      chartForward_property e (@Etale.{u}) V v he,
      chartForward_property e (@Surjective.{u}) V v hs, ?_, ?_⟩
    · change LocallyOfFiniteType (V.hom ≫ e.hom)
      infer_instance
    · change QuasiCompact (V.hom ≫ e.hom)
      infer_instance

/-- A genuine common dense affine open is transported on the same
physical source, with its original coefficient structure derived from e. -/
theorem rationalOpen_forward (n : ℕ) (M : M9StandaloneDraft.Presheaves K)
    (h : M9StandaloneDraft.RationalOpen K n M) :
    M9StandaloneDraft.RationalOpen L n (presheafForward e M) := by
  obtain ⟨U, j, hn, hd, a, ha, had, haw⟩ := h
  let _ := ha
  refine ⟨(forward e).obj U, chartForward e U j, hn,
    chartForward_denseOpen e U j hd,
    StandaloneAffineCoefficientTransport.chart n e a,
    StandaloneAffineCoefficientTransport.chart_isOpenImmersion n e a,
    StandaloneAffineCoefficientTransport.chart_dense n e a had,
    StandaloneAffineCoefficientTransport.chart_over n e a haw⟩

end M9Native.StandaloneCoefficientGeometryTransport
