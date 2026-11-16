module

public import M9StacksIntegration.NativeProjectiveVector
public import M9StacksIntegration.PrimitiveGaussNativeOrbit
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic

/-! Actual affine-chart compatibility for the native projective morphism of a vector.
The general affine factor proof follows the pinned WeierstrassCubicPoints proof;
the source path and hash are recorded in the accompanying provenance receipt. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open M9.ProjectiveGeometry

universe u

namespace M9Native.NativeProjectiveVectorChart

section General

variable {σ : Type*} {A S : Type u} [CommRing A] [CommRing S]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem awayLift_mk (κ : A →+* S) {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (h : κ t = 1)
    (k : ℕ) (p : A) (hp : p ∈ 𝒜 (k • d)) :
    ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t))) (Away.mk 𝒜 hd k p hp) = κ p := by
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  simpa using Localization.awayLift_mk κ t p 1 (by rw [h, one_mul]) k

theorem affine_factor (κ : A →+* S) {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (h0d : 0 < d)
    (h : κ t = 1) (hκ) :
    Proj.fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (.of S)).inv.hom.comp κ) hκ =
      Spec.map (CommRingCat.ofHom ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t)))) ≫ Proj.awayι 𝒜 t hd h0d := by
  let X := Spec (CommRingCat.of S)
  let f := (Scheme.ΓSpecIso (.of S)).inv.hom.comp κ
  have hf1 : f t = 1 := by simp [f, h]
  have hU : X.basicOpen (f t) = ⊤ := by rw [hf1, Scheme.basicOpen_one]
  have : IsIso (X.basicOpen (f t)).ι := by
    rw [hU, ← Scheme.topIso_hom]
    infer_instance
  refine (cancel_epi (X.basicOpen (f t)).ι).mp ?_
  rw [Stacks.ProjGlobalSectionsAppTop.ι_comp_fromOfGlobalSections _ _ _ h0d hd,
    ← Proj.basicOpenIsoSpec_inv_ι]
  suffices e : Proj.toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫
      (Proj.basicOpenIsoSpec 𝒜 t hd h0d).hom = (X.basicOpen (f t)).ι ≫
        Spec.map (CommRingCat.ofHom ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
          (algebraMap (Away 𝒜 t) (Localization.Away t)))) by
    rw [← reassoc_of% e, Iso.hom_inv_id_assoc]
  rw [Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom]
  have hι : (X.basicOpen (f t)).ι = (X.basicOpen (f t)).toSpecΓ ≫
      Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ Spec.map (Scheme.ΓSpecIso (.of S)).inv := by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [hι, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext _ hd
    fun k p hp => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one _ f
    hd k p hp (v := 1) (by rw [hf1, map_one, one_mul])]
  simp only [one_pow, mul_one]
  have e := awayLift_mk 𝒜 κ hd h k p hp
  rw [RingHom.comp_apply] at e
  rw [e]
  rfl

end General

open MvPolynomial M9.ProjectiveFunctionField NativeProjectiveVector

abbrev polynomial := MvPolynomial (Fin 13) ℂ
def normalTuple : Fin 14 → polynomial := Fin.cons 1 MvPolynomial.X

theorem normalTuple_span : Ideal.span (Set.range normalTuple) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one

theorem normalTuple_dehomogenize :
    vectorMap (MvPolynomial.C : ℂ →+* polynomial) normalTuple =
      (chartCoordinatesEquiv 13 0).toRingHom.comp (Dehomogenization.dehomogenize 0) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [vectorMap, chartCoordinatesEquiv, Dehomogenization.dehomogenize]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [vectorMap, normalTuple, chartCoordinatesEquiv, Dehomogenization.dehomogenize]
    · have he : (finSuccAboveEquiv (0 : Fin 14)).symm
          ⟨j.succ, Fin.succ_ne_zero j⟩ = j := by
        apply (Equiv.symm_apply_eq _).mpr
        apply Subtype.ext
        simp [finSuccAboveEquiv_apply]
      simp [vectorMap, normalTuple, chartCoordinatesEquiv,
        Dehomogenization.dehomogenize_X_of_ne, he]

theorem normalTuple_point : point MvPolynomial.C normalTuple normalTuple_span =
    PrimitiveGaussNativeOrbit.naturalChart := by
  rw [point]
  change Proj.fromOfGlobalSections (ProjectiveSpace.projectiveGrading 13)
    ((Scheme.ΓSpecIso (.of polynomial)).inv.hom.comp (vectorMap MvPolynomial.C normalTuple)) _ = _
  rw [affine_factor (ProjectiveSpace.projectiveGrading 13)
    (vectorMap MvPolynomial.C normalTuple)
    (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 13 0) Nat.one_pos
    (by simp [vectorMap, normalTuple])]
  change _ = Spec.map (CommRingCat.ofHom (chartCoordinatesEquiv 13 0).toRingHom) ≫
    ((ProjectiveChart.projectiveCoordinateIsoSpec 13 0).inv ≫
      (ProjectiveCoordinateCover.projectiveCoordinateOpen 13 0).ι)
  rw [ProjectiveChart.projectiveCoordinateIsoSpec_inv_ι, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext _
    (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 13 0)
  intro k p hp
  have h1 := awayLift_mk (ProjectiveSpace.projectiveGrading 13)
    (vectorMap MvPolynomial.C normalTuple)
    (ProjectiveChartToPolynomial.projectiveVariable_homogeneous 13 0)
    (show vectorMap MvPolynomial.C normalTuple (MvPolynomial.X 0) = 1 by
      simp [vectorMap, normalTuple]) k p hp
  have h2 := congrArg (chartCoordinatesEquiv 13 0)
    (ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk 13 0 k p hp)
  exact h1.trans ((RingHom.congr_fun normalTuple_dehomogenize p).trans h2.symm)

theorem normalized_point {R : Type} [CommRing R] [Algebra ℂ R] (y : Fin 13 → R)
    (hy : Ideal.span (Set.range (Fin.cons 1 y)) = ⊤) :
    point (algebraMap ℂ R) (Fin.cons 1 y) hy =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval y).toRingHom) ≫
        PrimitiveGaussNativeOrbit.naturalChart := by
  have h := point_map (MvPolynomial.aeval y).toRingHom MvPolynomial.C normalTuple normalTuple_span
  rw [normalTuple_point] at h
  have hf : (MvPolynomial.aeval y).toRingHom.comp MvPolynomial.C = algebraMap ℂ R := by
    ext c
    exact (MvPolynomial.aeval y).commutes c
  have hv : (MvPolynomial.aeval y).toRingHom ∘ normalTuple = Fin.cons 1 y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [normalTuple]
  simpa only [hf, hv] using h.symm

end M9Native.NativeProjectiveVectorChart
