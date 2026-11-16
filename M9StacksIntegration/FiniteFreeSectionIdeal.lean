module

public import M9StacksIntegration.LagrangianMatrixChart

/-! The actual dual-evaluation zero ideal of a finite free section is generated
by its actual coordinates. The affine zero scheme of polynomial coordinates is
the original quotient spectrum, with its closed immersion retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u
namespace M9Native.FiniteFreeSectionIdeal
open M9Native.LagrangianMatrixChart M9Native.SectionZeroIdealFactorization

/-- Actual affine dual-evaluation ideals are the ideals of the genuine free coordinates. -/
theorem sectionZeroIdeal_free_top (X : Scheme.{u}) [IsAffine X] (r : ℕ)
    (s : Γ(freeOn X r,⊤)) :
    (sectionZeroIdeal X (freeOn X r) s).ideal ⟨⊤,isAffineOpen_top X⟩=
      Ideal.span (Set.range (freeSectionCoordinates X r s)) := by
  have hfree : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn X r) r :=
    AlgebraicGeometry.Grassmannian.free_isFiniteLocallyFreeOfRank X r
  have : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (freeOn X r) := hfree.isFiniteLocallyFree
  rw [sectionZeroIdeal_ideal]
  have hres : (freeOn X r).presheaf.map
      (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op s=s := by
    rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op=𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  rw [hres]
  let e := freeSectionCoordinates X r
  let ψ : Fin r → Γ(freeOn X r,⊤) →ₗ[Γ(X,⊤)] Γ(X,⊤) :=
    fun i => (LinearMap.proj i).comp e.toLinearMap
  let v : Fin r → Γ(freeOn X r,⊤) := fun i => e.symm (Pi.single i 1)
  have hdec (m : Γ(freeOn X r,⊤)) : m=∑ i : Fin r,ψ i m • v i := by
    apply e.injective
    simp only [map_sum,map_smul]
    ext j
    simp [ψ,v,Pi.single_apply]
  rw [span_eval_eq_span_coord ψ v hdec]
  rfl

def coordinateSection (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    Γ(freeOn (Spec (.of R)) r,⊤) :=
  (freeSectionCoordinates (Spec (.of R)) r).symm (fun i => (Scheme.ΓSpecIso (.of R)).inv (p i))

def coordinateIdeal (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    (Spec (.of R)).IdealSheafData :=
  sectionZeroIdeal (Spec (.of R)) (freeOn (Spec (.of R)) r) (coordinateSection R r p)

def quotientInclusion (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    Spec (.of (R ⧸ Ideal.span (Set.range p))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

instance quotientInclusion_isClosedImmersion (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    IsClosedImmersion (quotientInclusion R r p) := by
  dsimp [quotientInclusion]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem coordinateIdeal_top (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    (coordinateIdeal R r p).ideal ⟨⊤,isAffineOpen_top _⟩=
      Ideal.map (Scheme.ΓSpecIso (.of R)).inv.hom (Ideal.span (Set.range p)) := by
  rw [coordinateIdeal,sectionZeroIdeal_free_top,coordinateSection,LinearEquiv.apply_symm_apply]
  rw [Ideal.map_span,← Set.range_comp]
  rfl

theorem quotientInclusion_ker_appTop (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    RingHom.ker (quotientInclusion R r p).appTop.hom=
      Ideal.map (Scheme.ΓSpecIso (.of R)).inv.hom (Ideal.span (Set.range p)) := by
  let e : R ≃+* Γ(Spec (.of R),⊤) := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  ext a
  obtain ⟨p0,rfl⟩ := e.surjective a
  change (quotientInclusion R r p).appTop (e p0)=0 ↔ e p0 ∈ Ideal.map e.toRingHom _
  rw [show e p0 ∈ Ideal.map e.toRingHom (Ideal.span (Set.range p)) ↔
      p0 ∈ Ideal.span (Set.range p) from Ideal.apply_mem_of_equiv_iff (f:=e)]
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range p))))) p0
  change (Scheme.ΓSpecIso (.of (R ⧸ Ideal.span (Set.range p)))).inv
      (Ideal.Quotient.mk (Ideal.span (Set.range p)) p0)=(quotientInclusion R r p).appTop (e p0) at hn
  rw [← hn]
  have hinv : Function.Injective (Scheme.ΓSpecIso (.of (R ⧸ Ideal.span (Set.range p)))).inv :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (R ⧸ Ideal.span (Set.range p)))).inv).injective
  exact (map_eq_zero_iff _ hinv).trans Ideal.Quotient.eq_zero_iff_mem

/-- Equality of the genuine affine ideal sheaves, with no pointwise substitute. -/
theorem coordinateIdeal_eq_kernel (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    coordinateIdeal R r p=(quotientInclusion R r p).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [coordinateIdeal_top]
  rw [Scheme.ker_of_isAffine,Scheme.IdealSheafData.ofIdealTop_ideal]
  rw [show (Spec (.of R)).presheaf.map
    (homOfLE (show (⊤ : (Spec (.of R)).Opens) ≤ ⊤ from le_top)).op=𝟙 _ from
      CategoryTheory.Functor.map_id _ _]
  change _=Ideal.map (RingHom.id _) _
  rw [Ideal.map_id]
  exact (quotientInclusion_ker_appTop R r p).symm

def coordinateZeroSchemeIsoQuotient (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    (coordinateIdeal R r p).subscheme ≅ Spec (.of (R ⧸ Ideal.span (Set.range p))) :=
  eqToIso (congrArg (fun I : (Spec (.of R)).IdealSheafData => I.subscheme)
    (coordinateIdeal_eq_kernel R r p)) ≪≫ (asIso (quotientInclusion R r p).toImage).symm


@[reassoc] theorem coordinateZeroSchemeIsoQuotient_hom_inclusion
    (R : Type u) [CommRing R] (r : ℕ) (p : Fin r → R) :
    (coordinateZeroSchemeIsoQuotient R r p).hom ≫ quotientInclusion R r p=
      (coordinateIdeal R r p).subschemeι := by
  rw [coordinateZeroSchemeIsoQuotient,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    asIso_toImage_inv_imageι]
  exact eqToIso_subscheme_ι _ _ (coordinateIdeal_eq_kernel R r p)

end M9Native.FiniteFreeSectionIdeal
end
