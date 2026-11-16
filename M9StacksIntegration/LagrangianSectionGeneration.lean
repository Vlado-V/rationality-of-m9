module
public import M9StacksIntegration.LagrangianAffineDeterminant
public import M9StacksIntegration.LagrangianDeterminantPullback
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit
namespace M9Native.LagrangianSectionGeneration
open M9Native.LagrangianPluckerQuotient M9Native.LagrangianMatrixChart
open M9Native.LagrangianAffineDeterminant M9Native.LagrangianDeterminantPullback
open M9Native.LagrangianDeterminantSections

theorem freeSectionCoordinates_basis (X : Scheme.{u}) (r : ℕ) (j : Fin r) :
    freeSectionCoordinates X r (freeBasisSection X r j)=Pi.single j 1 := by
  ext i
  rw [freeSectionCoordinates_apply,freeProj_eq_freeProjection]
  change Stacks.FreeSheafMatrix.unitEndValue
    (SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up j) ≫
      SheafOfModules.freeProjection (ULift.up i))=((Pi.single j (1:Γ(X,⊤)) : Fin r → Γ(X,⊤)) i)
  exact (Stacks.FreeSheafMatrix.ιFree_comp_freeProjection_value (X:=X) i j).trans
    (by simp [Pi.single_apply,eq_comm])

theorem freeSection_eq_sum (X : Scheme.{u}) (r : ℕ) (v : Γ(freeOn X r,⊤)) :
    v=∑ j : Fin r, freeSectionCoordinates X r v j • freeBasisSection X r j := by
  apply (freeSectionCoordinates X r).injective
  simp only [map_sum,map_smul,freeSectionCoordinates_basis]
  ext i
  simp [Pi.single_apply,smul_eq_mul]

theorem sectionMap_top_basis (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (j : Fin r) :
    (sectionMap X Q s).app ⊤ (freeBasisSection X r j)=s j := by
  have h := congrArg (fun φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ Q =>
    Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X,⊤))) (sectionMap_component X Q s j)
  exact h.trans (unitHom_top_one Q (s j))

theorem sectionMap_top_apply (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (v : Γ(freeOn X r,⊤)) :
    (sectionMap X Q s).app ⊤ v=
      ∑ j : Fin r, freeSectionCoordinates X r v j • s j := by
  have h := congrArg ((sectionMap X Q s).app ⊤) (freeSection_eq_sum X r v)
  simpa only [map_sum,Scheme.Modules.Hom.app_smul,sectionMap_top_basis] using h

theorem sectionMap_top_surjective_of_span (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (e : Γ(Q,⊤) ≃ₗ[Γ(X,⊤)] Γ(X,⊤))
    (hs : Ideal.span (Set.range (fun j => e (s j)))=⊤) :
    Function.Surjective ((sectionMap X Q s).app ⊤) := by
  intro w
  have hw : e w ∈ Ideal.span (Set.range (fun j => e (s j))) := by rw [hs]; trivial
  obtain ⟨a,ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hw
  refine ⟨(freeSectionCoordinates X r).symm a,?_⟩
  apply e.injective
  rw [sectionMap_top_apply]
  simpa only [map_sum,map_smul,LinearEquiv.apply_symm_apply,smul_eq_mul] using ha


theorem unitHom_symm_top_one {X : Scheme.{u}} (Q : X.Modules)
    (f : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ Q) :
    (Scheme.Modules.unitHomEquivTop Q).symm f=Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤)) := by
  have h := congrArg (fun φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ Q =>
      Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X,⊤)))
    ((Scheme.Modules.unitHomEquivTop Q).apply_symm_apply f)
  exact (unitHom_top_one Q ((Scheme.Modules.unitHomEquivTop Q).symm f)).symm.trans h

theorem unitHom_ext_top_one {X : Scheme.{u}} (Q : X.Modules)
    (f g : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ Q)
    (h : Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤))=
      Scheme.Modules.Hom.app g ⊤ (1 : Γ(X,⊤))) : f=g := by
  apply (Scheme.Modules.unitHomEquivTop Q).symm.injective
  exact (unitHom_symm_top_one Q f).trans (h.trans (unitHom_symm_top_one Q g).symm)

/-- Unit-ideal generation of the literal determinant coordinates gives an actual
surjective sheaf map, using the actual affine determinant-line isomorphism. -/
theorem sectionMap_epi_of_span (X : Scheme.{u}) [IsAffine X] {r : ℕ}
    (s : Fin r → Γ(Scheme.Modules.exteriorPower (freeOn X 3) 3,⊤))
    (hs : Ideal.span (Set.range (fun j => freeDeterminantCoordinates X (s j)))=⊤) :
    Epi (sectionMap X (Scheme.Modules.exteriorPower (freeOn X 3) 3) s) := by
  let q := sectionMap X (Scheme.Modules.exteriorPower (freeOn X 3) 3) s
  obtain ⟨v,hv⟩ := sectionMap_top_surjective_of_span X _ s (freeDeterminantCoordinates X) hs
    (determinantVolume X)
  let u := Scheme.Modules.unitHomEquivTop (freeOn X r) v
  have hu : Scheme.Modules.Hom.app u ⊤ (1 : Γ(X,⊤))=v := unitHom_top_one (freeOn X r) v
  have hcomp : u ≫ q=determinantUnitMap X := by
    apply unitHom_ext_top_one
    calc
      _ = Scheme.Modules.Hom.app q ⊤ (Scheme.Modules.Hom.app u ⊤ (1 : Γ(X,⊤))) := rfl
      _ = Scheme.Modules.Hom.app q ⊤ v := congrArg (Scheme.Modules.Hom.app q ⊤) hu
      _ = determinantVolume X := hv
      _ = _ := (unitHom_top_one _ (determinantVolume X)).symm
  have hdi : IsIso (determinantUnitMap X) := determinantUnitMap_isIso X
  have hd : Epi (determinantUnitMap X) :=
    @IsIso.epi_of_iso _ _ _ _ (determinantUnitMap X) hdi
  have : Epi (u ≫ q) := hcomp.symm ▸ hd
  exact epi_of_epi u q


/-- The actual compatible section of the coproduct map is its original top section. -/
theorem freeHom_sectionMap (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (i : ULift.{u} (Fin r)) :
    Stacks.NonvanishingSpelling.sectionsEquiv X Q (Q.freeHomEquiv (sectionMap X Q s) i)=s i.down := by
  exact sectionMap_top_basis X Q s i.down

theorem sectionMap_eq_freeHomEquiv (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) :
    sectionMap X Q s=Q.freeHomEquiv.symm (fun i : ULift.{u} (Fin r) =>
      (Stacks.NonvanishingSpelling.sectionsEquiv X Q).symm (s i.down)) := by
  apply Q.freeHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  funext i
  apply (Stacks.NonvanishingSpelling.sectionsEquiv X Q).injective
  exact (freeHom_sectionMap X Q s i).trans
    ((Stacks.NonvanishingSpelling.sectionsEquiv X Q).apply_symm_apply (s i.down)).symm

/-- Epimorphy of the actual finite section map proves actual stalkwise generation. -/
theorem generatesStalks_of_sectionMap_epi (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (h : Epi (sectionMap X Q s)) :
    Stacks.ProjectiveFromSections.GeneratesStalks s := by
  have he : Epi (Q.freeHomEquiv.symm (fun i : ULift.{u} (Fin r) =>
      (Stacks.NonvanishingSpelling.sectionsEquiv X Q).symm (s i.down))) :=
    sectionMap_eq_freeHomEquiv X Q s ▸ h
  exact (Stacks.ProjectiveFromSections.generatesStalks_ulift_iff s).mp
    (Stacks.ProjectiveFromSections.generatesStalks_of_epi_freeHomEquiv_symm _ he)

/-- The actual finite section map commutes with actual scheme pullback. -/
theorem sectionMap_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) :
    (AlgebraicGeometry.Grassmannian.pullbackFreeIso f r).inv ≫
        (Scheme.Modules.pullback f).map (sectionMap X Q s)=
      sectionMap Y ((Scheme.Modules.pullback f).obj Q)
        (fun j => pullbackGlobalSections f Q (s j)) := by
  apply ((Scheme.Modules.pullback f).obj Q).freeHomEquiv.injective
  funext i
  apply (Stacks.NonvanishingSpelling.sectionsEquiv Y ((Scheme.Modules.pullback f).obj Q)).injective
  calc
    _ = pullbackGlobalSections f Q
        (Stacks.NonvanishingSpelling.sectionsEquiv X Q (Q.freeHomEquiv (sectionMap X Q s) i)) :=
      Stacks.ProjectiveFromSections.freeHomEquiv_pullbackFreeIso_inv f Q r (sectionMap X Q s) i
    _ = pullbackGlobalSections f Q (s i.down) :=
      congrArg (pullbackGlobalSections f Q) (freeHom_sectionMap X Q s i)
    _ = _ := (freeHom_sectionMap Y ((Scheme.Modules.pullback f).obj Q)
      (fun j => pullbackGlobalSections f Q (s j)) i).symm

/-- Postcomposition transports the actual section map by the actual map on sections. -/
theorem sectionMap_postcomp (X : Scheme.{u}) {Q Q' : X.Modules} {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (e : Q ⟶ Q') :
    sectionMap X Q s ≫ e=sectionMap X Q' (fun j => e.app ⊤ (s j)) := by
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R:=X.ringCatSheaf) (ULift.{u} (Fin r))) _ _ ?_
  rintro ⟨j⟩
  change SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up j) ≫ (sectionMap X Q s ≫ e)=
    SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up j) ≫
      sectionMap X Q' (fun j => e.app ⊤ (s j))
  rw [← Category.assoc,sectionMap_component,sectionMap_component]
  apply unitHom_ext_top_one
  calc
    _ = e.app ⊤ ((Scheme.Modules.unitHomEquivTop Q (s j)).app ⊤ (1 : Γ(X,⊤))) := rfl
    _ = e.app ⊤ (s j) := congrArg (e.app ⊤) (unitHom_top_one Q (s j))
    _ = _ := (unitHom_top_one Q' (e.app ⊤ (s j))).symm



/-- Epimorphy of actual sheaf maps is local on a genuine open-immersion cover. -/
theorem epi_of_epi_pullback_cover {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {I : Type*} {Y : I → Scheme.{u}} (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
    (hcov : ∀ x : X,∃ i,∃ y : Y i,(j i) y=x)
    (hEpi : ∀ i,Epi ((Scheme.Modules.pullback (j i)).map φ)) : Epi φ := by
  constructor
  intro Z a b hab
  have hlocal (i : I) : (Scheme.Modules.pullback (j i)).map a=
      (Scheme.Modules.pullback (j i)).map b := by
    let := hEpi i
    apply (cancel_epi ((Scheme.Modules.pullback (j i)).map φ)).1
    simpa only [Functor.map_comp] using congrArg (Scheme.Modules.pullback (j i)).map hab
  have hkey (i : I) (V : X.Opens) (hV : V ≤ (j i).opensRange) : a.app V=b.app V := by
    have he := Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
      (Scheme.Modules.restrictFunctorIsoPullback (j i)).symm (hlocal i)
    have hV' : (j i) ''ᵁ ((j i) ⁻¹ᵁ V)=V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr hV
    have hh := congrArg (fun ψ => Scheme.Modules.Hom.app ψ ((j i) ⁻¹ᵁ V)) he
    change a.app ((j i) ''ᵁ ((j i) ⁻¹ᵁ V))=b.app ((j i) ''ᵁ ((j i) ⁻¹ᵁ V)) at hh
    rwa [hV'] at hh
  apply Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover (fun i => (j i).opensRange)
  · intro x
    obtain ⟨i,y,hy⟩ := hcov x
    exact ⟨i,Scheme.Hom.mem_opensRange.mpr ⟨y,hy⟩⟩
  · intro i
    apply Scheme.Modules.hom_ext
    intro V
    change a.app (((j i).opensRange).ι ''ᵁ V)=b.app (((j i).opensRange).ι ''ᵁ V)
    exact hkey i _ (((j i).opensRange).ι_image_le V)


end M9Native.LagrangianSectionGeneration
