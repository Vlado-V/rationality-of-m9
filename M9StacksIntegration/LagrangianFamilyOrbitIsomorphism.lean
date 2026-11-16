module

public import M9StacksIntegration.LagrangianRawFamilyAction
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth
public import M9StacksIntegration.OpenRestrictionPointFiber

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

@[expose] public section

/-! Original universal-family isomorphisms along actual symplectic orbits.
The frozen primitive coordinate convention is retained through the genuine
parameter coordinate change C. Every family below is a literal pullback of
the original universal LG five-cut projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace M9Native.LagrangianFamilyOrbitIsomorphism

open LagrangianLinearSections LagrangianParameterCoordinates LagrangianRawFamilyAction

instance rawAction_isIso (g : Sp6) : IsIso (rawAction g) :=
  inferInstanceAs (IsIso (LagrangianParameterLinearAction.action ℂ (rawUnit g⁻¹)))

instance familyAction_isIso (g : Sp6) : IsIso (familyAction g) :=
  (familyIso g).isIso_hom

/-- Applying the actual universal-family automorphism gives a genuine
isomorphism of its pullbacks over the SAME original arbitrary test scheme. -/
def rawPullbackIso {T : Scheme} (p : T ⟶ parameter ℂ) (g : Sp6) :
    pullback (familyProjection ℂ) p ≅ pullback (familyProjection ℂ) (p ≫ rawAction g) :=
  asIso (pullback.map (familyProjection ℂ) p (familyProjection ℂ) (p ≫ rawAction g)
    (familyAction g) (𝟙 T) (rawAction g) (familyAction_projection g).symm (by simp))

@[reassoc] theorem rawPullbackIso_hom_snd {T : Scheme} (p : T ⟶ parameter ℂ) (g : Sp6) :
    (rawPullbackIso p g).hom ≫ pullback.snd (familyProjection ℂ) (p ≫ rawAction g) =
      pullback.snd (familyProjection ℂ) p := by
  exact (pullback.map_snd (familyProjection ℂ) p (familyProjection ℂ) (p ≫ rawAction g)
    (familyAction g) (𝟙 T) (rawAction g) (familyAction_projection g).symm (by simp)).trans
      (Category.comp_id _)

/-- The family attached to the frozen primitive coordinates is the literal
pullback of the original raw-equation family through its actual C map. -/
abbrev coordinateFamily := pullback (familyProjection ℂ) coordinateChange.hom
abbrev coordinateProjection : coordinateFamily ⟶ parameter ℂ :=
  pullback.snd (familyProjection ℂ) coordinateChange.hom

/-- The actual C-conjugacy, together with the actual original family
isomorphism, gives the genuine lift of the frozen parameter action. -/
def coordinateFamilyAction (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    coordinateFamily ⟶ coordinateFamily :=
  pullback.map (familyProjection ℂ) coordinateChange.hom
    (familyProjection ℂ) coordinateChange.hom
    (familyAction (PrimitiveRingFieldBridge.fromOriginal h))
    (PrimitiveConstantFieldAction.schemeMap h)
    (rawAction (PrimitiveRingFieldBridge.fromOriginal h))
    (familyAction_projection (PrimitiveRingFieldBridge.fromOriginal h)).symm
    (schemeMap_coordinateChange h).symm

instance coordinateFamilyAction_isIso (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    IsIso (coordinateFamilyAction h) := by
  unfold coordinateFamilyAction
  infer_instance

/-- This is an isomorphism of the actual pulled universal family and it covers
the literal frozen native symplectic parameter action. -/
def coordinateFamilyIso (h : M9.PrimitiveStabilizer.Sp6 ℂ) : coordinateFamily ≅ coordinateFamily :=
  asIso (coordinateFamilyAction h)

@[reassoc] theorem coordinateFamilyAction_projection (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    coordinateFamilyAction h ≫ coordinateProjection =
      coordinateProjection ≫ PrimitiveConstantFieldAction.schemeMap h :=
  pullback.map_snd (familyProjection ℂ) coordinateChange.hom
    (familyProjection ℂ) coordinateChange.hom
    (familyAction (PrimitiveRingFieldBridge.fromOriginal h))
    (PrimitiveConstantFieldAction.schemeMap h)
    (rawAction (PrimitiveRingFieldBridge.fromOriginal h))
    (familyAction_projection (PrimitiveRingFieldBridge.fromOriginal h)).symm
    (schemeMap_coordinateChange h).symm

/-- The original restricted family over ANY map into its good open is the
literal pullback of the original unrestricted universal projection. -/
theorem restricted_isPullback {T : Scheme}
    (p : T ⟶ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme) :
    IsPullback
      (pullback.fst (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p ≫
        ((familyProjection ℂ) ⁻¹ᵁ LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι)
      (pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p)
      (familyProjection ℂ) (p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) :=
  (IsPullback.of_hasPullback (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p).paste_horiz
    (isPullback_morphismRestrict (familyProjection ℂ)
      (LagrangianLinearSectionGenericSmooth.goodOpen ℂ)).flip

/-- The actual restricted/unrestricted comparison retains the SAME test base. -/
def restrictedPullbackIso {T : Scheme}
    (p : T ⟶ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme) :
    pullback (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p ≅
      pullback (familyProjection ℂ)
        (p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) :=
  (restricted_isPullback p).isoPullback

@[reassoc] theorem restrictedPullbackIso_hom_snd {T : Scheme}
    (p : T ⟶ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme) :
    (restrictedPullbackIso p).hom ≫ pullback.snd (familyProjection ℂ)
        (p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) =
      pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p :=
  (restricted_isPullback p).isoPullback_hom_snd

/-- Genuine isomorphism of the original smooth curve families at two actual
raw-orbit maps, over their SAME arbitrary test base. -/
def rawGoodPullbackIso {T : Scheme}
    (p q : T ⟶ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme) (g : Sp6)
    (hpq : (p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) ≫ rawAction g =
      q ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) :
    pullback (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p ≅
      pullback (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) q :=
  restrictedPullbackIso p ≪≫
    rawPullbackIso (p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) g ≪≫
    pullback.congrHom rfl hpq ≪≫ (restrictedPullbackIso q).symm

@[reassoc] theorem rawGoodPullbackIso_hom_snd {T : Scheme}
    (p q : T ⟶ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme) (g : Sp6)
    (hpq : (p ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) ≫ rawAction g =
      q ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) :
    (rawGoodPullbackIso p q g hpq).hom ≫
      pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) q =
    pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) p := by
  have hq := restrictedPullbackIso_hom_snd q
  have hqi : (restrictedPullbackIso q).inv ≫
      pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ) q =
    pullback.snd (familyProjection ℂ)
      (q ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) := by
    rw [Iso.inv_comp_eq, hq]
  simp only [rawGoodPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, hqi]
  rw [pullback.congrHom_hom, pullback.map_snd, Category.comp_id,
    rawPullbackIso_hom_snd, restrictedPullbackIso_hom_snd]

/-- The genuine domain for the original classifier in the frozen primitive
coordinates: the inverse image of the actual original good open through C. -/
def coordinateGoodOpen : (parameter ℂ).Opens :=
  coordinateChange.hom ⁻¹ᵁ LagrangianLinearSectionGenericSmooth.goodOpen ℂ

theorem coordinateGoodOpen_nonempty : (coordinateGoodOpen : Set (parameter ℂ)).Nonempty := by
  obtain ⟨x, hx⟩ := LagrangianLinearSectionGenericSmooth.goodOpen_nonempty ℂ
  obtain ⟨y, hy⟩ := (Scheme.homeoOfIso coordinateChange).surjective x
  refine ⟨y, ?_⟩
  change coordinateChange.hom y ∈ LagrangianLinearSectionGenericSmooth.goodOpen ℂ
  change coordinateChange.hom y = x at hy
  rwa [hy]

/-- The actual map to the original good-open classifier domain, with no
basis renaming or arbitrary rational parameter identification. -/
def coordinateGoodMap : coordinateGoodOpen.toScheme ⟶
    (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).toScheme :=
  IsOpenImmersion.lift (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι
    (coordinateGoodOpen.ι ≫ coordinateChange.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact t.property)

@[reassoc] theorem coordinateGoodMap_inclusion :
    coordinateGoodMap ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι =
      coordinateGoodOpen.ι ≫ coordinateChange.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- Native original-coordinate orbit maps give literal isomorphic original
smooth LG section families over the SAME arbitrary test scheme. -/
def nativeGoodPullbackIso {T : Scheme}
    (p q : T ⟶ coordinateGoodOpen.toScheme) (h : M9.PrimitiveStabilizer.Sp6 ℂ)
    (hpq : (p ≫ coordinateGoodOpen.ι) ≫ PrimitiveConstantFieldAction.schemeMap h =
      q ≫ coordinateGoodOpen.ι) :
    pullback (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ)
        (p ≫ coordinateGoodMap) ≅
      pullback (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ)
        (q ≫ coordinateGoodMap) := by
  apply rawGoodPullbackIso (p ≫ coordinateGoodMap) (q ≫ coordinateGoodMap)
    (PrimitiveRingFieldBridge.fromOriginal h)
  calc
    ((p ≫ coordinateGoodMap) ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι) ≫
        rawAction (PrimitiveRingFieldBridge.fromOriginal h) =
      ((p ≫ coordinateGoodOpen.ι) ≫ PrimitiveConstantFieldAction.schemeMap h) ≫
        coordinateChange.hom := by
      simp only [Category.assoc, coordinateGoodMap_inclusion, schemeMap_coordinateChange]
    _ = (q ≫ coordinateGoodOpen.ι) ≫ coordinateChange.hom :=
      congrArg (fun f => f ≫ coordinateChange.hom) hpq
    _ = (q ≫ coordinateGoodMap) ≫ (LagrangianLinearSectionGenericSmooth.goodOpen ℂ).ι := by
      simp only [Category.assoc, coordinateGoodMap_inclusion]

@[reassoc] theorem nativeGoodPullbackIso_hom_snd {T : Scheme}
    (p q : T ⟶ coordinateGoodOpen.toScheme) (h : M9.PrimitiveStabilizer.Sp6 ℂ)
    (hpq : (p ≫ coordinateGoodOpen.ι) ≫ PrimitiveConstantFieldAction.schemeMap h =
      q ≫ coordinateGoodOpen.ι) :
    (nativeGoodPullbackIso p q h hpq).hom ≫
      pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ)
        (q ≫ coordinateGoodMap) =
    pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection ℂ)
      (p ≫ coordinateGoodMap) :=
  rawGoodPullbackIso_hom_snd _ _ _ _

end M9Native.LagrangianFamilyOrbitIsomorphism
