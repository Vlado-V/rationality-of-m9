module

public import M9StacksIntegration.GenusNineFiniteInertia
public import M9StacksIntegration.GenusNineCoarsePredicates
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenDirectH2H3
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.UniqueSmoothStableModelsEtaleDvr
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesInCurvesDM
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase

/-!
# The smooth genus-g curve stack and its coarse space

This module defines the smooth and stable curve stacks, proves separatedness for the
smooth stack, and constructs its uniform coarse algebraic space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.GenusNineCoarse

universe u w

section StableCurves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The actual open substack of the stack of curve families cut out by stability
and the native cohomological genus condition. -/
abbrev stableOpen (g : ℕ) :=
  curvesSmallOpenSubstack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)

abbrev stableStack (g : ℕ) : Stack.AlgebraicStacks.{u, u + 1} B integerBase hZ :=
  (stableOpen B hZ g).toAlgebraicStack

/-- The actual smooth genus-`g` open substack inside the stable-curve stack. -/
abbrev smoothOpen (g : ℕ) (hg : 2 ≤ g) :=
  let _ := hg
  curvesSmallOpenSubstack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
    (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)

abbrev smoothStack (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.{u, u + 1} B integerBase hZ :=
  (smoothOpen B hZ g hg).toAlgebraicStack

theorem smooth_le_stable (g : ℕ) (hg : 2 ≤ g) :
    (smoothOpen B hZ g hg).property ≤ (stableOpen B hZ g).property := by
  apply curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ
    (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
    ?_ (curvesAlgebraicStack B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))
    (curvesSmallEquivalence B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))
    (curvesSmallEquivalence_functor_comp_p B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))
  intro F hF
  exact stable_of_smooth_cohomological_genus B hZ hg hF

theorem stableStack_quasiDM (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiDMOver B integerBase hZ (stableStack B hZ g) := by
  let _ := hg
  obtain ⟨W, hW, hWdm, hstable, hgenus⟩ :=
    curvesSmall.exists_curvesDM_and_le_and_isDeligneMumfordStack_of_isOpenCurvesLocus
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ) g
      (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
      (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
  have habs : Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ
      B.contains_terminal (stableStack B hZ g) := hgenus.2.1
  have hrel := Stack.AlgebraicStacks.isDMOver_of_isAbsolutelyDM B integerBase hZ
    B.contains_terminal (stableStack B hZ g) habs
  exact Stack.AlgebraicStacks.isQuasiDM_of_isDM B integerBase hZ hrel

/-- The actual inclusion of smooth families into stable families. -/
abbrev smoothToStable (g : ℕ) (hg : 2 ≤ g) :
    smoothStack B hZ g hg ⟶ stableStack B hZ g :=
  (stableOpen B hZ g).factor B integerBase hZ (smoothOpen B hZ g hg).inclusion
    (fun X => smooth_le_stable B hZ g hg _ X.property)

theorem smoothToStable_monomorphism (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsMonomorphism B integerBase hZ (smoothToStable B hZ g hg) := by
  let F := CatFiberedInGroupoids.homFunctor (smoothToStable B hZ g hg).hom
  let G := CatFiberedInGroupoids.homFunctor (stableOpen B hZ g).inclusion.hom
  have : G.Faithful := by
    change (ObjectProperty.ι _).Faithful
    infer_instance
  have : (F ⋙ G).Full := by
    change (ObjectProperty.ι _).Full
    infer_instance
  have : (F ⋙ G).Faithful := by
    change (ObjectProperty.ι _).Faithful
    infer_instance
  exact Stack.AlgebraicStacks.isMonomorphism_of_full_and_faithful B integerBase hZ
    (smoothToStable B hZ g hg) (Functor.Full.of_comp_faithful F G) (Functor.Faithful.of_comp F G)

theorem smoothStack_separated (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (smoothStack B hZ g hg)) := by
  let h := curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ
  let hQ := isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2
  let W := curvesSmallOpenSubstack B hZ h hQ
  let f := Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)
  let E := (curvesSmallEquivalence B hZ h).inverse
  have hSmoothModels := C1590Private.uniqueSmoothStableModels_of_etaleDvr B hZ g
  have hqsCurves : Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ f :=
    Stack.AlgebraicStacks.isQuasiSeparated_of_isRelativelyFinitePresentation_relativeDiagonal
      B integerBase hZ f
      (isSeparated_and_isRelativelyFinitePresentation_diagonal_curves.{u, u + 1} B hZ).2
  let T : Set (Stack.AlgebraicStacks.points B integerBase hZ W.toAlgebraicStack) := Set.univ
  have hTo : @IsOpen _ (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val) T :=
    @isOpen_univ _ (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val)
  have hTd : @Dense _ (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val) T :=
    @dense_univ _ (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val)
  have hsep : Stack.AlgebraicStacks.IsSeparated B integerBase hZ (W.inclusion ≫ f) := by
    refine Stack.OpenSubstack.isSeparated_inclusion_comp_of_denseTestUniqueness
      B integerBase hZ f W
      (hasPropertyOnSomeSchemeAtlas_isLocallyNoetherian_schemeStack_integerBase.{u, u + 1} B hZ)
      (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h
          (C1590Private.isLimitPreserving_curvesFiberedCategory B hZ)))
      hqsCurves T hTo hTd ?_
    have hlift {U V : BigFppfOver B integerBase hZ} (a : U ⟶ V)
        {ξ η : W.toAlgebraicStack.val.val.obj} (m : ξ ⟶ η)
        (hm : W.toAlgebraicStack.val.val.p.IsHomLift a m) :=
      (isHomLift_curvesSmallEquivalence_inverse_map_iff a m.hom).1
        ((Functor.isHomLift_comp_iff W.property.ι _ _ _).1 hm)
    refine Stack.ValuativeSquare.denseTestUniqueness_of_fibre B integerBase hZ _ ?_ ?_
    · intro q hq _ ξ η c _ hc _ t ht htc
      have := hq
      have hc' := hlift _ c hc
      have ht' := hlift _ t ht
      have hξ := prop_curvesSmallEquivalence_inverse_obj hQ ξ.property
      have hη := prop_curvesSmallEquivalence_inverse_obj hQ η.property
      have hstab := stable_of_smooth_cohomological_genus B hZ hg hξ
      have hηK : (curvesProjectionOver B hZ).obj (E.obj η.obj) =
          siteObject B integerBase hZ q.field_mem
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) := by
        have := hc'
        exact IsHomLift.domain_eq _ q.genericMap (E.map c.hom)
      have hξR : (curvesProjectionOver B hZ).obj (E.obj ξ.obj) =
          siteObject B integerBase hZ q.ring_mem q.base := by
        have := ht'
        exact IsHomLift.domain_eq _ (𝟙 _) (E.map t.hom)
      obtain ⟨_, _, huniq⟩ := hSmoothModels q.R q.K q.ring_mem q.field_mem
        q.base q.genericMap q.genericMap_left (E.map c.hom) (E.map c.hom) (𝟙 _)
        hstab hstab hξ.1.1.1 hξ.1.1.1 hη.1 hη.2 hc' hc' (IsHomLift.id hηK)
      have htc' : c.hom ≫ t.hom = c.hom := congrArg (fun m => m.hom) htc
      have h₁ := huniq (E.map t.hom)
        ⟨ht', by rw [← Functor.map_comp, htc', Category.id_comp]⟩
      have h₂ := huniq (𝟙 _) ⟨IsHomLift.id hξR, by rw [Category.id_comp, Category.comp_id]⟩
      apply ObjectProperty.hom_ext
      apply E.map_injective
      exact h₁.trans (h₂.symm.trans (E.map_id ξ.obj).symm)
    · intro q hq _ ξ ξ' η η' c c' s _ hc hc' hs _
      have := hq
      have hc₀ := hlift _ c hc
      have hc₀' := hlift _ c' hc'
      have hs₀ := hlift _ s hs
      have hξ := prop_curvesSmallEquivalence_inverse_obj hQ ξ.property
      have hξ' := prop_curvesSmallEquivalence_inverse_obj hQ ξ'.property
      have hη := prop_curvesSmallEquivalence_inverse_obj hQ η.property
      obtain ⟨t₀, ⟨ht₀, htc₀⟩, _⟩ := hSmoothModels q.R q.K q.ring_mem
        q.field_mem q.base q.genericMap q.genericMap_left (E.map c.hom) (E.map c'.hom)
        (E.map s.hom) (stable_of_smooth_cohomological_genus B hZ hg hξ)
        (stable_of_smooth_cohomological_genus B hZ hg hξ') hξ.1.1.1 hξ'.1.1.1 hη.1 hη.2
        hc₀ hc₀' hs₀
      let t₁ : ξ.obj ⟶ ξ'.obj := E.preimage t₀
      have hmt : E.map t₁ = t₀ := Functor.map_preimage _ t₀
      refine ⟨ObjectProperty.homMk t₁, ?_, ?_⟩
      · refine (Functor.isHomLift_comp_iff W.property.ι _ _ _).2 ?_
        refine (isHomLift_curvesSmallEquivalence_inverse_map_iff _ t₁).2 ?_
        rwa [hmt]
      · apply ObjectProperty.hom_ext
        apply E.map_injective
        change E.map (c.hom ≫ t₁) = E.map (s.hom ≫ c'.hom)
        rwa [Functor.map_comp, Functor.map_comp, hmt]
  change Stack.AlgebraicStacks.IsSeparated B integerBase hZ
    (Stack.structureMorphism B integerBase hZ W.toAlgebraicStack)
  simpa only [f, Stack.comp_structureMorphism] using hsep

theorem smoothStack_quasiDM (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiDMOver B integerBase hZ (smoothStack B hZ g hg) := by
  have h := Stack.AlgebraicStacks.isQuasiDM_comp B integerBase hZ
    (smoothToStable B hZ g hg) (Stack.structureMorphism B integerBase hZ (stableStack B hZ g))
    (Stack.AlgebraicStacks.isQuasiDM_of_isMonomorphism B integerBase hZ
      (smoothToStable B hZ g hg) (smoothToStable_monomorphism B hZ g hg))
    (stableStack_quasiDM B hZ g hg)
  simpa only [Stack.comp_structureMorphism] using h

theorem smoothStack_finite_inertia (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsFinite B integerBase hZ
      (Stack.inertiaProjectionAlgebraicStacks B integerBase hZ (smoothStack B hZ g hg)) :=
  finite_inertia_of_separated_quasiDM B integerBase hZ (smoothStack B hZ g hg)
    (smoothStack_separated B hZ g hg) (smoothStack_quasiDM B hZ g hg)

/-- Independently universal coarse-space existence for the actual smooth curve
stack. This is not the stable compactification named as the smooth moduli space. -/
theorem exists_smoothCoarseSpace (g : ℕ) (hg : 2 ≤ g) :
    ∃ (M : AlgebraicSpaces B integerBase hZ)
      (f : smoothStack B hZ g hg ⟶ Stack.algebraicSpaceStack.{u, u + 1}
        B integerBase hZ M.obj M.property),
      Stack.IsUniformCategoricalModuliSpace B integerBase hZ M f.hom ∧
        Stack.AlgebraicStacks.IsSeparated B integerBase hZ f ∧
        Stack.IsQuasiCompactMorphism B integerBase hZ f ∧
        Stack.UniversalHomeomorphism B integerBase hZ f :=
  Stack.exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B integerBase hZ
    (smoothStack B hZ g hg) (smoothStack_finite_inertia B hZ g hg)

def smoothCoarseSpace (g : ℕ) (hg : 2 ≤ g) : AlgebraicSpaces B integerBase hZ :=
  (exists_smoothCoarseSpace B hZ g hg).choose

def smoothCoarseMap (g : ℕ) (hg : 2 ≤ g) :
    smoothStack B hZ g hg ⟶ Stack.algebraicSpaceStack.{u, u + 1} B integerBase hZ
      (smoothCoarseSpace B hZ g hg).obj (smoothCoarseSpace B hZ g hg).property :=
  (exists_smoothCoarseSpace B hZ g hg).choose_spec.choose

theorem smoothCoarseMap_uniform (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsUniformCategoricalModuliSpace B integerBase hZ
      (smoothCoarseSpace B hZ g hg) (smoothCoarseMap B hZ g hg).hom :=
  (exists_smoothCoarseSpace B hZ g hg).choose_spec.choose_spec.1

/-- The independently universal coarse space of the actual smooth genus-nine
stack over the integer base. -/
abbrev smoothGenusNineCoarseSpace := smoothCoarseSpace B hZ 9 (by decide)

/-- Actual base change of the smooth coarse space. Its identification with the
coarse space of the base-changed smooth stack is a separate flat-base-change
comparison, not part of the algebraicity assertion used here. -/
def smoothGenusNineCoarseSpaceOverField (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) : AlgebraicSpaces B (Spec (.of K)) hK :=
  ⟨(OverShriek.relocalizeRestrict (integerSiteObject B hZ hK).hom).obj
      (smoothGenusNineCoarseSpace B hZ).obj,
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) integerBase hK hZ
      (integerSiteObject B hZ hK).hom _ (smoothGenusNineCoarseSpace B hZ).property⟩


end StableCurves

end M9StacksIntegration.GenusNineCoarse
