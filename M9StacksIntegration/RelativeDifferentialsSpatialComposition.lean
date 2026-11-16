module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.PullbackCompUnit

/-! Spatial composition of the actual native relative differential maps,
allowing both base morphisms to change. The proof retains the genuine
pullback comparisons and universal derivations. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.RelativeDifferentialsSpatialComposition

open AlgebraicGeometry.Scheme.Hom Stacks.ConormalSequenceRight

variable {Z W X S S₁ S₂ : Scheme.{u}}

private theorem pullback_map_unit_app_apply (j : Z ⟶ W) {F G : W.Modules} (φ : F ⟶ G)
    (V : W.Opens) (x : Γ(F, V)) :
    ((Scheme.Modules.pullback j).map φ).app (j ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app F).app V x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app G).app V (φ.app V x) := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ V)
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality φ)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

/-- **The canonical maps on relative differentials of two squares stacked along the source
compose to the canonical map of the outer square**, read on the universal differential of a
local section of `𝒪_X` pulled back to `Z`.  The iterated pullback is identified with the
pullback along the composite by `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem relativeDifferentialsMap_app_spatial_unit (j : Z ⟶ W) (ι : W ⟶ X) (p : X ⟶ S)
    (qW : W ⟶ S₁) (qZ : Z ⟶ S₂) (bW : S₁ ⟶ S) (bZ : S₂ ⟶ S₁)
    (hcommW : ι ≫ p = qW ≫ bW) (hcommZ : j ≫ qW = qZ ≫ bZ)
    (U : X.Opens) (s : Γ(X, U)) :
    (relativeDifferentialsMap j qW qZ bZ hcommZ).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback j).map
          (relativeDifferentialsMap ι p qW bW hcommW)).app ((j ≫ ι) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp j ι).inv.app (relativeDifferentials p)).app
          ((j ≫ ι) ⁻¹ᵁ U)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app
              (relativeDifferentials p)).app U)
            ((universalRelativeDerivation p).d s)))) =
      (universalRelativeDerivation qZ).d (((j ≫ ι).app U).hom s) := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ U)
    (unit_comp_pullbackComp_inv j ι (relativeDifferentials p))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app] at h
  have hm : ((Scheme.Modules.pullbackComp j ι).inv.app (relativeDifferentials p)).app
        ((j ≫ ι) ⁻¹ᵁ U)
      ((((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app
          (relativeDifferentials p)).app U) ((universalRelativeDerivation p).d s)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          ((Scheme.Modules.pullback ι).obj (relativeDifferentials p))).app (ι ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
            (relativeDifferentials p)).app U) ((universalRelativeDerivation p).d s)) := by
    have h2 := ConcreteCategory.congr_hom h ((universalRelativeDerivation p).d s)
    exact h2
  have hA := relativeDifferentialsMap_app_d (f := ι) (p := p) (p' := qW) bW hcommW U s
  rw [Adjunction.homEquiv_unit] at hA
  have hC := relativeDifferentialsMap_app_d (f := j) (p := qW) (p' := qZ) bZ hcommZ
    (ι ⁻¹ᵁ U) ((ι.app U).hom s)
  rw [Adjunction.homEquiv_unit] at hC
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j qW qZ bZ hcommZ).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback j).map
          (relativeDifferentialsMap ι p qW bW hcommW)).app ((j ≫ ι) ⁻¹ᵁ U) y)) hm) ?_
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j qW qZ bZ hcommZ).app ((j ≫ ι) ⁻¹ᵁ U) y)
    (pullback_map_unit_app_apply j
      (relativeDifferentialsMap ι p qW bW hcommW) (ι ⁻¹ᵁ U) _)) ?_
  refine Eq.trans (congrArg
    (fun y => (relativeDifferentialsMap j qW qZ bZ hcommZ).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (relativeDifferentials qW)).app (ι ⁻¹ᵁ U) y)) hA) ?_
  exact Eq.trans hC rfl

/-- **The canonical maps on relative differentials of two squares stacked along the source
compose to the canonical map of the outer square**, as an equality of morphisms of sheaves of
modules.  The uniqueness of Stacks 01UV turns the identity on universal differentials into this
one. -/
theorem relativeDifferentialsMap_spatial_comp (j : Z ⟶ W) (ι : W ⟶ X) (p : X ⟶ S)
    (qW : W ⟶ S₁) (qZ : Z ⟶ S₂) (bW : S₁ ⟶ S) (bZ : S₂ ⟶ S₁)
    (hcommW : ι ≫ p = qW ≫ bW) (hcommZ : j ≫ qW = qZ ≫ bZ)
    (hcomm : (j ≫ ι) ≫ p = qZ ≫ (bZ ≫ bW)) :
    (Scheme.Modules.pullbackComp j ι).inv.app (relativeDifferentials p) ≫
        ((Scheme.Modules.pullback j).map
            (relativeDifferentialsMap ι p qW bW hcommW) ≫
          relativeDifferentialsMap j qW qZ bZ hcommZ) =
      relativeDifferentialsMap (j ≫ ι) p qZ (bZ ≫ bW) hcomm := by
  refine (isRelativeDifferentialsMap_iff_eq (j ≫ ι) p qZ (bZ ≫ bW) hcomm _).mp ?_
  intro U s
  rw [Adjunction.homEquiv_unit]
  exact relativeDifferentialsMap_app_spatial_unit j ι p qW qZ bW bZ hcommW hcommZ U s

/-- **The composition law in the form the sections map of Stacks 03DS uses it**: the comparison
of iterated pullbacks followed by the canonical map of the outer square is the pullback of the
canonical map of the inner square followed by the canonical map of the remaining one.  The outer
source morphism is given as data with the equation `j ≫ ι = i` it satisfies, which is the shape
`AlgebraicGeometry.pullbackSectionsMap` is built in. -/
theorem relativeDifferentialsMap_spatial_comp_hom (j : Z ⟶ W) (ι : W ⟶ X) (i : Z ⟶ X)
    (hi : j ≫ ι = i) (p : X ⟶ S)
    (qW : W ⟶ S₁) (qZ : Z ⟶ S₂) (bW : S₁ ⟶ S) (bZ : S₂ ⟶ S₁)
    (hcommW : ι ≫ p = qW ≫ bW) (hcommZ : j ≫ qW = qZ ≫ bZ)
    (hcomm : i ≫ p = qZ ≫ (bZ ≫ bW)) :
    (Scheme.Modules.pullbackComp j ι).hom.app (relativeDifferentials p) ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (relativeDifferentials p) ≫
          relativeDifferentialsMap i p qZ (bZ ≫ bW) hcomm =
      (Scheme.Modules.pullback j).map
          (relativeDifferentialsMap ι p qW bW hcommW) ≫
        relativeDifferentialsMap j qW qZ bZ hcommZ := by
  subst hi
  rw [pullbackCongr_rfl_hom_app, Category.id_comp,
    ← relativeDifferentialsMap_spatial_comp j ι p qW qZ bW bZ hcommW hcommZ hcomm,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]


end M9Native.RelativeDifferentialsSpatialComposition
