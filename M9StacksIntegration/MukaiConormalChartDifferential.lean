module

public import M9StacksIntegration.MukaiConormalFieldDifferential
public import M9StacksIntegration.MukaiConormalChartJets
public import M9StacksIntegration.RelativeDifferentialsSpatialComposition

/-! The actual étale-chart cotangent comparison and the actual
surjective field-point differential into the genuine chart cotangent. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalChartDifferential

open LagrangianGrassmannian MukaiConormalChartJets MukaiConormalDifferentialTransport
open MukaiConormalCotangentTransport

/-- The actual native associativity comparison in the inverse direction,
with its original pullback-congruence map retained. -/
theorem pullbackComp_assoc_inv {X Y Z W : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullbackCongr (Category.assoc a b c)).hom.app M ≫
        (Scheme.Modules.pullbackComp a (b ≫ c)).inv.app M ≫
          (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app M) =
      (Scheme.Modules.pullbackComp (a ≫ b) c).inv.app M ≫
        (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback c).obj M) := by
  have h := congrArg (fun α => α.app M) (Scheme.Modules.pseudofunctor_associativity a b c)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at h
  change (Scheme.Modules.pullbackComp a (b ≫ c)).inv.app M ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app M) ≫
        (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
          (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M =
    (Scheme.Modules.pullbackCongr (Category.assoc a b c)).inv.app M at h
  have h' := congrArg (fun q =>
    (Scheme.Modules.pullbackCongr (Category.assoc a b c)).hom.app M ≫ q ≫
      (Scheme.Modules.pullbackComp (a ≫ b) c).inv.app M ≫
        (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback c).obj M)) h
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Category.id_comp, Category.comp_id] using h'

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
variable (f : chart K ⟶ space K) (hf : f ≫ projection K = chartProjection K)

def nativeDifferential :
    (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials (projection K)) ⟶
      chartCotangent K :=
  Scheme.Hom.relativeDifferentialsMap f (projection K) (chartProjection K) (𝟙 _)
    (by simpa only [Category.comp_id] using hf)

omit [IsAlgClosed K] in
theorem integralDifferential_factor :
    (Scheme.Modules.pullbackComp f (LagrangianPlucker.integralPrimitivePlucker K)).inv.app
        (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≫
      (Scheme.Modules.pullback f).map (integralDifferential K) ≫ nativeDifferential K f hf =
      Scheme.Hom.relativeDifferentialsMap (f ≫ LagrangianPlucker.integralPrimitivePlucker K)
        (integralProjection 13) (chartProjection K)
        (specULiftZIsTerminal.from (Spec (.of K))) (specULiftZIsTerminal.hom_ext _ _) := by
  have h := RelativeDifferentialsSpatialComposition.relativeDifferentialsMap_spatial_comp
    f (LagrangianPlucker.integralPrimitivePlucker K) (integralProjection 13)
    (projection K) (chartProjection K) (specULiftZIsTerminal.from (Spec (.of K))) (𝟙 _)
    (integralSquare K) (by simpa only [Category.comp_id] using hf)
    (specULiftZIsTerminal.hom_ext _ _)
  simpa only [Category.id_comp, nativeDifferential, integralDifferential] using h

variable [Etale f]

instance nativeDifferential_isIso : IsIso (nativeDifferential K f hf) :=
  Scheme.Hom.isIso_relativeDifferentialsMap_of_etale f (projection K) (chartProjection K)
    (𝟙 _) (by simpa only [Category.comp_id] using hf)

def pointCotangentIso (z : Spec (.of K) ⟶ chart K) :
    (Scheme.Modules.pullback (z ≫ f)).obj (Scheme.Hom.relativeDifferentials (projection K)) ≅
      (Scheme.Modules.pullback z).obj (chartCotangent K) :=
  ((Scheme.Modules.pullbackComp z f).app (Scheme.Hom.relativeDifferentials (projection K))).symm ≪≫
    (Scheme.Modules.pullback z).mapIso (asIso (nativeDifferential K f hf))

def differential (z : Spec (.of K) ⟶ chart K) :
    MukaiConormalFieldDifferential.CotangentSource K (z ≫ f) →ₗ[K] PointCotangent K z :=
  (moduleSpecΓFunctor.map (pointCotangentIso K f hf z).hom).hom.comp
    (MukaiConormalFieldDifferential.differential K (z ≫ f))

theorem differential_surjective (z : Spec (.of K) ⟶ chart K) :
    Function.Surjective (differential K f hf z) :=
  (moduleSpecΓFunctor.mapIso (pointCotangentIso K f hf z)).toLinearEquiv.surjective.comp
    (MukaiConormalFieldDifferential.differential_surjective K (z ≫ f))

/-- Direct source-composition spelling of the genuine chart map. -/
def directDifferentialSheaf (z : Spec (.of K) ⟶ chart K) :
    (Scheme.Modules.pullback ((z ≫ f) ≫ LagrangianPlucker.integralPrimitivePlucker K)).obj
        (Scheme.Hom.relativeDifferentials (integralProjection 13)) ⟶
      (Scheme.Modules.pullback z).obj (chartCotangent K) :=
  (Scheme.Modules.pullbackCongr (Category.assoc z f
    (LagrangianPlucker.integralPrimitivePlucker K))).hom.app
      (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≫
    (Scheme.Modules.pullbackComp z (f ≫ LagrangianPlucker.integralPrimitivePlucker K)).inv.app
      (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≫
        (Scheme.Modules.pullback z).map
          (Scheme.Hom.relativeDifferentialsMap (f ≫ LagrangianPlucker.integralPrimitivePlucker K)
            (integralProjection 13) (chartProjection K)
            (specULiftZIsTerminal.from (Spec (.of K))) (specULiftZIsTerminal.hom_ext _ _))

omit [IsAlgClosed K] in
/-- The actual two-stage LG cotangent comparison is the actual direct
projective differential. This uses native pullback associativity. -/
theorem differential_eq_direct (z : Spec (.of K) ⟶ chart K) :
    differential K f hf z = (moduleSpecΓFunctor.map (directDifferentialSheaf K f z)).hom := by
  have hn := (Scheme.Modules.pullbackComp z f).inv.naturality (integralDifferential K)
  have ha := pullbackComp_assoc_inv z f (LagrangianPlucker.integralPrimitivePlucker K)
    (Scheme.Hom.relativeDifferentials (integralProjection 13))
  have hΩ :
      MukaiConormalFieldDifferential.differentialSheaf K (z ≫ f) ≫
        (pointCotangentIso K f hf z).hom = directDifferentialSheaf K f z := by
    have h' := congrArg (fun t => t ≫
      (Scheme.Modules.pullback z).map
        ((Scheme.Modules.pullback f).map (integralDifferential K)) ≫
          (Scheme.Modules.pullback z).map (nativeDifferential K f hf)) ha.symm
    have hpre : MukaiConormalFieldDifferential.differentialSheaf K (z ≫ f) ≫
        (pointCotangentIso K f hf z).hom =
      (Scheme.Modules.pullbackCongr (Category.assoc z f
        (LagrangianPlucker.integralPrimitivePlucker K))).hom.app
          (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≫
        (Scheme.Modules.pullbackComp z (f ≫ LagrangianPlucker.integralPrimitivePlucker K)).inv.app
          (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≫
            (Scheme.Modules.pullback z).map
              ((Scheme.Modules.pullbackComp f (LagrangianPlucker.integralPrimitivePlucker K)).inv.app
                (Scheme.Hom.relativeDifferentials (integralProjection 13))) ≫
              (Scheme.Modules.pullback z).map ((Scheme.Modules.pullback f).map (integralDifferential K)) ≫
                (Scheme.Modules.pullback z).map (nativeDifferential K f hf) := by
      simp only [MukaiConormalFieldDifferential.differentialSheaf, pointCotangentIso,
        Iso.trans_hom, Iso.symm_hom, Iso.app_inv, CategoryTheory.Functor.mapIso_hom,
        asIso_hom, Category.assoc]
      rw [← Category.assoc ((Scheme.Modules.pullback (z ≫ f)).map (integralDifferential K)), hn]
      simpa only [Category.assoc, Functor.comp_map] using h'
    calc
      _ = _ := hpre
      _ = directDifferentialSheaf K f z := by
        simp only [← CategoryTheory.Functor.map_comp, integralDifferential_factor,
          directDifferentialSheaf]

  change (moduleSpecΓFunctor.map (pointCotangentIso K f hf z).hom).hom.comp
    (moduleSpecΓFunctor.map (MukaiConormalFieldDifferential.differentialSheaf K (z ≫ f))).hom = _
  rw [← ModuleCat.hom_comp, ← CategoryTheory.Functor.map_comp, hΩ]


omit [CharZero K] [IsAlgClosed K] in
include f hf in
theorem target_finite_and_finrank (z : Spec (.of K) ⟶ chart K) :
    Module.Finite K (PointCotangent K z) ∧ finrank K (PointCotangent K z) = 6 := by
  obtain ⟨hM,hD⟩ := MukaiConormalFieldDifferential.target_finite_and_finrank K (z ≫ f)
  let : Module.Finite K (MukaiConormalFieldDifferential.CotangentTarget K (z ≫ f)) := hM
  let e := (moduleSpecΓFunctor.mapIso (pointCotangentIso K f hf z)).toLinearEquiv
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, e.finrank_eq.symm.trans hD⟩

end M9Native.MukaiConormalChartDifferential
