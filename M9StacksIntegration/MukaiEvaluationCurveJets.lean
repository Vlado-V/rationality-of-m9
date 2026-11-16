module

public import M9StacksIntegration.MukaiCurvePointLine
public import M9StacksIntegration.MukaiFreePullbackCoordinates
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative

/-!
# Actual determinant evaluation vanishes to first order along the curve

A vector in the kernel of the original primitive evaluation is a zero
global determinant section. On every genuine pulled determinant frame,
its literal fourteen-coordinate combination and its universal relative
differential both vanish. The final first jet uses the original pulled
cotangent sheaf, without replacing it by a chosen vector space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.MukaiEvaluationCurveJets

open MukaiPrimitiveCanonicalEvaluation MukaiCubicFreeSheaf MukaiConstantFreeBasis
open MukaiBundleDeterminant

variable (K : Type u) [Field K] [CharZero K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))

omit [CharZero K] in
theorem baseRingMap_eq_baseScalar :
    ExteriorEvaluation.baseRingMap K f = MukaiConstantFreeBasis.baseScalar (.of K) f := by
  have happ : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    have h : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op =
        𝟙 Γ(X, ⊤) := by
      change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) = _
      exact X.presheaf.map_id _
    rw [Scheme.Hom.appLE, h]
    exact Category.comp_id _
  unfold ExteriorEvaluation.baseRingMap MukaiConstantFreeBasis.baseScalar
  rw [happ]

theorem primitiveEvaluation_sum (ell : MukaiPrimitiveQuartic.Forms K) :
    primitiveEvaluation K f E b ell =
      ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
        primitiveEvaluation K f E b (formsBasis K j) := by
  conv_lhs => rw [← (formsBasis K).sum_repr ell]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_smul, formsBasis, Basis.dualBasis_repr]

def determinantSectionEvaluation :
    MukaiPrimitiveQuartic.Forms K →ₛₗ[ExteriorEvaluation.baseRingMap K f]
      Γ(Scheme.Modules.exteriorPower E (3 : ℤ), ⊤) :=
  (ExteriorEvaluation.h0SectionsSemilinear K f (Scheme.Modules.exteriorPower E (3 : ℤ))).comp
    (primitiveEvaluation K f E b)

theorem determinantSections_sum_zero (ell : MukaiPrimitiveQuartic.Forms K)
    (hell : primitiveEvaluation K f E b ell = 0) :
    (∑ j : Fin 14, MukaiConstantFreeBasis.baseScalar (.of K) f
      (ell (LagrangianPluckerLinear.primitiveBasis14 K j)) • determinantSections K f E b j) = 0 := by
  have h := congrArg (determinantSectionEvaluation K f E b) ((formsBasis K).sum_repr ell)
  simp only [map_sum, map_smulₛₗ, formsBasis, Basis.dualBasis_repr] at h
  have hc (a : K) : ExteriorEvaluation.baseRingMap K f a =
      MukaiConstantFreeBasis.baseScalar (.of K) f a :=
    congrArg (fun r => r a) (baseRingMap_eq_baseScalar K f)
  simp only [hc] at h
  change (∑ j : Fin 14, MukaiConstantFreeBasis.baseScalar (.of K) f
    (ell (LagrangianPluckerLinear.primitiveBasis14 K j)) • determinantSections K f E b j) =
      determinantSectionEvaluation K f E b ell at h
  refine h.trans ?_
  change (ExteriorEvaluation.h0SectionsSemilinear K f
    (Scheme.Modules.exteriorPower E (3 : ℤ))) (primitiveEvaluation K f E b ell) = 0
  rw [hell, map_zero]

def framedSections (p : Y ⟶ X)
    (e : (Scheme.Modules.pullback p).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
      MukaiBundle.structureModule Y) : Fin 14 → Γ(Y, ⊤) :=
  fun j => e.hom.app ⊤ (pullbackGlobalSections p
    (Scheme.Modules.exteriorPower E (3 : ℤ)) (determinantSections K f E b j))

theorem framedSections_sum_zero (p : Y ⟶ X)
    (e : (Scheme.Modules.pullback p).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
      MukaiBundle.structureModule Y)
    (ell : MukaiPrimitiveQuartic.Forms K) (hell : primitiveEvaluation K f E b ell = 0) :
    (∑ j : Fin 14, MukaiConstantFreeBasis.baseScalar (.of K) (p ≫ f)
      (ell (LagrangianPluckerLinear.primitiveBasis14 K j)) * framedSections K f E b p e j) = 0 := by
  have h := congrArg (fun s => e.hom.app ⊤
    (pullbackGlobalSections p (Scheme.Modules.exteriorPower E (3 : ℤ)) s))
      (determinantSections_sum_zero K f E b ell hell)
  simpa only [map_sum, map_zero, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul,
    ← MukaiFreePullbackCoordinates.baseScalar_comp (.of K) f p,
    framedSections, smul_eq_mul] using h

omit [CharZero K] in
theorem differential_baseScalar (q : Y ⟶ Spec (.of K)) (a : K) :
    (Scheme.Hom.universalRelativeDerivation q).d (MukaiConstantFreeBasis.baseScalar (.of K) q a) = 0 := by
  exact Scheme.Hom.universalRelativeDerivation_d_app_eq_zero q ⊤
    ((Scheme.ΓSpecIso (.of K)).inv a)

theorem framedSections_differential_sum_zero (p : Y ⟶ X)
    (e : (Scheme.Modules.pullback p).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
      MukaiBundle.structureModule Y)
    (ell : MukaiPrimitiveQuartic.Forms K) (hell : primitiveEvaluation K f E b ell = 0) :
    (∑ j : Fin 14, MukaiConstantFreeBasis.baseScalar (.of K) (p ≫ f)
      (ell (LagrangianPluckerLinear.primitiveBasis14 K j)) •
      (Scheme.Hom.universalRelativeDerivation (p ≫ f)).d (framedSections K f E b p e j)) = 0 := by
  have h := congrArg (Scheme.Hom.universalRelativeDerivation (p ≫ f)).d
    (framedSections_sum_zero K f E b p e ell hell)
  simpa only [map_sum, map_zero, PresheafOfModulesOfCommRing.Derivation.d_mul,
    differential_baseScalar K (p ≫ f), smul_zero, add_zero] using h

omit [CharZero K] in
theorem fieldPoint_baseScalar (q : Y ⟶ Spec (.of K))
    (z : Spec (.of K) ⟶ Y) (hz : z ≫ q = 𝟙 _) (a : K) :
    z.appTop (MukaiConstantFreeBasis.baseScalar (.of K) q a) = (Scheme.ΓSpecIso (.of K)).inv a := by
  calc
    _ = MukaiConstantFreeBasis.baseScalar (.of K) (z ≫ q) a :=
      (MukaiFreePullbackCoordinates.baseScalar_comp (.of K) q z a).symm
    _ = _ := by rw [hz, MukaiFreePullbackCoordinates.baseScalar_id]

abbrev PointCotangent (q : Y ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ Y) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback z).obj (Scheme.Hom.relativeDifferentials q))

def curveDerivative (q : Y ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ Y)
    (s : Γ(Y, ⊤)) : PointCotangent K q z :=
  pullbackGlobalSections z (Scheme.Hom.relativeDifferentials q)
    ((Scheme.Hom.universalRelativeDerivation q).d s)

def curveJet (q : Y ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ Y)
    (v : Fin 14 → Γ(Y, ⊤)) :
    MukaiPrimitiveQuartic.Forms K →ₗ[K] K × PointCotangent K q z :=
  (show MukaiPrimitiveQuartic.Forms K →ₗ[K] K from
    { toFun := fun ell => ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) *
        (Scheme.ΓSpecIso (.of K)).hom (z.appTop (v j))
      map_add' := by intros; simp only [LinearMap.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by intros; simp only [LinearMap.smul_apply, RingHom.id_apply,
        smul_eq_mul, mul_assoc, Finset.mul_sum] }).prod
    (show MukaiPrimitiveQuartic.Forms K →ₗ[K] PointCotangent K q z from
      { toFun := fun ell => ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
          curveDerivative K q z (v j)
        map_add' := by intros; simp only [LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by intros; simp only [LinearMap.smul_apply, RingHom.id_apply,
          smul_eq_mul, mul_smul, Finset.smul_sum] })

theorem curveJet_eq_zero (p : Y ⟶ X)
    (e : (Scheme.Modules.pullback p).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
      MukaiBundle.structureModule Y)
    (z : Spec (.of K) ⟶ Y) (hz : z ≫ (p ≫ f) = 𝟙 _)
    (ell : MukaiPrimitiveQuartic.Forms K) (hell : primitiveEvaluation K f E b ell = 0) :
    curveJet K (p ≫ f) z (framedSections K f E b p e) ell = 0 := by
  apply Prod.ext
  · change (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) *
      (Scheme.ΓSpecIso (.of K)).hom
        (z.appTop (framedSections K f E b p e j))) = 0
    have h := congrArg (fun a => (Scheme.ΓSpecIso (.of K)).hom (z.appTop a))
      (framedSections_sum_zero K f E b p e ell hell)
    simpa only [map_sum, map_mul, map_zero, fieldPoint_baseScalar K (p ≫ f) z hz,
      Iso.inv_hom_id_apply] using h
  · change (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
      curveDerivative K (p ≫ f) z (framedSections K f E b p e j)) = 0
    have h := congrArg (pullbackGlobalSections z (Scheme.Hom.relativeDifferentials (p ≫ f)))
      (framedSections_differential_sum_zero K f E b p e ell hell)
    rw [map_sum, map_zero] at h
    have hs (j : Fin 14) :
        pullbackGlobalSections z (Scheme.Hom.relativeDifferentials (p ≫ f))
          (MukaiConstantFreeBasis.baseScalar (.of K) (p ≫ f)
            (ell (LagrangianPluckerLinear.primitiveBasis14 K j)) •
            (Scheme.Hom.universalRelativeDerivation (p ≫ f)).d
              (framedSections K f E b p e j)) =
        ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
          curveDerivative K (p ≫ f) z (framedSections K f E b p e j) := by
      change _ = (Scheme.ΓSpecIso (.of K)).inv.hom
        (ell (LagrangianPluckerLinear.primitiveBasis14 K j)) •
        pullbackGlobalSections z (Scheme.Hom.relativeDifferentials (p ≫ f))
          ((Scheme.Hom.universalRelativeDerivation (p ≫ f)).d (framedSections K f E b p e j))
      rw [SectionsEqualizer.pullbackGlobalSections_smul,
        fieldPoint_baseScalar K (p ≫ f) z hz]
    simpa only [hs] using h

theorem ker_primitiveEvaluation_le_ker_curveJet (p : Y ⟶ X)
    (e : (Scheme.Modules.pullback p).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
      MukaiBundle.structureModule Y)
    (z : Spec (.of K) ⟶ Y) (hz : z ≫ (p ≫ f) = 𝟙 _) :
    LinearMap.ker (primitiveEvaluation K f E b) ≤
      LinearMap.ker (curveJet K (p ≫ f) z (framedSections K f E b p e)) := by
  intro ell hell
  exact curveJet_eq_zero K f E b p e z hz ell hell

end M9Native.MukaiEvaluationCurveJets
