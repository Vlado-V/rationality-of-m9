module

public import M9StacksIntegration.GrassmannianFixedLineSheaf

/-! The actual native Grassmannian of rank-five quotients killing a
fixed nonzero vector. The factorization criterion holds on all test
schemes, and the universal quotient and the base field are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.GrassmannianFixedLine
open AlgebraicGeometry.Grassmannian
open LagrangianLinearSections LagrangianLinearSectionQuotientCharts

section NativeCoordinates
variable (K : Type u) [Field K] (r n : ℕ)

def pointClass {T : Scheme.{u}} (f : T ⟶ GrassmannianCharts.space K r n) : Points T r n :=
  (functorData r n).objEquiv T ((schemeRepresentableBy r n).homEquiv
    (f ≫ GrassmannianCharts.toIntegral K r n))

theorem pointClass_comp {S T : Scheme.{u}} (f : T ⟶ S)
    (g : S ⟶ GrassmannianCharts.space K r n) :
    pointClass K r n (f ≫ g) = pullbackPointsMap f r n (pointClass K r n g) := by
  have h := LagrangianGrassmannian.pointsEquiv_map f r n
    ((schemeRepresentableBy r n).homEquiv (g ≫ GrassmannianCharts.toIntegral K r n))
  rw [← (schemeRepresentableBy r n).homEquiv_comp] at h
  simpa only [pointClass, Category.assoc] using h

def classify {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (x : Points T r n) :
    T ⟶ GrassmannianCharts.space K r n :=
  pullback.lift p ((schemeRepresentableBy r n).homEquiv.symm
    (((functorData r n).objEquiv T).symm x)) (terminal.hom_ext _ _)

@[reassoc] theorem classify_projection {T : Scheme.{u}}
    (p : T ⟶ Spec (.of K)) (x : Points T r n) :
    classify K r n p x ≫ GrassmannianCharts.projection K r n = p :=
  pullback.lift_fst _ _ _

theorem classify_class {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (x : Points T r n) :
    pointClass K r n (classify K r n p x) = x := by
  simp only [pointClass, classify, GrassmannianCharts.toIntegral, pullback.lift_snd,
    Equiv.apply_symm_apply]

theorem hom_ext {T : Scheme.{u}} (f g : T ⟶ GrassmannianCharts.space K r n)
    (hb : f ≫ GrassmannianCharts.projection K r n = g ≫ GrassmannianCharts.projection K r n)
    (hc : pointClass K r n f = pointClass K r n g) : f = g := by
  apply pullback.hom_ext
  · exact hb
  · apply (schemeRepresentableBy r n).homEquiv.injective
    apply ((functorData r n).objEquiv T).injective
    exact hc
end NativeCoordinates

variable (K : Type u) [Field K] (v : Fin 14 → K) (hv : v ≠ 0)
abbrev source : Scheme.{u} := GrassmannianCharts.space K 8 13
abbrev sourceProjection : source K ⟶ Spec (.of K) := GrassmannianCharts.projection K 8 13

/-- The actual native rank-five quotient over the identity of Gr8,13. -/
def sourceQuotient : QuotientPresentation (source K) 8 13 :=
  Quotient.out (pointClass K 8 13 (𝟙 (source K)))

theorem sourceQuotient_class :
    (⟦sourceQuotient K⟧ : Points (source K) 8 13) = pointClass K 8 13 (𝟙 (source K)) :=
  Quotient.out_eq _

/-- The genuine classifying scheme map, with the prescribed line removed. -/
def map : source K ⟶ parameter K :=
  classify K 9 14 (sourceProjection K)
    (GrassmannianFixedLineSheaf.liftPoints K (sourceProjection K) v hv
      (pointClass K 8 13 (𝟙 (source K))))

@[reassoc] theorem map_projection : map K v hv ≫ parameterProjection K = sourceProjection K :=
  classify_projection _ _ _ _ _

theorem map_class :
    pointClass K 9 14 (map K v hv) =
      GrassmannianFixedLineSheaf.liftPoints K (sourceProjection K) v hv
        (pointClass K 8 13 (𝟙 (source K))) :=
  classify_class _ _ _ _ _

/-- The actual scheme map realizes the native quotient equivalence on every
scheme, with no reduced or affine restriction. -/
theorem pointClass_map {T : Scheme.{u}} (f : T ⟶ source K) :
    pointClass K 9 14 (f ≫ map K v hv) =
      GrassmannianFixedLineSheaf.liftPoints K (f ≫ sourceProjection K) v hv
        (pointClass K 8 13 f) := by
  rw [pointClass_comp, map_class, GrassmannianFixedLineSheaf.liftPoints_natural]
  have hf : pullbackPointsMap f 8 13 (pointClass K 8 13 (𝟙 (source K))) =
      pointClass K 8 13 f := by
    simpa only [Category.comp_id] using (pointClass_comp K 8 13 f (𝟙 (source K))).symm
  rw [hf]

/-- The original parameter quotient has exactly the native class of
its actual classifying morphism. -/
theorem parameter_class {T : Scheme.{u}} (q : T ⟶ parameter K) :
    (⟦pullbackPresentation q (parameterQuotient K)⟧ : Points T 9 14) =
      pointClass K 9 14 q :=
  pullback_parameter_class K q

/-- Literal annihilation of the original native coefficient column by the
original parameter quotient, with the exact field-scalar pullback. -/
def Annihilates {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (q : T ⟶ parameter K) : Prop :=
  LagrangianIncidenceFieldFrame.coefficientColumn T
    (fun j => p.appTop ((Scheme.ΓSpecIso (.of K)).inv (v j))) ≫
      (pullbackPresentation q (parameterQuotient K)).map = 0

theorem pointClass_annihilates_iff {T : Scheme.{u}} (p : T ⟶ Spec (.of K))
    (q : T ⟶ parameter K) :
    GrassmannianFixedLineSheaf.KillsColumnPoint K p v (pointClass K 9 14 q) ↔
      Annihilates K v p q := by
  rw [← parameter_class K q]
  rfl

/-- The actual pulled universal quotient kills the fixed original column. -/
theorem map_annihilates : Annihilates K v (sourceProjection K) (map K v hv) := by
  apply (pointClass_annihilates_iff K v (sourceProjection K) (map K v hv)).mp
  rw [map_class]
  exact GrassmannianFixedLineSheaf.liftPoints_kills K (sourceProjection K) v hv _

/-- A proved actual universal-quotient isomorphism and triangle, retaining
the original parameter quotient rather than a distinct chosen universal class. -/
theorem map_quotient_factor :
    ∃ e : (pullbackPresentation (map K v hv) (parameterQuotient K)).target ≅
        (sourceQuotient K).target,
      (pullbackPresentation (map K v hv) (parameterQuotient K)).map ≫ e.hom =
        (GrassmannianFixedLineSheaf.splitMap K (sourceProjection K) v hv).quotient ≫
          (sourceQuotient K).map := by
  have hc :
      (⟦pullbackPresentation (map K v hv) (parameterQuotient K)⟧ : Points (source K) 9 14) =
        ⟦GrassmannianSplitQuotient.lift
          (GrassmannianFixedLineSheaf.splitMap K (sourceProjection K) v hv) (sourceQuotient K)⟧ := by
    rw [parameter_class, map_class, ← sourceQuotient_class]
    rfl
  exact GrassmannianFieldKernels.isomorphic_of_class_eq hc

/-- The genuine classifying morphism is a scheme monomorphism, proved
from injectivity on the native quotient functor on every test scheme. -/
instance map_mono : Mono (map K v hv) := by
  constructor
  intro T f g h
  have hb : f ≫ sourceProjection K = g ≫ sourceProjection K := by
    simpa only [Category.assoc, map_projection] using
      congrArg (fun a : T ⟶ parameter K => a ≫ parameterProjection K) h
  apply hom_ext K 8 13 f g hb
  apply GrassmannianFixedLineSheaf.liftPoints_injective K (f ≫ sourceProjection K) v hv
  have hc := congrArg (fun a : T ⟶ parameter K => pointClass K 9 14 a) h
  rw [pointClass_map, pointClass_map, ← hb] at hc
  exact hc

/-- All-test lifting through the native map; nilpotents and the actual base
morphism are retained. No global quotient frame is needed. -/
theorem exists_lift {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (q : T ⟶ parameter K)
    (hq : q ≫ parameterProjection K = p) (hz : Annihilates K v p q) :
    ∃ f : T ⟶ source K, f ≫ sourceProjection K = p ∧ f ≫ map K v hv = q := by
  have hp := (pointClass_annihilates_iff K v p q).mpr hz
  obtain ⟨x, hx⟩ := (GrassmannianFixedLineSheaf.exists_liftPoints_iff K p v hv
    (pointClass K 9 14 q)).mpr hp
  refine ⟨classify K 8 13 p x, classify_projection K 8 13 p x, ?_⟩
  apply hom_ext K 9 14
  · simpa only [Category.assoc, map_projection, classify_projection] using hq.symm
  · rw [pointClass_map, classify_projection, classify_class]
    exact hx

theorem existsUnique_lift {T : Scheme.{u}} (p : T ⟶ Spec (.of K)) (q : T ⟶ parameter K)
    (hq : q ≫ parameterProjection K = p) (hz : Annihilates K v p q) :
    ∃! f : T ⟶ source K, f ≫ sourceProjection K = p ∧ f ≫ map K v hv = q := by
  obtain ⟨f, hf, hqf⟩ := exists_lift K v hv p q hq hz
  refine ⟨f, ⟨hf, hqf⟩, ?_⟩
  intro g hg
  exact (cancel_mono (map K v hv)).1 (hg.2.trans hqf.symm)

/-- Exact factorization through the fixed-line Grassmannian, on all test
schemes, equals the literal original coefficient-column equation. -/
theorem factorsThrough_iff_column_zero {T : Scheme.{u}} (q : T ⟶ parameter K) :
    (∃ f : T ⟶ source K, f ≫ map K v hv = q) ↔
      LagrangianIncidenceFieldFrame.coefficientColumn T
        (fun j => (q ≫ parameterProjection K).appTop
          ((Scheme.ΓSpecIso (.of K)).inv (v j))) ≫
        (pullbackPresentation q (parameterQuotient K)).map = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    apply (pointClass_annihilates_iff K v _ _).mp
    rw [Category.assoc, map_projection, pointClass_map]
    exact GrassmannianFixedLineSheaf.liftPoints_kills K (f ≫ sourceProjection K) v hv _
  · intro hz
    obtain ⟨f, _, hf⟩ := exists_lift K v hv (q ≫ parameterProjection K) q rfl hz
    exact ⟨f, hf⟩

end M9Native.GrassmannianFixedLine
