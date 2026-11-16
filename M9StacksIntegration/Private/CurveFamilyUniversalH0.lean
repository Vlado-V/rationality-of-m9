module

public import M9StacksIntegration.SchematicCurveFibreConstants
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# Selected actual global-function descent proofs for native curve families

Private isolated selection from the pinned AxiomMath/Stacks proof source
`Quot/CurvesH01Inputs.lean`, commit c496df0d9beea9deaeabcea8492605f9a0a2313b.
Original source SHA256: fcf3f174ed08c6fb31edabcb3e55139da71d60dda25c0ddc1292682928922465.

Only actual identity-chart comparison, descent of compatible functions,
field-fibre relocalization and the universal-H0 wrapper are selected.
Namespace is changed to M9Native.CurveFamilyUniversalH0 to avoid collision
with later native imports; the native checkout is unchanged. Visibility
is public within this isolated module for explicit audit. The final
wrapper applies the genuinely proved native0E6B theorem rather than
assuming its conclusion or a universal-H0 premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry AlgebraicGeometry.Space
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.CurveFamilyUniversalH0

local instance (priority := high) hasPullbacks_presheaf
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) := (hasPullbacks_presheaf (B := B) (S := S) (hS := hS)).has_limit _

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Actual Gamma transport along an actual space isomorphism. Selected
from pinned Spaces/AffineSpaceGlobalFunctions.lean, SHA256 05dcd62af235f0ec0f80910861d71960a8155123b350f86ad60c776a9625add6.
No broader affine-representability import is needed for these ring maps. -/
def globalFunctionsMapEquiv {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) :
    globalFunctions' B S hS Y.obj ≃+* globalFunctions' B S hS X.obj where
  toFun := globalFunctionsMap B S hS e.hom
  invFun := globalFunctionsMap B S hS e.inv
  left_inv s := by
    rw [← RingHom.comp_apply, ← globalFunctionsMap_comp, e.inv_hom_id,
      globalFunctionsMap_id, RingHom.id_apply]
  right_inv s := by
    rw [← RingHom.comp_apply, ← globalFunctionsMap_comp, e.hom_inv_id,
      globalFunctionsMap_id, RingHom.id_apply]
  map_mul' := (globalFunctionsMap B S hS e.hom).map_mul
  map_add' := (globalFunctionsMap B S hS e.hom).map_add


/-! ### Global functions across an invertible structure map -/

/-- Over the algebraic space of a scheme `U₀`, pullback of global functions along `f` is the
comparison `AlgebraicGeometry.Space.terminalChartPullback` at the identity chart of `U₀`, read
through `Γ(U₀, 𝒪) = H⁰(U₀, 𝒪)`. -/
theorem globalFunctionsMap_eq_terminalChartPullback {Z : AlgebraicSpaces B S hS}
    (U₀ : BigFppfOver B S hS) (f : Z ⟶ (schemeSpaceFunctor B S hS).obj U₀)
    (hV : IsIso ((comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)).1.hom)
    (s : globalFunctions' B S hS (yoneda.obj U₀)) :
    globalFunctionsMap B S hS f s =
      terminalChartPullback B S hS f (idEtaleChart B S hS U₀) hV
        (globalFunctionsYonedaRingEquiv B S hS U₀ s) := by
  refine Subtype.ext (funext fun U => ?_)
  let j := terminalChartIndex B S hS f (idEtaleChart B S hS U₀) hV U.unop
  have hψ : yoneda.map (chartBaseChangeMap B S hS f (idEtaleChart B S hS U₀) j) ≫
      ((SmallEtale.inclusion B S hS (yoneda.obj U₀)).obj (idEtaleChart B S hS U₀)).hom =
        ((SmallEtale.inclusion B S hS Z.obj).obj U.unop).hom ≫ f.hom := by
    refine (congrArg (· ≫ ((SmallEtale.inclusion B S hS (yoneda.obj U₀)).obj
      (idEtaleChart B S hS U₀)).hom) (yoneda_map_chartBaseChangeMap B S hS f _ j)).trans ?_
    let cV := (comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)
    change ((j.hom.unop.hom.left ≫ (spacesBaseChange B S hS f).projection.app cV) ≫
      cV.1.hom).hom = _
    rw [Category.assoc, ((spacesBaseChange B S hS f).isPullback cV).w, ← Category.assoc,
      Over.w j.hom.unop.hom]
    rfl
  exact globalFunctionsMap_val_chart B S hS f (idEtaleChart B S hS U₀) U.unop _ hψ s

/-- **Over a scheme, an invertible structure map makes pullback of global functions bijective.**
If `f : Z ⟶ U₀` is a morphism to the algebraic space of a scheme with `𝒪_{U₀} ≅ f_*𝒪_Z`, then
`Γ(U₀, 𝒪) ⟶ Γ(Z, 𝒪)` is bijective. -/
theorem bijective_globalFunctionsMap_of_isIso_structureSharp {Z : AlgebraicSpaces B S hS}
    (U₀ : BigFppfOver B S hS) (f : Z ⟶ (schemeSpaceFunctor B S hS).obj U₀)
    (hf : IsIso (structureSharp B S hS f)) :
    Function.Bijective (globalFunctionsMap B S hS f) := by
  have hV : IsIso ((comparisonFunctor B S hS ((schemeSpaceFunctor B S hS).obj U₀)).obj
      (idEtaleChart B S hS U₀)).1.hom := by
    change IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj U₀))
    infer_instance
  have heq : ⇑(globalFunctionsMap B S hS f) =
      ⇑(terminalChartPullback B S hS f (idEtaleChart B S hS U₀) hV) ∘
        ⇑(globalFunctionsYonedaRingEquiv B S hS U₀) :=
    funext (globalFunctionsMap_eq_terminalChartPullback B S hS U₀ f hV)
  rw [heq]
  exact (bijective_terminalChartPullback B S hS f _ hV hf).comp
    (globalFunctionsYonedaRingEquiv B S hS U₀).bijective

/-! ### Global functions along base changes to schemes -/

section Gluing

variable {B S hS}

/-- **Gluing global functions along all scheme charts.** If, for every morphism `t` from a
representable presheaf to `Y`, precomposition of compatible functions on all scheme charts along
the base change `Z ×_Y T ⟶ T` of `π : Z ⟶ Y` is bijective, then so is precomposition along `π`:
a family on the charts of `Z` descends chart by chart, each chart `t` of `Y` giving the unique
function on `T` whose pullback to `Z ×_Y T` is the restriction of the family. -/
theorem bijective_chartFunctionsMap_of_forall {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : Z ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y),
      Function.Bijective (chartFunctionsMap B S hS (pullback.snd π t))) :
    Function.Bijective (chartFunctionsMap B S hS π) := by
  have key (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) (s : chartFunctions B S hS Y) :
      chartFunctionsMap B S hS (pullback.snd π t) (chartFunctionsMap B S hS t s) =
        chartFunctionsMap B S hS (pullback.fst π t) (chartFunctionsMap B S hS π s) :=
    (congrArg (fun m => chartFunctionsMap B S hS m s) (pullback.condition (f := π) (g := t))).symm
  refine ⟨fun s₁ s₂ he => Subtype.ext (funext fun j => ?_), fun σ => ?_⟩
  · have ht : chartFunctionsMap B S hS j.unop.hom s₁ = chartFunctionsMap B S hS j.unop.hom s₂ :=
      (h j.unop.left j.unop.hom).1 (by rw [key, key, he])
    exact congrArg (fun r : chartFunctions B S hS (yoneda.obj j.unop.left) =>
      r.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj j.unop.left))))) ht
  · let e (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) := Equiv.ofBijective _ (h T t)
    let r (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) : chartFunctions B S hS (yoneda.obj T) :=
      (e T t).symm (chartFunctionsMap B S hS (pullback.fst π t) σ)
    have hr (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y) :
        chartFunctionsMap B S hS (pullback.snd π t) (r T t) =
          chartFunctionsMap B S hS (pullback.fst π t) σ :=
      (e T t).apply_symm_apply _
    -- restriction of `r T t` along a morphism of charts is `r T' t'`
    have hres {T T' : BigFppfOver B S hS} (t : yoneda.obj T ⟶ Y) (ml : T' ⟶ T) :
        chartFunctionsMap B S hS (yoneda.map ml) (r T t) = r T' (yoneda.map ml ≫ t) := by
      apply (h T' (yoneda.map ml ≫ t)).1
      let k : pullback π (yoneda.map ml ≫ t) ⟶ pullback π t :=
        pullback.lift (pullback.fst π _) (pullback.snd π _ ≫ yoneda.map ml)
          (by rw [pullback.condition, Category.assoc])
      have hks : pullback.snd π (yoneda.map ml ≫ t) ≫ yoneda.map ml = k ≫ pullback.snd π t :=
        (pullback.lift_snd _ _ _).symm
      have hkf : k ≫ pullback.fst π t = pullback.fst π (yoneda.map ml ≫ t) :=
        pullback.lift_fst _ _ _
      rw [hr]
      change chartFunctionsMap B S hS (pullback.snd π (yoneda.map ml ≫ t) ≫ yoneda.map ml)
        (r T t) = _
      rw [hks]
      change chartFunctionsMap B S hS k (chartFunctionsMap B S hS (pullback.snd π t) (r T t)) = _
      rw [hr]
      change chartFunctionsMap B S hS (k ≫ pullback.fst π t) σ = _
      rw [hkf]
    let s : chartFunctions B S hS Y := ⟨fun j =>
      (r j.unop.left j.unop.hom).val (op (CostructuredArrow.mk (𝟙 (yoneda.obj j.unop.left)))),
      fun {j j'} m => by
        have hw : yoneda.map m.unop.left ≫ j.unop.hom = j'.unop.hom := CostructuredArrow.w m.unop
        have h1 := congrArg (fun x : chartFunctions B S hS (yoneda.obj j'.unop.left) =>
          x.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj j'.unop.left)))))
          (hres j.unop.hom m.unop.left)
        have h2 := (r j.unop.left j.unop.hom).property
          (CostructuredArrow.homMk m.unop.left (by simp) :
            CostructuredArrow.mk (yoneda.map m.unop.left) ⟶
              CostructuredArrow.mk (𝟙 (yoneda.obj j.unop.left))).op
        refine h2.trans (h1.trans ?_)
        rw [hw]⟩
    refine ⟨s, Subtype.ext (funext fun c => ?_)⟩
    let W := c.unop.left
    let w := c.unop.hom
    let σw : yoneda.obj W ⟶ pullback π (w ≫ π) := pullback.lift w (𝟙 _) (by simp)
    have h1 : chartFunctionsMap B S hS σw
        (chartFunctionsMap B S hS (pullback.snd π (w ≫ π)) (r W (w ≫ π))) = r W (w ≫ π) := by
      change chartFunctionsMap B S hS (σw ≫ pullback.snd π (w ≫ π)) (r W (w ≫ π)) = _
      rw [pullback.lift_snd]
      rfl
    rw [hr] at h1
    change chartFunctionsMap B S hS (σw ≫ pullback.fst π (w ≫ π)) σ = _ at h1
    rw [pullback.lift_fst] at h1
    exact (congrArg (fun x : chartFunctions B S hS (yoneda.obj W) =>
      x.val (op (CostructuredArrow.mk (𝟙 (yoneda.obj W))))) h1).symm

/-- Pullback of global functions is bijective exactly when precomposition of compatible functions
on all scheme charts is. -/
theorem bijective_globalFunctionsMap_iff {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) :
    Function.Bijective (globalFunctionsMap B S hS f) ↔
      Function.Bijective (chartFunctionsMap B S hS f.hom) := by
  have h : ⇑(globalFunctionsMap B S hS f) = ⇑(globalFunctionsChartEquiv B S hS V).val.symm ∘
      ⇑(chartFunctionsMap B S hS f.hom) ∘ ⇑(globalFunctionsChartEquiv B S hS U).val := rfl
  rw [h, Function.Bijective.of_comp_iff' (globalFunctionsChartEquiv B S hS V).val.symm.bijective,
    Function.Bijective.of_comp_iff _ (globalFunctionsChartEquiv B S hS U).val.bijective]

/-- **Pullback of global functions along `π : Z ⟶ Y` is bijective as soon as it is so along every
base change `Z ×_Y T ⟶ T` of `π` to a scheme `T`.** -/
theorem bijective_globalFunctionsMap_of_forall_schemeSpace {Z Y : AlgebraicSpaces B S hS}
    (π : Z ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (t : schemeSpace T ⟶ Y),
      Function.Bijective (globalFunctionsMap B S hS
        (ObjectProperty.homMk (pullback.snd π.hom t.hom) :
          AlgebraicSpaces.fiberProduct B S hS π t ⟶ schemeSpace T))) :
    Function.Bijective (globalFunctionsMap B S hS π) := by
  rw [bijective_globalFunctionsMap_iff]
  exact bijective_chartFunctionsMap_of_forall π.hom fun T t =>
    (bijective_globalFunctionsMap_iff _).1 (h T (ObjectProperty.homMk t))

end Gluing

end Space

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre over a field-valued point, formed over the field -/

/-- Identifying the field `k` of a field-valued point with the global functions of `Spec k` in the
site of the base is a bijective ring map. -/
private theorem bijective_yonedaRingEquiv_symm_comp_ΓSpecIso_inv
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS Y) :
    Function.Bijective
      ((globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y)).symm.toRingHom.comp
        (Scheme.ΓSpecIso (.of p.carrier)).inv.hom) :=
  (globalFunctionsYonedaRingEquiv B S hS _).symm.bijective.comp
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)

section FieldFibre

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)

/-- The morphism `Spec k ⟶ S` of the site underlying a field-valued point. -/
abbrev fieldPointBaseSiteHom : B.obj p.contained ⟶ B.obj hS := (p.siteObject B S hS Y).hom

/-- The unique morphism from the fibre of `f` over the section of a field-valued point to the
terminal presheaf over the field. -/
def fibreOfSectionToTerminal :
    OverShriek.fibreOfSection (fieldPointBaseSiteHom B S hS p) f (yonedaEquiv.symm p.value) ⟶
      yoneda.obj (Over.mk (𝟙 (B.obj p.contained))) where
  app W := ↾fun _ => Over.homMk W.unop.hom (Category.comp_id _)
  naturality _ _ _ := by
    ext _
    exact Over.OverMorphism.ext (Over.w _).symm

/-- The fibre of `f` over the section of a field-valued point, as a subpresheaf, is the fibre
product defining `AlgebraicGeometry.Space.restrictedFibre`. -/
theorem isPullback_fibreOfSection :
    IsPullback (OverShriek.fibreOfSectionι (fieldPointBaseSiteHom B S hS p) f (yonedaEquiv.symm p.value))
      (fibreOfSectionToTerminal B S hS f p)
      ((OverShriek.relocalizeRestrict (fieldPointBaseSiteHom B S hS p)).map f)
      (restrictedSection B S hS Y p.contained (fieldPointBaseSiteHom B S hS p) p.value) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact x.2.trans rfl
  · rintro x x' ⟨h1, -⟩
    exact Subtype.ext h1
  · intro x t hxt
    obtain rfl : t = Over.homMk (unop W).hom (Category.comp_id _) :=
      Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w t))
    exact ⟨⟨x, hxt.trans rfl⟩, rfl, rfl⟩

variable (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

include hX hY in
/-- **The global functions of the fibre over a field-valued point, formed over the field, are the
global functions of the fibre product.** For `f : X ⟶ Y` and a field-valued point `p` of `Y`
with field `k`, the base ring map `k ⟶ H⁰(X_k, 𝒪)` of the fibre of `f` over `p` formed over
`Spec k` is bijective exactly when pullback of global functions along `X ×_Y Spec k ⟶ Spec k`
is. The fibre is the subpresheaf `AlgebraicGeometry.OverShriek.fibreOfSection`, whose
relocalization to the site of the base is `X ×_Y Spec k`, and relocalizing does not change global
functions (`AlgebraicGeometry.Space.globalFunctionsRelocalizeEquiv`). -/
theorem bijective_algebraMap_fibreOverFieldValuedPoint_iff :
    Function.Bijective (algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier))
      p.contained (fibreOverFieldValuedPoint B S hS f p))) ↔
    Function.Bijective (globalFunctionsMap B S hS
      (ObjectProperty.homMk (pullback.snd f (yonedaEquiv.symm p.value)) :
        (⟨pullback f (yonedaEquiv.symm p.value), isAlgebraicSpace_pullback B S hS f _ hX
          (isAlgebraicSpace_yoneda B S hS _) hY⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (p.siteObject B S hS Y))) := by
  set a := fieldPointBaseSiteHom B S hS p
  set β : yoneda.obj (Over.mk a) ⟶ Y := yonedaEquiv.symm p.value
  let fib := OverShriek.fibreOfSection a f β
  let e1 : fib ≅ fibreOverFieldValuedPoint B S hS f p :=
    (isPullback_fibreOfSection B S hS f p).isoPullback
  have hrf := isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p
  have hfib : IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained fib :=
    isAlgebraicSpace_of_iso B _ p.contained e1.symm hrf
  have hpbP := OverShriek.isPullback_relocalizeFibreOfSectionMap a f β
  have hP : IsAlgebraicSpace B S hS (pullback f β) :=
    isAlgebraicSpace_pullback B S hS f β hX (isAlgebraicSpace_yoneda B S hS _) hY
  have hΛ : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor a).obj fib) :=
    isAlgebraicSpace_of_iso B S hS hpbP.isoPullback.symm hP
  let P' : AlgebraicSpaces B S hS := ⟨pullback f β, hP⟩
  let Λ' : AlgebraicSpaces B S hS := ⟨_, hΛ⟩
  let I3 : Λ' ≅ P' := (ObjectProperty.fullyFaithfulι _).preimageIso hpbP.isoPullback
  let RF : AlgebraicSpaces B (Spec (.of p.carrier)) p.contained := ⟨_, hrf⟩
  let FB : AlgebraicSpaces B (Spec (.of p.carrier)) p.contained := ⟨fib, hfib⟩
  let I1 : RF ≅ FB := (ObjectProperty.fullyFaithfulι _).preimageIso e1.symm
  let rTY : Λ' ⟶ schemeSpace (p.siteObject B S hS Y) :=
    ObjectProperty.homMk (OverShriek.relocalizeToYoneda a fib)
  let snd : P' ⟶ schemeSpace (p.siteObject B S hS Y) := ObjectProperty.homMk (pullback.snd f β)
  let ι : p.carrier → globalFunctions' B S hS (yoneda.obj (p.siteObject B S hS Y)) := fun c =>
    (globalFunctionsYonedaRingEquiv B S hS (p.siteObject B S hS Y)).symm
      ((Scheme.ΓSpecIso (.of p.carrier)).inv c)
  have hι : Function.Bijective ι := bijective_yonedaRingEquiv_symm_comp_ΓSpecIso_inv B S hS p
  have hsnd : I3.hom ≫ snd = rTY :=
    ObjectProperty.hom_ext _ hpbP.isoPullback_hom_snd
  have key (c : p.carrier) :
      globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS a fib
          (globalFunctionsMap B S hS rTY (ι c)) =
        algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier)) p.contained fib) c := by
    refine Subtype.ext (funext fun V => ?_)
    rw [globalFunctionsRelocalizeEquiv_apply]
    let ψ := relocalizeOverHom B (Spec (.of p.carrier)) S p.contained hS a
      ((SmallEtale.toOver B (Spec (.of p.carrier)) p.contained fib).obj V.unop)
    have hψ : yoneda.map ψ ≫ ((SmallEtale.inclusion B S hS (yoneda.obj (p.siteObject B S hS Y))).obj
        (idEtaleChart B S hS (p.siteObject B S hS Y))).hom =
        ((SmallEtale.inclusion B S hS Λ'.obj).obj
          ((SmallEtale.relocalizeEquivalence B (Spec (.of p.carrier)) S p.contained hS a
            fib).functor.obj V.unop)).hom ≫ rTY.hom := by
      ext W x
      exact Over.OverMorphism.ext rfl
    refine (globalFunctionsMap_val_chart B S hS rTY (idEtaleChart B S hS _)
      ((SmallEtale.relocalizeEquivalence B (Spec (.of p.carrier)) S p.contained hS a
        fib).functor.obj V.unop) ψ hψ (ι c)).trans ?_
    have hc : (ι c).val (op (idEtaleChart B S hS (p.siteObject B S hS Y))) =
        (Scheme.ΓSpecIso (.of p.carrier)).inv c :=
      (globalFunctionsYonedaRingEquiv_apply B S hS _ (ι c)).symm.trans
        ((globalFunctionsYonedaRingEquiv B S hS _).apply_symm_apply _)
    exact (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom hc).trans rfl
  have hcomp : ⇑(algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier)) p.contained
      (fibreOverFieldValuedPoint B S hS f p))) =
      ⇑(globalFunctionsMapEquiv B _ p.contained I1) ∘
        ⇑(globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS a fib) ∘
          ⇑(globalFunctionsMapEquiv B S hS I3) ∘ ⇑(globalFunctionsMap B S hS snd) ∘ ι := by
    funext c
    change _ = globalFunctionsMap B _ p.contained I1.hom
      (globalFunctionsRelocalizeEquiv B (Spec (.of p.carrier)) S p.contained hS a fib
        (globalFunctionsMap B S hS I3.hom (globalFunctionsMap B S hS snd (ι c))))
    have h3 : globalFunctionsMap B S hS I3.hom (globalFunctionsMap B S hS snd (ι c)) =
        globalFunctionsMap B S hS rTY (ι c) := by
      rw [← hsnd, globalFunctionsMap_comp]
      rfl
    rw [h3, key, globalFunctionsMap_algebraMap]
  rw [hcomp, Function.Bijective.of_comp_iff' (globalFunctionsMapEquiv B _ p.contained I1).bijective,
    Function.Bijective.of_comp_iff'
      (globalFunctionsRelocalizeEquiv B _ S p.contained hS a fib).bijective,
    Function.Bijective.of_comp_iff' (globalFunctionsMapEquiv B S hS I3).bijective]
  exact Function.Bijective.of_comp_iff (globalFunctionsMap B S hS snd) hι

include hX hY in
/-- One direction of `AlgebraicGeometry.Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff`:
bijectivity of pullback of global functions along `X ×_Y Spec k ⟶ Spec k` gives
`k = H⁰(X_k, 𝒪)` for the fibre formed over `Spec k`. -/
theorem bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective
    (h : Function.Bijective (globalFunctionsMap B S hS
      (ObjectProperty.homMk (pullback.snd f (yonedaEquiv.symm p.value)) :
        (⟨pullback f (yonedaEquiv.symm p.value), isAlgebraicSpace_pullback B S hS f _ hX
          (isAlgebraicSpace_yoneda B S hS _) hY⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (p.siteObject B S hS Y)))) :
    Function.Bijective (algebraMap p.carrier (globalFunctions B (Spec (.of p.carrier))
      p.contained (fibreOverFieldValuedPoint B S hS f p))) :=
  (bijective_algebraMap_fibreOverFieldValuedPoint_iff B S hS f p hX hY).2 h

end FieldFibre

/-! ### The dimension of `H⁰` of the fibres over fields -/


end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

theorem hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp {X : CurveFamily B hZ}
    (h : ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ schemeSpace X.base),
      IsIso (AlgebraicGeometry.Space.structureSharp B integerBase hZ (pullback.snd X.toBase g))) :
    HasUniversallyBijectiveGlobalFunctions B hZ X := by
  intro Y' g
  refine M9Native.CurveFamilyUniversalH0.Space.bijective_globalFunctionsMap_of_forall_schemeSpace _ fun T t => ?_
  have hb := M9Native.CurveFamilyUniversalH0.Space.bijective_globalFunctionsMap_of_isIso_structureSharp B integerBase hZ T
    (pullback.snd X.toBase (t ≫ g)) (h _ (t ≫ g))
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    (ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g ⟶ Y') t).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase g)
  have he := IsPullback.isoIsPullback_hom_snd _ _ sq (IsPullback.of_hasPullback X.toBase (t ≫ g))
  rw [← he, AlgebraicGeometry.Space.globalFunctionsMap_comp, RingHom.coe_comp]
  exact (M9Native.CurveFamilyUniversalH0.Space.globalFunctionsMapEquiv B integerBase hZ _).bijective.comp hb

/-- Genuine native0E6B and the proved relocalization comparison turn
actual field-fibre constants into universal H0 for the same curve family.
No H0, direct-image or moduli-membership conclusion is a premise. -/
theorem hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
    (X : CurveFamily B hZ)
    (hX : ∀ p : AlgebraicGeometry.Space.FieldValuedPoint B integerBase hZ
        (schemeSpace X.base).obj,
      Function.Bijective (AlgebraicGeometry.Space.globalFunctionsMap B integerBase hZ
        (ObjectProperty.homMk
          (pullback.snd X.toBase.hom (schemeSpaceMap p.value).hom) :
          AlgebraicSpaces.fiberProduct B integerBase hZ
            X.toBase (schemeSpaceMap p.value) ⟶ schemeSpace p.siteObject))) :
    HasUniversallyBijectiveGlobalFunctions B hZ X := by
  apply hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp
  intro Y' g
  exact (AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre
    B integerBase hZ X.toBase X.proper X.flat X.finitePresentation
    (fun p => Space.bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective
      B integerBase hZ X.toBase.hom p X.total.2 (schemeSpace X.base).2 (hX p))).2 Y' g

end M9Native.CurveFamilyUniversalH0
