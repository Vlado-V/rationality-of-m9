module

public import M9StacksIntegration.IntegralHyperplaneRestriction
public import M9StacksIntegration.IteratedLineSectionCuts
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPullbackFamily

/-! Kernel calculation along literal successive zero schemes.  The
hypotheses describe only actual integral prefixes and actual nonzero
restricted defining sections.  No restriction-kernel conclusion occurs
in the input.  The identity-pullback calculation below follows the
pinned native FreeTower/Hyperplane identity-section proof. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Bertini

universe u

namespace M9Native.IntegralRestrictionLadder

open IteratedLineSectionCuts

variable (D : FamilyDivisors.{u,u})

/-- The actual restriction map, retaining the original field and
coefficient module in its type. -/
def restrictionMap {Y : Scheme.{u}} (g : Y ⟶ D.X) :
    D.V →ₗ[D.k] globalSections D.k (g ≫ D.toBase)
      ((Scheme.Modules.pullback g).obj D.L) :=
  (D.pullbackAlong g).ψ

/-- Only genuine geometric prefix data: integrality and a nonzero
section on each literal prefix zero scheme. -/
def IntegralSteps : List D.V → Over D.X → Prop
  | [], _ => True
  | v :: vs, A => IsIntegral A.left ∧
      (D.pullbackAlong A.hom).sectionOf v ≠ 0 ∧
      IntegralSteps vs (cut D.L A (D.sectionOf v))

section Proper
variable [IsAlgClosed D.k] [IsProper D.toBase]

/-- A single actual cut adds exactly its original coefficient vector
to the kernel; this is derived from the native regular-section sequence. -/
theorem ker_cut (A : Over D.X) [IsClosedImmersion A.hom] [IsIntegral A.left]
    (v : D.V) (hv : (D.pullbackAlong A.hom).sectionOf v ≠ 0) :
    LinearMap.ker (restrictionMap D (cut D.L A (D.sectionOf v)).hom) =
      LinearMap.ker (restrictionMap D A.hom) ⊔ Submodule.span D.k {v} := by
  let E := D.pullbackAlong A.hom
  let I := cutIdeal D.L A (D.sectionOf v)
  let : IsIntegral E.X := (inferInstance : IsIntegral A.left)
  let : IsAlgClosed E.k := (inferInstance : IsAlgClosed D.k)
  let : IsProper E.toBase := by
    change IsProper (A.hom ≫ D.toBase)
    infer_instance
  have hz (w : D.V) :
      (D.pullbackAlong (cut D.L A (D.sectionOf v)).hom).sectionOf w = 0 ↔
        pullbackGlobalSections I.subschemeι E.L (E.sectionOf w) = 0 :=
    pullback_comp_zero_iff D.L I.subschemeι A.hom (D.sectionOf w)
  apply le_antisymm
  · intro w hw
    have hw' : pullbackGlobalSections I.subschemeι E.L (E.sectionOf w) = 0 :=
      (hz w).mp hw
    obtain ⟨c,hc⟩ := IntegralHyperplaneRestriction.exists_scalar_multiple_of_pullback_zero
      E.L D.k E.toBase (E.sectionOf v) hv (E.sectionOf w) hw'
    have hk : w - c • v ∈ LinearMap.ker (restrictionMap D A.hom) := by
      change restrictionMap D A.hom (w - c • v) = 0
      rw [map_sub, map_smul]
      change E.sectionOf w -
        IntegralHyperplaneRestriction.coefficientMap D.k E.toBase c • E.sectionOf v = 0
      rw [hc,sub_self]
    exact Submodule.mem_sup.mpr ⟨w-c•v,hk,c•v,
      Submodule.smul_mem _ c (Submodule.subset_span (by simp)), by module⟩
  · apply sup_le
    · intro w hw
      apply (hz w).mpr
      rw [show E.sectionOf w = 0 from hw,map_zero]
    · apply Submodule.span_le.mpr
      intro w hw
      have hwv : w = v := Set.mem_singleton_iff.mp hw
      subst w
      apply (hz v).mpr
      exact pullbackGlobalSections_subschemeι_zeroScheme_eq_zero E.X E.L (E.sectionOf v)

/-- The complete literal zero-scheme ladder has precisely the original
kernel plus the span of the actual original defining coefficient list. -/
theorem ker_iteratedCut (vs : List D.V) (A : Over D.X)
    [IsClosedImmersion A.hom] (h : IntegralSteps D vs A) :
    LinearMap.ker
        (restrictionMap D (iteratedCut D.L (vs.map D.sectionOf) A).hom) =
      LinearMap.ker (restrictionMap D A.hom) ⊔
        Submodule.span D.k {v | v ∈ vs} := by
  induction vs generalizing A with
  | nil =>
    change LinearMap.ker (restrictionMap D A.hom) =
      LinearMap.ker (restrictionMap D A.hom) ⊔ Submodule.span D.k {v | v ∈ ([] : List D.V)}
    simp
  | cons v vs ih =>
    let B := cut D.L A (D.sectionOf v)
    let : IsIntegral A.left := h.1
    let : IsClosedImmersion B.hom := cut_closed D.L A (D.sectionOf v)
    have hi := ih B h.2.2
    change LinearMap.ker (restrictionMap D
      (iteratedCut D.L (vs.map D.sectionOf) B).hom) = _
    rw [hi,ker_cut D A v h.2.1]
    have hs : {w : D.V | w ∈ v :: vs} = ({v} : Set D.V) ∪ {w | w ∈ vs} := by
      ext w
      simp
    rw [hs,Submodule.span_union,sup_assoc]

end Proper

/-- The actual pullback along the identity recovers the original section. -/
theorem pullbackId_section {X : Scheme.{u}} (F : X.Modules) (s : Γ(F,⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app F).app ⊤
      (pullbackGlobalSections (𝟙 X) F s) = s := by
  have h : ((Scheme.Modules.pullbackId X).hom.app F).app (𝟙 X ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F).app ⊤ s) = s :=
    congrArg (fun (t : F ⟶ (Scheme.Modules.pushforward (𝟙 X)).obj F) => t.app ⊤ s)
      (AlgebraicGeometry.pullbackId_unit F)
  have hu : pullbackGlobalSections (𝟙 X) F s =
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F).app ⊤ s := by
    have hid : ((Scheme.Modules.pullback (𝟙 X)).obj F).presheaf.map
        (eqToHom (by simp : (⊤ : X.Opens) = 𝟙 X ⁻¹ᵁ ⊤)).op = 𝟙 _ := by
      rw [show (eqToHom (by simp : (⊤ : X.Opens) = 𝟙 X ⁻¹ᵁ ⊤)).op =
        CategoryTheory.CategoryStruct.id (Opposite.op (⊤ : X.Opens)) from rfl]
      exact CategoryTheory.Functor.map_id _ _
    change ((Scheme.Modules.pullback (𝟙 X)).obj F).presheaf.map
      (eqToHom (by simp : (⊤ : X.Opens) = 𝟙 X ⁻¹ᵁ ⊤)).op
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F).app ⊤ s) = _
    exact (ConcreteCategory.congr_hom hid _).trans (CategoryTheory.id_apply _)
  rw [hu]
  exact h

theorem ker_pullback_identity :
    LinearMap.ker (restrictionMap D (𝟙 D.X)) = LinearMap.ker D.ψ := by
  ext v
  change pullbackGlobalSections (𝟙 D.X) D.L (D.sectionOf v) = 0 ↔ D.sectionOf v = 0
  constructor
  · intro hv
    have h := pullbackId_section D.L (D.sectionOf v)
    rw [hv,map_zero] at h
    exact h.symm
  · intro hv
    rw [hv,map_zero]

theorem ker_simultaneousCut [IsAlgClosed D.k] [IsProper D.toBase]
    (vs : List D.V) (h : IntegralSteps D vs (Over.mk (𝟙 D.X))) :
    LinearMap.ker (restrictionMap D
      (simultaneousCut D.L (vs.map D.sectionOf)).hom) =
        LinearMap.ker D.ψ ⊔ Submodule.span D.k {v | v ∈ vs} := by
  have hi : IsClosedImmersion (Over.mk (𝟙 D.X)).hom := by
    change IsClosedImmersion (𝟙 D.X)
    infer_instance
  let : IsClosedImmersion (Over.mk (𝟙 D.X)).hom := hi
  rw [simultaneousCut,ker_iteratedCut D vs _ h]
  change LinearMap.ker (restrictionMap D (𝟙 D.X)) ⊔ _ = _
  rw [ker_pullback_identity]

end M9Native.IntegralRestrictionLadder
end
