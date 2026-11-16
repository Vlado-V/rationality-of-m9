module

public import M9StacksIntegration.VanishingSectionConormalMap
public import M9StacksIntegration.SectionZeroEvaluation
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact

/-!
# Vanishing of the conormal inside the full section zero scheme

The actual equation-induced conormal map has zero composite with the
native right conormal-transitivity arrow whenever dual evaluation
vanishes on the intermediate closed subscheme. That arrow is genuinely
epimorphic. Thus an epimorphic equation-induced map forces the relative
conormal to be zero. For the full native section zero scheme, evaluation
vanishing follows from its original dual-evaluation ideal definition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules RingedSpaceModuleAdjunction

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.SectionZeroRelativeConormal

open M9Native.VanishingSectionConormalMap
open Stacks.ClosedImmersion Stacks.Immersion

theorem pullbackHomEquiv_zero {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N
      (0 : (Scheme.Modules.pullback f).obj M ⟶ N) = 0 := by
  change (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app M ≫
    (modulePushforward f.toLRSHom.toShHom).map (0 : _ ⟶ N) = 0
  rw [modulePushforward_map_zero, comp_zero]

section IntermediateClosedSubscheme

variable {X Y C : Scheme.{u}} (j : Y ⟶ X) (q : C ⟶ Y)
  [IsClosedImmersion j] [IsClosedImmersion q]

/-- The genuine map of defining ideals for the triangle of closed immersions. -/
def relativeIdealMap :
    (modulePullback j.toLRSHom.toShHom).obj
      (idealSheaf (q ≫ j).toLRSHom.toShHom) ⟶ idealSheaf q.toLRSHom.toShHom :=
  Stacks.ClosedImmersion.idealSheafMap
    (i := q.toLRSHom.toShHom) (j := (q ≫ j).toLRSHom.toShHom)
    (f := (Scheme.Hom.toLRSHom (𝟙 C)).toShHom) (k := j.toLRSHom.toShHom)
    (toShHom_square (conormalSequence_isPullback q j).w)

variable {M : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)}

omit [IsClosedImmersion q] in
/-- An actual ideal-valued map killed on the intermediate subscheme has
zero image under the genuine relative ideal map. -/
theorem relativeIdeal_map_eq_zero
    (a : M ⟶ idealSheaf (q ≫ j).toLRSHom.toShHom)
    (hzero : a ≫ idealSheafι (q ≫ j).toLRSHom.toShHom ≫
      structureSheafModuleHom j.toLRSHom.toShHom = 0) :
    (modulePullback j.toLRSHom.toShHom).map a ≫ relativeIdealMap j q = 0 := by
  apply (cancel_mono (idealSheafι q.toLRSHom.toShHom)).mp
  rw [zero_comp, Category.assoc]
  change (modulePullback j.toLRSHom.toShHom).map a ≫
    Stacks.ClosedImmersion.idealSheafMap
      (toShHom_square (conormalSequence_isPullback q j).w) ≫ idealSheafι q.toLRSHom.toShHom = 0
  rw [idealSheafMap_comp_ι, ← Functor.map_comp_assoc]
  apply ((modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_modulePullbackUnitToUnit]
  simpa only [Category.assoc, Adjunction.homEquiv_unit, modulePushforward_map_zero, comp_zero] using hzero

/-- The native right conormal quotient kills every such actual ideal map,
with the canonical quotient normalization retained. -/
theorem relativeIdeal_comp_quotient_eq_zero
    (a : M ⟶ idealSheaf (q ≫ j).toLRSHom.toShHom)
    (hzero : a ≫ idealSheafι (q ≫ j).toLRSHom.toShHom ≫
      structureSheafModuleHom j.toLRSHom.toShHom = 0) :
    a ≫ canonicalConormalQuotientMap (q ≫ j) ≫
      (modulePushforward (q ≫ j).toLRSHom.toShHom).map (conormalSequenceRightMap q j) = 0 := by
  let comm := toShHom_square (conormalSequence_isPullback q j).w
  have hid :
      (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 C)).toShHom).homEquiv _ _
        (immersionConormalSheafMap q (q ≫ j) (𝟙 C) j comm) =
          conormalSequenceRightMap q j :=
    homEquiv_id_eq C.toLocallyRingedSpace.toRingedSpace _ _ _
  have hright := canonicalConormalQuotientMap_comp_pushforward_homEquiv
    q (q ≫ j) (𝟙 C) j comm
  rw [hid] at hright
  have hnat := (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.naturality a
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have hz : a ≫
      (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.app
        (idealSheaf (q ≫ j).toLRSHom.toShHom) ≫
      (modulePushforward j.toLRSHom.toShHom).map (relativeIdealMap j q) = 0 := by
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp,
      relativeIdeal_map_eq_zero j q a hzero, modulePushforward_map_zero, comp_zero]
  rw [hright]
  simpa only [relativeIdealMap, Category.assoc, zero_comp] using
    congrArg (fun b => b ≫
      (modulePushforward j.toLRSHom.toShHom).map (canonicalConormalQuotientMap q) ≫
      (modulePushforwardSquareIso (Scheme.Hom.toLRSHom (𝟙 C)).toShHom
        j.toLRSHom.toShHom q.toLRSHom.toShHom (q ≫ j).toLRSHom.toShHom comm).hom.app
          (conormalSheaf q.liftCoborder.toLRSHom.toShHom)) hz

variable (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
  (s : Γ(E, ⊤)) (hs : pullbackGlobalSections (q ≫ j) E s = 0)

/-- The actual equation-to-conormal map has zero composite with the
native relative conormal quotient; its normalization is unchanged. -/
theorem conormalMap_comp_right_eq_zero
    (hzero : dualEvalHom E s ≫ structureMap j = 0) :
    conormalMap (q ≫ j) E s hs ≫ conormalSequenceRightMap q j = 0 := by
  let a : dualModule E ⟶ idealSheaf (q ≫ j).toLRSHom.toShHom :=
    idealEvaluation (q ≫ j) E s hs
  have ha : a ≫ idealSheafι (q ≫ j).toLRSHom.toShHom = dualEvalHom E s :=
    idealEvaluation_comp_inclusion (q ≫ j) E s hs
  have ha0 : a ≫ idealSheafι (q ≫ j).toLRSHom.toShHom ≫
      structureSheafModuleHom j.toLRSHom.toShHom = 0 :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun b => b ≫ structureSheafModuleHom j.toLRSHom.toShHom) ha)).trans hzero
  have hz := relativeIdeal_comp_quotient_eq_zero j q a ha0
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (q ≫ j)
  apply (adj.homEquiv _ _).injective
  calc
    _ = adj.homEquiv _ _ (conormalMap (q ≫ j) E s hs) ≫
        (Scheme.Modules.pushforward (q ≫ j)).map (conormalSequenceRightMap q j) :=
      adj.homEquiv_naturality_right _ _
    _ = (idealEvaluation (q ≫ j) E s hs ≫ canonicalConormalQuotientMap (q ≫ j)) ≫
        (Scheme.Modules.pushforward (q ≫ j)).map (conormalSequenceRightMap q j) :=
      congrArg (fun b => b ≫
        (Scheme.Modules.pushforward (q ≫ j)).map (conormalSequenceRightMap q j))
          (conormalMap_adjoint (q ≫ j) E s hs)
    _ = 0 := (Category.assoc _ _ _).trans hz
    _ = _ := (pullbackHomEquiv_zero (q ≫ j) _ _).symm

/-- If the original equations already surject onto the ambient conormal,
the conormal inside the intermediate closed subscheme is zero. -/
theorem isZero_conormalSheaf_of_epi
    (hzero : dualEvalHom E s ≫ structureMap j = 0)
    [Epi (conormalMap (q ≫ j) E s hs)] :
    IsZero (Stacks.Conormal.conormalSheaf q) := by
  let := epi_conormalSequenceRightMap q j
  have hr : conormalSequenceRightMap q j = 0 :=
    (cancel_epi (conormalMap (q ≫ j) E s hs)).mp
      (by simpa only [comp_zero] using conormalMap_comp_right_eq_zero j q E s hs hzero)
  exact IsZero.of_epi_eq_zero (conormalSequenceRightMap q j) hr

end IntermediateClosedSubscheme

section FullZeroScheme

variable {X C : Scheme.{u}} (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E, ⊤))

/-- The full native zero ideal kills the actual dual evaluation map. -/
theorem fullZero_evaluation_eq_zero :
    dualEvalHom E s ≫ structureMap (Stacks.Chow.zeroSchemeOfSection X E s).subschemeι = 0 :=
  M9Native.SectionConormalEvaluation.eval_comp_structure_zero E s
    (Stacks.Chow.zeroSchemeOfSection X E s) (M9Native.SectionZeroEvaluation.eval_mem_zeroIdeal E s)

/-- The desired consequence for the FULL native section zero scheme,
with all its nilpotent structure retained. -/
theorem fullZero_isZero_conormalSheaf
    (q : C ⟶ (Stacks.Chow.zeroSchemeOfSection X E s).subscheme) [IsClosedImmersion q]
    (hs : pullbackGlobalSections (q ≫ (Stacks.Chow.zeroSchemeOfSection X E s).subschemeι) E s = 0)
    [Epi (conormalMap (q ≫ (Stacks.Chow.zeroSchemeOfSection X E s).subschemeι) E s hs)] :
    IsZero (Stacks.Conormal.conormalSheaf q) :=
  isZero_conormalSheaf_of_epi (Stacks.Chow.zeroSchemeOfSection X E s).subschemeι q E s hs
    (fullZero_evaluation_eq_zero E s)

/-- A true factorization triangle lets callers retain their original
ambient immersion and their original section-vanishing proof. -/
theorem fullZero_isZero_conormalSheaf_of_triangle
    (i : C ⟶ X) [IsClosedImmersion i]
    (q : C ⟶ (Stacks.Chow.zeroSchemeOfSection X E s).subscheme) [IsClosedImmersion q]
    (hi : q ≫ (Stacks.Chow.zeroSchemeOfSection X E s).subschemeι = i)
    (hs : pullbackGlobalSections i E s = 0) [Epi (conormalMap i E s hs)] :
    IsZero (Stacks.Conormal.conormalSheaf q) := by
  subst i
  exact fullZero_isZero_conormalSheaf E s q hs

end FullZeroScheme

end M9Native.SectionZeroRelativeConormal

end
