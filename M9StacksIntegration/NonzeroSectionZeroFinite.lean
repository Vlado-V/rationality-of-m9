module

public import M9StacksIntegration.SectionZeroEvaluation
public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# The full zero scheme of a nonzero vector-bundle section on a proper curve is finite

Actual finite free frames show that a zero evaluation ideal forces the
original section to be zero. On an integral scheme, a nonzero section
therefore cuts out a proper closed subset. Native dimension drop on a
one-dimensional irreducible scheme and properness then prove finiteness
of the ORIGINAL zero-scheme morphism. No reduction of that scheme is
performed; all nilpotents are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.NonzeroSectionZeroFinite

variable {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E, ⊤))

/-- Local genuine finite free expansions detect the ORIGINAL section. -/
theorem section_eq_zero_of_zeroScheme_eq_bot
    (hJ : Stacks.Chow.zeroSchemeOfSection X E s = ⊥) : s = 0 := by
  classical
  choose V hxV hVle ι hι he using fun x : X =>
    SectionZeroEvaluation.exists_affine_frame E (U := ⊤) (x := x) (by trivial)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨E.val.presheaf, E.isSheaf⟩
    (fun x : X => (V x : X.Opens)) ⊤ (fun x => homOfLE (hVle x))
    (fun y _ => Opens.mem_iSup.2 ⟨y, hxV y⟩) s 0 (fun x => ?_)
  letI : Finite (ι x) := hι x
  letI : Fintype (ι x) := Fintype.ofFinite (ι x)
  let e := (he x).some
  let t : Γ(E, (V x : X.Opens)) := E.presheaf.map (homOfLE le_top).op s
  have hcoord (i : ι x) :
      evalAt E
        (SectionZeroEvaluation.frameDualSection E (V x : X.Opens) e i) t = 0 := by
    have hm := SectionZeroEvaluation.eval_mem_zeroIdeal E s (V x)
      (SectionZeroEvaluation.frameDualSection E (V x : X.Opens) e i)
    rw [hJ, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot] at hm
    exact hm
  have ht : t = 0 := (SectionZeroEvaluation.frame_expansion E (V x : X.Opens) e t).trans (by
    apply Finset.sum_eq_zero
    intro i _
    rw [hcoord i, zero_smul])
  change E.presheaf.map (homOfLE (hVle x)).op s =
    E.presheaf.map (homOfLE (hVle x)).op 0
  rw [map_zero]
  exact ht

theorem zeroScheme_ne_bot_of_section_ne_zero (hs : s ≠ 0) :
    Stacks.Chow.zeroSchemeOfSection X E s ≠ ⊥ :=
  fun hJ => hs (section_eq_zero_of_zeroScheme_eq_bot E s hJ)

/-- Reducedness of the BASE is used; no reducedness of the zero scheme is asserted. -/
theorem supportSet_ne_univ_of_section_ne_zero [IsReduced X] (hs : s ≠ 0) :
    (Stacks.Chow.zeroSchemeOfSection X E s).supportSet ≠ Set.univ := by
  intro hsupport
  have htop : (Stacks.Chow.zeroSchemeOfSection X E s).support = ⊤ :=
    SetLike.coe_injective hsupport
  exact zeroScheme_ne_bot_of_section_ne_zero E s hs
    (Scheme.IdealSheafData.support_eq_top_iff.mp htop)

/-- The full zero subscheme, including nilpotents, has dimension at most zero. -/
theorem dimension_zero_of_section_ne_zero [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (hs : s ≠ 0) :
    topologicalKrullDim (Stacks.Chow.zeroSchemeOfSection X E s).subscheme ≤ 0 := by
  let J := Stacks.Chow.zeroSchemeOfSection X E s
  have hclosed : IsClosed J.supportSet := J.support.isClosed
  have hdimSupport : topologicalKrullDim J.supportSet ≤ 0 :=
    topologicalKrullDim_le_zero_of_isClosed_of_ne_univ hdim J.supportSet hclosed
      (supportSet_ne_univ_of_section_ne_zero E s hs)
  exact (topologicalKrullDim_le_of_range_subset J.subschemeι J.supportSet
    (by rw [J.range_subschemeι]; exact subset_rfl)).trans hdimSupport

/-- Genuine morphism finiteness of the ORIGINAL zero scheme over the ORIGINAL field. -/
theorem isFinite_zeroSchemeOfSection_of_dimension_le_one
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (hs : s ≠ 0) :
    IsFinite ((Stacks.Chow.zeroSchemeOfSection X E s).subschemeι ≫ f) :=
  isFinite_of_isProper_of_topologicalKrullDim_le_zero
    ((Stacks.Chow.zeroSchemeOfSection X E s).subschemeι ≫ f)
    (dimension_zero_of_section_ne_zero E s hdim hs)

/-- The actual curve dimension supplies the bound; smoothness, algebraic
closedness and a pattern for the zero scheme are unnecessary. -/
theorem isFinite_zeroSchemeOfSection_of_isCurve
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f]
    (hs : s ≠ 0) :
    IsFinite ((Stacks.Chow.zeroSchemeOfSection X E s).subschemeι ≫ f) :=
  isFinite_zeroSchemeOfSection_of_dimension_le_one E s K f
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le hs

end M9Native.NonzeroSectionZeroFinite
