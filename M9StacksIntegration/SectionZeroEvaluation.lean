module

public import M9StacksIntegration.SectionConormalEvaluation
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Ideal
public import StacksFrontier.AlgebraicGeometry.ReflexiveDualHullInput.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Actual evaluation onto the zero ideal of a finite locally free section

The ideal is the native zero-scheme ideal. Local finite free frames make
its generators values of genuine sections of the sheaf dual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionZeroEvaluation

variable {X : Scheme.{u}} (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
  (s : Γ(E, (⊤ : X.Opens)))

/-- Affine evaluation belongs to the actual native zero ideal; no
normal-bundle or ideal-generation assertion is a premise. -/
theorem eval_mem_zeroIdeal (V : X.affineOpens) (t : Γ(dualSheaf E, (V : X.Opens))) :
    evalAt E t (E.presheaf.map (homOfLE le_top).op s) ∈
      (Stacks.Chow.zeroSchemeOfSection X E s).ideal V := by
  rw [Stacks.Chow.SectionZeroScheme.zeroSchemeOfSection_ideal E s V]
  exact Ideal.subset_span ⟨dualEvalLinearMap E t, rfl⟩

/-- Evaluation into the original native zero ideal. -/
def evaluationIdealMap : dualSheaf E ⟶
    idealSheafModule (Stacks.Chow.zeroSchemeOfSection X E s) :=
  SectionConormalEvaluation.evaluationIdealModuleMap E s _ (eval_mem_zeroIdeal E s)

theorem evaluationIdealMap_eval (U : X.Opens) (t : Γ(dualSheaf E, U)) :
    Stacks.Divisors.idealSheafSection (Stacks.Chow.zeroSchemeOfSection X E s)
      (Scheme.Modules.Hom.app (evaluationIdealMap E s) U t) =
        evalAt E t (E.presheaf.map (homOfLE le_top).op s) :=
  SectionConormalEvaluation.evaluationIdealModuleMap_eval E s _ (eval_mem_zeroIdeal E s) U t

/-- Every point has an affine neighbourhood carrying a genuine finite
free isomorphism on the entire slice site. -/
theorem exists_affine_frame {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ (V : X.affineOpens), x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ U ∧
      ∃ (ι : Type u), Finite ι ∧ Nonempty
        (E.over (V : X.Opens) ≅ SheafOfModules.free
          (R := X.ringCatSheaf.over (V : X.Opens)) ι) := by
  obtain ⟨q, hq, hfin⟩ := hE.exists_isFiniteLocallyFreeData
  let := hq
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff (X : Type u) q.X).mp q.coversTop).exists_mem x
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U ⊓ q.X i from ⟨hx, hi⟩) (U ⊓ q.X i).isOpen
  let T := SheafOfModules.overMap X.ringCatSheaf
    (homOfLE (show V ≤ q.X i from fun y hy => (hVle hy).2))
  let G := (q.generators i).map T (Iso.refl _)
  have : IsIso G.π := by dsimp [G]; infer_instance
  have : Finite G.I := (hfin.isFiniteType i).finite
  exact ⟨⟨V, hV⟩, hxV, (fun y hy => (hVle hy).1),
    G.I, inferInstance, ⟨(asIso G.π).symm⟩⟩

section Frame

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (U : X.Opens)
  (e : E.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) ι)

/-- A frame coordinate is a genuine section of the actual sheaf dual. -/
def frameDualSection (i : ι) : Γ(dualSheaf E, U) := by
  classical
  exact ((dualSheafHom E).sectionsEquiv U).symm
    (e.hom ≫ Stacks.SheafOfModules.freeProj i)

/-- A frame vector is the actual image of the corresponding unit section. -/
def frameVector (i : ι) : Γ(E, U) :=
  (SheafOfModules.freeHomEquiv (E.over U) e.inv i).eval (op (Over.mk (𝟙 U)))

omit hE [Fintype ι] in
theorem frameDualSection_eval (i : ι) (m : Γ(E, U)) :
    evalAt E (frameDualSection E U e i) m =
      Stacks.SheafOfModules.freeCoord (op (Over.mk (𝟙 U)))
        (e.hom.val.app (op (Over.mk (𝟙 U))) m) i := by
  classical
  change ((dualSheafHom E).sectionsEquiv U (frameDualSection E U e i)).val.app
    (op (Over.mk (𝟙 U))) m = _
  unfold frameDualSection
  rw [AddEquiv.apply_symm_apply]
  rfl

omit hE in
/-- The finite frame expansion is on actual sections, not merely stalks. -/
theorem frame_expansion (m : Γ(E, U)) :
    m = ∑ i, evalAt E (frameDualSection E U e i) m • frameVector E U e i := by
  classical
  let V : Over U := Over.mk (𝟙 U)
  let c := Stacks.SheafOfModules.coordsOver (R := X.ringCatSheaf) V
    (e.hom.val.app (op V) m)
  have he : e.inv = Stacks.SheafOfModules.freeToOver E (frameVector E U e) := by
    exact (congrArg (fun f => f) ((SheafOfModules.freeHomEquiv (E.over U)).symm_apply_apply
      e.inv)).symm.trans
        (Stacks.SheafOfModules.freeHomEquiv_symm_eq_freeToOver E
          (SheafOfModules.freeHomEquiv (E.over U) e.inv))
  have h := Stacks.SheafOfModules.freeToOver_app_ofCoordsOver E
    (frameVector E U e) V c
  rw [← he, Stacks.SheafOfModules.ofCoordsOver_coordsOver] at h
  rw [Stacks.SheafOfModules.inv_val_app_hom_val_app] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  exact congrArg₂ (fun (a : Γ(X, U)) (v : Γ(E, U)) => a • v)
    (frameDualSection_eval E U e i m).symm
    (Stacks.SheafOfModules.res_id E (frameVector E U e i))

include e in

/-- On an affine frame, every actual zero-ideal section is the evaluation
of an actual dual section. Only local preimages are claimed. -/
theorem exists_dual_eval_of_mem (hU : IsAffineOpen U) (a : Γ(X, U))
    (ha : a ∈ (Stacks.Chow.zeroSchemeOfSection X E s).ideal ⟨U, hU⟩) :
    ∃ t : Γ(dualSheaf E, U), evalAt E t
      (E.presheaf.map (homOfLE le_top).op s) = a := by
  classical
  let v : Γ(E, U) := E.presheaf.map (homOfLE le_top).op s
  let ev : Γ(dualSheaf E, U) →ₗ[Γ(X, U)] Γ(X, U) :=
    ((dualEvalHom E s).val.app (op U)).hom
  let A : Ideal Γ(X, U) := LinearMap.range ev
  have hspan : Ideal.span {a : Γ(X, U) | ∃ φ : Γ(E, U) →ₗ[Γ(X, U)] Γ(X, U),
      a = φ v} ≤ A := by
    refine Ideal.span_le.2 ?_
    rintro a ⟨φ, rfl⟩
    have hφ : φ v = ∑ i, φ (frameVector E U e i) *
        evalAt E (frameDualSection E U e i) v := by
      calc
        φ v = φ (∑ i, evalAt E (frameDualSection E U e i) v •
            frameVector E U e i) := congrArg φ (frame_expansion E U e v)
        _ = _ := by
          simp only [map_sum, map_smul, smul_eq_mul]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hφ]
    refine Ideal.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_left _ _ ⟨frameDualSection E U e i, rfl⟩
  rw [Stacks.Chow.SectionZeroScheme.zeroSchemeOfSection_ideal E s ⟨U, hU⟩] at ha
  exact hspan ha

end Frame

/-- Evaluation is locally surjective onto the actual zero ideal. -/
theorem evaluationIdealMap_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (evaluationIdealMap E s).val) := by
  constructor
  intro U y
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V, hxV, hVU, ι, hι, ⟨e⟩⟩ := exists_affine_frame E hx
  let := hι
  let := Fintype.ofFinite ι
  classical
  let I := Stacks.Chow.zeroSchemeOfSection X E s
  let yV := (Stacks.Divisors.idealSheafOfModules I).val.resLE hVU y
  have hyV : Stacks.Divisors.idealSheafSection I yV ∈ I.ideal V :=
    (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection I V _).2 ⟨yV, rfl⟩
  obtain ⟨t, ht⟩ := exists_dual_eval_of_mem E s V.1 e V.2 _ hyV
  refine ⟨V.1, homOfLE hVU, ⟨t, ?_⟩, hxV⟩
  exact Stacks.Divisors.idealSheafSection_injective I
    ((evaluationIdealMap_eval E s V.1 t).trans ht)

/-- The actual sheaf morphism onto the actual zero ideal is an epimorphism. -/
theorem evaluationIdealMap_epi : Epi (evaluationIdealMap E s) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (evaluationIdealMap_locallySurjective E s)

end M9Native.SectionZeroEvaluation
