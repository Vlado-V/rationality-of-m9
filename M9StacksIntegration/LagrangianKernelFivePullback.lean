module

public import M9StacksIntegration.LagrangianKernelFiveMinorNormalization

/-!
# Actual source naturality of the five determinant sections

The five sections are the pullbacks of five literal ordered universal
minors, transported by the actual exterior-pullback isomorphism. This
gives genuine source naturality of their native projective morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianKernelFivePullback

open LagrangianPluckerQuotient LagrangianMatrixChart LagrangianDeterminantSections LagrangianPullback
open LagrangianKernelFiveSections LagrangianKernelFiveMinorNormalization
open LagrangianSectionGeneration LagrangianPluckerGeneration

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

/-- Actual transport of generating sections along an actual module isomorphism. -/
theorem generatesStalks_transport {X : Scheme.{u}} {M N : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule X N]
    {n : ℕ} (s : Fin (n+1) → Γ(M, ⊤))
    (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
    (t : Fin (n+1) → Γ(N, ⊤)) (e : M ≅ N)
    (he : ∀ i, e.hom.app ⊤ (s i) = t i) :
    Stacks.ProjectiveFromSections.GeneratesStalks t := by
  letI := sectionMap_epi_of_generatesStalks s hs
  have hep : Epi (sectionMap X M s ≫ e.hom) := inferInstance
  have hmap : sectionMap X M s ≫ e.hom = sectionMap X N t :=
    (MukaiPrimitiveCanonicalEvaluation.sectionMap_postcomp (X := X) s e.hom).trans
      (congrArg (sectionMap X N) (funext he))
  exact generatesStalks_of_sectionMap_epi X N t (hmap ▸ hep)

variable (k : Type u) [Field k]

/-- The literal five ordered universal minors, on the original native LG. -/
def ambientFiveSections (a : Fin 5) : Γ(determinantLine k, ⊤) :=
  minorSection (LagrangianGrassmannian.space k) (quotientOnLG k).map (fiveMinor a)

/-- Their actual pullback to every native test scheme. -/
def pulledFiveSections {X : Scheme.{u}} (l : X ⟶ LagrangianGrassmannian.space k)
    (a : Fin 5) : Γ((Scheme.Modules.pullback l).obj (determinantLine k), ⊤) :=
  pullbackGlobalSections l (determinantLine k) (ambientFiveSections k a)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (l : X ⟶ LagrangianGrassmannian.space k)

/-- The actual exterior-pullback comparison, with no coefficient identification premise. -/
theorem pulledFiveSections_transport (a : Fin 5) :
    (exteriorPullbackIso l (quotientOnLG k).target 3).hom.app ⊤
      (pulledFiveSections k l a) =
        fiveSections k f (LagrangianUniversalSections.quotientMap k l) a := by
  rw [fiveSections_eq_orderedMinor]
  exact LagrangianDeterminantPullback.minorSection_pullback l (quotientOnLG k) (fiveMinor a)

variable [CharZero k]

theorem pulledFiveSections_generatesStalks
    (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤
      (freeBasisSection X 6 0) = 0) :
    Stacks.ProjectiveFromSections.GeneratesStalks (pulledFiveSections k l) := by
  letI := transportedDeterminant_isInvertibleModule k l
    (Iso.refl (LagrangianUniversalSections.bundle k l))
  let e := exteriorPullbackIso l (quotientOnLG k).target 3
  apply generatesStalks_transport
    (fiveSections k f (LagrangianUniversalSections.quotientMap k l))
    (fiveSections_generatesStalks k f l hl hq) (pulledFiveSections k l) e.symm
  intro a
  have h := congrArg (fun s => e.inv.app ⊤ s) (pulledFiveSections_transport k f l a)
  have heid : e.inv.app ⊤ (e.hom.app ⊤ (pulledFiveSections k l a)) =
      pulledFiveSections k l a := by
    change (e.hom ≫ e.inv).app ⊤ (pulledFiveSections k l a) = _
    rw [Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  exact h.symm.trans heid

/-- The already-constructed projective map is the native map of these actual pullbacks. -/
theorem projectiveMap_eq_pulled
    (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤
      (freeBasisSection X 6 0) = 0) :
    projectiveMap k f l hl hq =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver (pulledFiveSections k l)
        (pulledFiveSections_generatesStalks k f l hl hq) f := by
  letI := transportedDeterminant_isInvertibleModule k l
    (Iso.refl (LagrangianUniversalSections.bundle k l))
  symm
  exact ProjectiveSectionIso.toProjectiveSpaceOver_iso (pulledFiveSections k l)
    (fiveSections k f (LagrangianUniversalSections.quotientMap k l))
    (pulledFiveSections_generatesStalks k f l hl hq)
    (fiveSections_generatesStalks k f l hl hq)
    (exteriorPullbackIso l (quotientOnLG k).target 3)
    (pulledFiveSections_transport k f l) f

omit [CharZero k] in
/-- The actual pullback-composition isomorphism retains every one of the five sections. -/
theorem pulledFiveSections_comp {Y : Scheme.{u}} (t : Y ⟶ X) (a : Fin 5) :
    ((Scheme.Modules.pullbackComp t l).app (determinantLine k)).hom.app ⊤
      (pullbackGlobalSections t ((Scheme.Modules.pullback l).obj (determinantLine k))
        (pulledFiveSections k l a)) = pulledFiveSections k (t ≫ l) a :=
  AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp t l
    (determinantLine k) (ambientFiveSections k a)

/-- Actual source naturality of the constructed five-section morphism.
The two zero-section hypotheses are literal equations, not map comparisons. -/
theorem projectiveMap_comp
    (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hq : (LagrangianUniversalSections.quotientMap k l).app ⊤
      (freeBasisSection X 6 0) = 0)
    {Y : Scheme.{u}} (t : Y ⟶ X)
    (hqt : (LagrangianUniversalSections.quotientMap k (t ≫ l)).app ⊤
      (freeBasisSection Y 6 0) = 0) :
    t ≫ projectiveMap k f l hl hq =
      projectiveMap k (t ≫ f) (t ≫ l) (by rw [Category.assoc, hl]) hqt := by
  let hc : (t ≫ l) ≫ LagrangianGrassmannian.projection k = t ≫ f := by
    rw [Category.assoc, hl]
  let st : Stacks.ProjectiveSpaceModuli.GeneratingTuple X 4 :=
    ⟨(Scheme.Modules.pullback l).obj (determinantLine k), inferInstance,
      pulledFiveSections k l, pulledFiveSections_generatesStalks k f l hl hq⟩
  have hgen : Stacks.ProjectiveFromSections.GeneratesStalks
      (fun a => pullbackGlobalSections t ((Scheme.Modules.pullback l).obj (determinantLine k))
        (pulledFiveSections k l a)) :=
    (Stacks.ProjectiveSpaceModuli.pullbackTuple t st).generates
  calc
    _ = t ≫ Stacks.ProjectiveFromSections.toProjectiveSpaceOver (pulledFiveSections k l)
        (pulledFiveSections_generatesStalks k f l hl hq) f :=
      congrArg (fun m => t ≫ m) (projectiveMap_eq_pulled k f l hl hq)
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (fun a => pullbackGlobalSections t ((Scheme.Modules.pullback l).obj (determinantLine k))
          (pulledFiveSections k l a)) hgen (t ≫ f) :=
      comp_toProjectiveSpaceOver_sameBase (pulledFiveSections k l)
        (pulledFiveSections_generatesStalks k f l hl hq) t f hgen
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver (pulledFiveSections k (t ≫ l))
        (pulledFiveSections_generatesStalks k (t ≫ f) (t ≫ l) hc hqt) (t ≫ f) :=
      ProjectiveSectionIso.toProjectiveSpaceOver_iso _ _ hgen
        (pulledFiveSections_generatesStalks k (t ≫ f) (t ≫ l) hc hqt)
        ((Scheme.Modules.pullbackComp t l).app (determinantLine k))
        (pulledFiveSections_comp k l t) (t ≫ f)
    _ = _ := (projectiveMap_eq_pulled k (t ≫ f) (t ≫ l) hc hqt).symm

end M9Native.LagrangianKernelFivePullback
