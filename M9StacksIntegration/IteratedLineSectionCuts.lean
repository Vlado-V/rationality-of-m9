module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# Actual successive line-section cuts

Successive zero schemes of restricted sections represent simultaneous
vanishing of the original sections on every test scheme. In particular,
the comparison retains the scheme structure, including nilpotents.

The pullback-composition zero lemma follows the short proof of the
private lemma of the same purpose in the pinned native
`Chow/ZeroSchemePullback/Basic.lean`; the zero-scheme factorization theorem
itself is used directly from that provider.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.IteratedLineSectionCuts

variable {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      X.sheaf.obj X.ringCatSheaf.property L]

/-- An actual factorization through an object over the original scheme. -/
def FactorsThrough {T : Scheme.{u}} (f : T ⟶ X) (A : Over X) : Prop :=
  ∃ g : T ⟶ A.left, g ≫ A.hom = f

/-- The actual zero ideal of a restricted original section. -/
def cutIdeal (A : Over X) (s : Γ(L, ⊤)) : A.left.IdealSheafData :=
  Stacks.Divisors.zeroScheme A.left ((Scheme.Modules.pullback A.hom).obj L)
    (pullbackGlobalSections A.hom L s)

/-- One actual cut, with its composite map to the original scheme. -/
def cut (A : Over X) (s : Γ(L, ⊤)) : Over X :=
  Over.mk ((cutIdeal L A s).subschemeι ≫ A.hom)

/-- Actual repeated zero schemes of the successively restricted sections. -/
def iteratedCut : List Γ(L, ⊤) → Over X → Over X
  | [], A => A
  | s :: ss, A => iteratedCut ss (cut L A s)

omit [AlgebraicGeometry.SheafOfModules.IsInvertible
  X.sheaf.obj X.ringCatSheaf.property L] in
/-- Pullback-composition transports zero sections faithfully. -/
theorem pullback_comp_zero_iff {Y T : Scheme.{u}} (f : T ⟶ Y) (g : Y ⟶ X)
    (s : Γ(L, ⊤)) :
    pullbackGlobalSections (f ≫ g) L s = 0 ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L)
        (pullbackGlobalSections g L s) = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  refine ⟨fun h => pullbackGlobalSections_injective_pullbackComp f g L ?_, fun h => ?_⟩
  · simpa using h
  · simp [h]

/-- One actual cut represents factorization through the previous scheme
and vanishing of the original section. -/
theorem cut_factors_iff {T : Scheme.{u}} (f : T ⟶ X) (A : Over X)
    (s : Γ(L, ⊤)) :
    FactorsThrough f (cut L A s) ↔
      FactorsThrough f A ∧ pullbackGlobalSections f L s = 0 := by
  let I := cutIdeal L A s
  change (∃ g : T ⟶ I.subscheme, g ≫ (I.subschemeι ≫ A.hom) = f) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨⟨g ≫ I.subschemeι, by simpa only [Category.assoc] using hg⟩, ?_⟩
    have hz : pullbackGlobalSections (g ≫ I.subschemeι)
        ((Scheme.Modules.pullback A.hom).obj L)
        (pullbackGlobalSections A.hom L s) = 0 :=
      (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme A.left
        ((Scheme.Modules.pullback A.hom).obj L) (pullbackGlobalSections A.hom L s)
        (g ≫ I.subschemeι)).mpr ⟨g, rfl⟩
    rw [← hg, ← Category.assoc]
    exact (pullback_comp_zero_iff L (g ≫ I.subschemeι) A.hom s).mpr hz
  · rintro ⟨⟨g, hg⟩, hz⟩
    have hz' : pullbackGlobalSections g ((Scheme.Modules.pullback A.hom).obj L)
        (pullbackGlobalSections A.hom L s) = 0 :=
      (pullback_comp_zero_iff L g A.hom s).mp (by rw [hg]; exact hz)
    obtain ⟨h, hh⟩ :=
      (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme A.left
        ((Scheme.Modules.pullback A.hom).obj L) (pullbackGlobalSections A.hom L s) g).mp hz'
    change h ≫ I.subschemeι = g at hh
    exact ⟨h, by rw [← Category.assoc, hh, hg]⟩

/-- The exact all-test universal property of successive restricted cuts. -/
theorem iteratedCut_factors_iff {T : Scheme.{u}} (f : T ⟶ X)
    (ss : List Γ(L, ⊤)) (A : Over X) :
    FactorsThrough f (iteratedCut L ss A) ↔
      FactorsThrough f A ∧ ∀ s ∈ ss, pullbackGlobalSections f L s = 0 := by
  induction ss generalizing A with
  | nil => simp [iteratedCut]
  | cons s ss ih =>
    rw [iteratedCut, ih, cut_factors_iff]
    constructor
    · rintro ⟨⟨hA, hs⟩, hss⟩
      refine ⟨hA, fun t ht => ?_⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hss t ht
    · rintro ⟨hA, hss⟩
      exact ⟨⟨hA, hss s (List.mem_cons_self)⟩,
        fun t ht => hss t (List.mem_cons_of_mem s ht)⟩

/-- The successive-cut model starting with the actual original scheme. -/
def simultaneousCut (ss : List Γ(L, ⊤)) : Over X :=
  iteratedCut L ss (Over.mk (𝟙 X))

/-- The actual successive-cut scheme represents simultaneous vanishing
of every original section on every test scheme. -/
theorem simultaneousCut_factors_iff {T : Scheme.{u}} (f : T ⟶ X)
    (ss : List Γ(L, ⊤)) :
    FactorsThrough f (simultaneousCut L ss) ↔
      ∀ s ∈ ss, pullbackGlobalSections f L s = 0 := by
  rw [simultaneousCut, iteratedCut_factors_iff]
  exact ⟨fun h => h.2, fun h => ⟨⟨f, by simp⟩, h⟩⟩

/-- Cutting an actual closed subscheme gives an actual closed subscheme. -/
theorem cut_closed (A : Over X) (s : Γ(L, ⊤)) [IsClosedImmersion A.hom] :
    IsClosedImmersion (cut L A s).hom := by
  dsimp [cut]
  infer_instance

/-- The actual composite of successive zero-scheme inclusions is closed. -/
theorem iteratedCut_closed (ss : List Γ(L, ⊤)) (A : Over X) [IsClosedImmersion A.hom] :
    IsClosedImmersion (iteratedCut L ss A).hom := by
  induction ss generalizing A with
  | nil => change IsClosedImmersion A.hom; infer_instance
  | cons s ss ih =>
    let : IsClosedImmersion (cut L A s).hom := cut_closed L A s
    exact ih (cut L A s)

instance simultaneousCut_closed (ss : List Γ(L, ⊤)) :
    IsClosedImmersion (simultaneousCut L ss).hom := by
  let : IsClosedImmersion (Over.mk (𝟙 X)).hom := by
    change IsClosedImmersion (𝟙 X)
    infer_instance
  exact iteratedCut_closed L ss (Over.mk (𝟙 X))

end M9Native.IteratedLineSectionCuts

namespace M9Native.IteratedLineSectionCuts

variable {X : Scheme.{u}}

/-- The comparison map determined by identical actual factorization
properties on every test scheme. -/
def comparisonHom (A B : Over X)
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ X), FactorsThrough f A ↔ FactorsThrough f B) :
    A.left ⟶ B.left :=
  Classical.choose ((h A.left A.hom).mp ⟨𝟙 _, by simp⟩)

@[reassoc]
theorem comparisonHom_comp (A B : Over X)
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ X), FactorsThrough f A ↔ FactorsThrough f B) :
    comparisonHom A B h ≫ B.hom = A.hom :=
  Classical.choose_spec ((h A.left A.hom).mp ⟨𝟙 _, by simp⟩)

/-- Identical all-test factorization properties give an actual scheme
isomorphism over the original scheme whenever both structural maps are
monomorphisms. -/
def comparisonIso (A B : Over X) [Mono A.hom] [Mono B.hom]
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ X), FactorsThrough f A ↔ FactorsThrough f B) :
    A.left ≅ B.left where
  hom := comparisonHom A B h
  inv := comparisonHom B A (fun T f => (h T f).symm)
  hom_inv_id := (cancel_mono A.hom).mp (by
    simp only [Category.assoc, comparisonHom_comp, Category.id_comp])
  inv_hom_id := (cancel_mono B.hom).mp (by
    simp only [Category.assoc, comparisonHom_comp, Category.id_comp])

@[reassoc]
theorem comparisonIso_hom_comp (A B : Over X) [Mono A.hom] [Mono B.hom]
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ X), FactorsThrough f A ↔ FactorsThrough f B) :
    (comparisonIso A B h).hom ≫ B.hom = A.hom :=
  comparisonHom_comp A B h

@[reassoc]
theorem comparisonIso_inv_comp (A B : Over X) [Mono A.hom] [Mono B.hom]
    (h : ∀ (T : Scheme.{u}) (f : T ⟶ X), FactorsThrough f A ↔ FactorsThrough f B) :
    (comparisonIso A B h).inv ≫ A.hom = B.hom :=
  comparisonHom_comp B A (fun T f => (h T f).symm)

end M9Native.IteratedLineSectionCuts
