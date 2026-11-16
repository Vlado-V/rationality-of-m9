module

public import M9StacksIntegration.IteratedLineSectionCuts

/-!
# Actual closed maps between the original line-section prefixes

These are maps of the literal successive zero schemes. They retain the
original ambient map and every restricted original section, including all
nilpotents; no integrality, regularity or desired restriction-kernel premise
is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9Native.LineSectionPrefixes
open IteratedLineSectionCuts

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- Every original equation vanishes on its literal simultaneous cut. -/
theorem section_zero_on_cut (ss : List Γ(L, ⊤)) {s : Γ(L, ⊤)} (hs : s ∈ ss) :
    pullbackGlobalSections (simultaneousCut L ss).hom L s = 0 := by
  apply (simultaneousCut_factors_iff L (simultaneousCut L ss).hom ss).mp
    ⟨𝟙 _, by simp⟩ s hs

/-- Inclusion of the actual equation lists gives an actual factorization
through the corresponding shorter zero scheme. -/
theorem factors_of_sublist (short long : List Γ(L, ⊤)) (h : short.Sublist long) :
    FactorsThrough (simultaneousCut L long).hom (simultaneousCut L short) := by
  apply (simultaneousCut_factors_iff L (simultaneousCut L long).hom short).mpr
  intro s hs
  exact section_zero_on_cut L long (h.subset hs)

/-- The actual map from the longer cut to the shorter cut. -/
def sublistHom (short long : List Γ(L, ⊤)) (h : short.Sublist long) :
    (simultaneousCut L long).left ⟶ (simultaneousCut L short).left :=
  Classical.choose (factors_of_sublist L short long h)

@[reassoc]
theorem sublistHom_over (short long : List Γ(L, ⊤)) (h : short.Sublist long) :
    sublistHom L short long h ≫ (simultaneousCut L short).hom =
      (simultaneousCut L long).hom :=
  Classical.choose_spec (factors_of_sublist L short long h)

/-- The actual longer cut is the represented pullback of its own ambient
closed immersion along the shorter cut's actual ambient immersion. -/
theorem sublistHom_isPullback (short long : List Γ(L, ⊤)) (h : short.Sublist long) :
    IsPullback (𝟙 (simultaneousCut L long).left) (sublistHom L short long h)
      (simultaneousCut L long).hom (simultaneousCut L short).hom := by
  apply IsPullback.of_horiz_isIso_mono
  constructor
  simpa using (sublistHom_over L short long h).symm

/-- The actual map between these literal cuts is a closed immersion. -/
theorem sublistHom_closed (short long : List Γ(L, ⊤)) (h : short.Sublist long) :
    IsClosedImmersion (sublistHom L short long h) :=
  MorphismProperty.of_isPullback (sublistHom_isPullback L short long h)
    (inferInstanceAs (IsClosedImmersion (simultaneousCut L long).hom))

/-- The actual maps compose, by monicity of the original ambient map. -/
theorem sublistHom_comp (a b c : List Γ(L, ⊤))
    (hab : a.Sublist b) (hbc : b.Sublist c) :
    sublistHom L b c hbc ≫ sublistHom L a b hab =
      sublistHom L a c (hab.trans hbc) := by
  apply (cancel_mono (simultaneousCut L a).hom).mp
  simp only [Category.assoc, sublistHom_over]

/-- The original full cut maps to every literal initial segment. -/
def prefixHom (ss : List Γ(L, ⊤)) (i : ℕ) :
    (simultaneousCut L ss).left ⟶ (simultaneousCut L (ss.take i)).left :=
  sublistHom L (ss.take i) ss (List.take_sublist i ss)

@[reassoc]
theorem prefixHom_over (ss : List Γ(L, ⊤)) (i : ℕ) :
    prefixHom L ss i ≫ (simultaneousCut L (ss.take i)).hom =
      (simultaneousCut L ss).hom :=
  sublistHom_over L _ _ _

theorem prefixHom_closed (ss : List Γ(L, ⊤)) (i : ℕ) :
    IsClosedImmersion (prefixHom L ss i) :=
  sublistHom_closed L _ _ _

/-- Actual pullback along the prefix map retains the zero condition for
the original section, using the genuine pullback-composition comparison. -/
theorem prefix_pullback_zero_iff (ss : List Γ(L, ⊤)) (i : ℕ) (s : Γ(L, ⊤)) :
    pullbackGlobalSections (prefixHom L ss i)
        ((Scheme.Modules.pullback (simultaneousCut L (ss.take i)).hom).obj L)
        (pullbackGlobalSections (simultaneousCut L (ss.take i)).hom L s) = 0 ↔
      pullbackGlobalSections (simultaneousCut L ss).hom L s = 0 := by
  rw [← pullback_comp_zero_iff, prefixHom_over]

/-- Every remaining original equation vanishes after restriction from a
prefix to the actual original final cut. -/
theorem tail_zero_on_final (ss : List Γ(L, ⊤)) (i : ℕ) {s : Γ(L, ⊤)}
    (hs : s ∈ ss.drop i) :
    pullbackGlobalSections (prefixHom L ss i)
        ((Scheme.Modules.pullback (simultaneousCut L (ss.take i)).hom).obj L)
        (pullbackGlobalSections (simultaneousCut L (ss.take i)).hom L s) = 0 := by
  apply (prefix_pullback_zero_iff L ss i s).mpr
  exact section_zero_on_cut L ss (List.mem_of_mem_drop hs)

end M9Native.LineSectionPrefixes
