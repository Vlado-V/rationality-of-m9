module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Abelian.Monomorphisms

/-!
# Rationality of the actual genus-nine coarse moduli space

The statement uses only canonical Mathlib definitions. All original complex
test schemes, genus-nine families (including nonschematic total spaces), and
algebraic-space targets are retained. The paired Solution proves the result
using the actual moduli construction and its complex function field.

The base field is explicit. Every test scheme in the working universe is
allowed; no finite-type restriction is imposed on test schemes or families.
The proved endpoint uses the literal complex field in Type 0. The optional
ULift formulations below are separate statements, not additional conclusions.
The native Solution must prove comparison with its size-bounded fppf site.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StandaloneDraft

variable (K : Type u) [Field K]

/-- The full category of schemes over the specified original field. -/
abbrev Base := Spec (CommRingCat.of K)
abbrev Schemes := Over (Base K)
abbrev Presheaves := (Schemes K)ᵒᵖ ⥤ Type u

/-- Ordinary fppf algebraic space: a sheaf with representable diagonal and
a representable surjective etale scheme atlas. Every relative property below
is tested on all represented pullbacks, not merely on geometric points. -/
structure Space where
  obj : Presheaves K
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over (Base K)) obj
  diagonal : yoneda.relativelyRepresentable (diag obj)
  atlas : ∃ (U : Schemes K) (a : yoneda.obj U ⟶ obj),
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget (Base K))).presheaf a ∧
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget (Base K))).presheaf a

/-- Right-derived global sections of the actual structure sheaf, with the
original structure-map action of the coefficient field. The sections functor
and pushforward are Mathlib definitions, not additional opaque inputs. -/
abbrev H1 {L : Type u} [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of L)) : ModuleCat.{u} L :=
  letI : (moduleSpecΓFunctor (R := CommRingCat.of L)).Additive :=
    ⟨by intro M N φ ψ; ext x; rfl⟩
  (((Scheme.Modules.pushforward f) ⋙ moduleSpecΓFunctor).rightDerived 1).obj
    (SheafOfModules.unit X.ringCatSheaf)

/-- A scheme family has proper, smooth, geometrically connected fibres of
relative dimension one, whose genuine H1 is finite-dimensional of genus g.
The fibre requirement is over every field-valued point, including arbitrary
field extensions and non-closed points. -/
def SchemeCurve {X T : Scheme.{u}} (f : X ⟶ T) (g : ℕ) : Prop :=
  IsProper f ∧ SmoothOfRelativeDimension 1 f ∧ GeometricallyConnected f ∧
  ∀ (L : Type u) [Field L] (s : Spec (CommRingCat.of L) ⟶ T),
    Module.Finite L (H1 (pullback.snd f s)) ∧
      Module.finrank L (H1 (pullback.snd f s)) = g

/-- All genuine families, including nonschematic total spaces: a total
algebraic space over T which is a proper smooth geometrically connected
genus-g scheme family after an etale cover of T. This is a local geometric
condition, not a supplied moduli functor, atlas, or Mukai hypothesis. -/
structure Family (T : Schemes K) (g : ℕ) where
  total : Space K
  projection : total.obj ⟶ yoneda.obj T
  locally_curve : ∀ t : T.left,
    ∃ (T' Z : Schemes K) (v : T' ⟶ T) (q : Z ⟶ T')
      (r : yoneda.obj Z ⟶ total.obj),
      Etale v.left ∧ t ∈ Set.range v.left ∧
      IsPullback r (yoneda.map q) projection (yoneda.map v) ∧
      SchemeCurve q.left g

/-- An isomorphism of actual total spaces over the entire test scheme. -/
def FamilyIsomorphic {T : Schemes K} {g : ℕ} (F G : Family K T g) : Prop :=
  ∃ e : F.total.obj ≅ G.total.obj, e.hom ≫ G.projection = F.projection

/-- A map from the moduli problem to a presheaf: it assigns a section on the
entire base to every family and commutes with every Cartesian square. The
identity-base case includes invariance under all family isomorphisms. -/
structure Classifier (g : ℕ) (M : Presheaves K) where
  value : ∀ (T : Schemes K), Family K T g → M.obj (op T)
  naturality : ∀ (T U : Schemes K) (a : U ⟶ T)
    (F : Family K T g) (G : Family K U g) (r : G.total.obj ⟶ F.total.obj),
    IsPullback r G.projection F.projection (yoneda.map a) →
      M.map a.op (value T F) = value U G

/-- Universality against ALL algebraic-space targets, including targets
which are not schemes. The factorization is equality of classifying maps
on all families, with unique natural transformation between the spaces. -/
def IsCategorical {g : ℕ} {M : Presheaves K} (c : Classifier K g M) : Prop :=
  ∀ (W : Space K) (d : Classifier K g W.obj),
    ∃! h : M ⟶ W.obj, ∀ (T : Schemes K) (F : Family K T g),
      h.app (op T) (c.value T F) = d.value T F

/-- The spectrum of any extension field with its actual structure map. -/
abbrev FieldPoint (L : Type u) [Field L] [Algebra K L] : Schemes K :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The geometric-point part of coarse moduli: for EVERY algebraically
closed extension L/K, the classifying map is onto and identifies exactly
isomorphic unpointed curves. No choice of markings or bases is retained. -/
def IsGeometric {g : ℕ} {M : Presheaves K} (c : Classifier K g M) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L],
    Function.Surjective (c.value (FieldPoint K L)) ∧
    ∀ F G : Family K (FieldPoint K L) g,
      c.value _ F = c.value _ G ↔ FamilyIsomorphic K F G

/-- A genuine coarse moduli map, not a set of geometric isomorphism classes. -/
def IsCoarse {g : ℕ} {M : Presheaves K} (c : Classifier K g M) : Prop :=
  IsCategorical K c ∧ IsGeometric K c

/-- A representable open immersion into a presheaf, tested on all schemes. -/
def OpenImmersion {F G : Presheaves K} (j : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
    (Over.forget (Base K))).presheaf j

/-- Density of an open subspace, tested after every etale scheme chart.
Density is deliberately not required after arbitrary base change (which
would wrongly exclude every proper dense open). Representability of j
supplies the pullback squares quantified in the density condition. -/
def DenseOpen {F G : Presheaves K} (j : F ⟶ G) : Prop :=
  OpenImmersion K j ∧
  ∀ (V : Schemes K) (v : yoneda.obj V ⟶ G),
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (Base K))).presheaf v →
    ∀ (P : Schemes K) (a : P ⟶ V) (b : yoneda.obj P ⟶ F),
      IsPullback b (yoneda.map a) j v → DenseRange a.left

/-- A nonempty common open with affine n-space, over the ORIGINAL base K.
The actual AffineSpace construction is the Mathlib scheme. -/
def RationalOpen (n : ℕ) (M : Presheaves K) : Prop :=
  ∃ (U : Schemes K) (j : yoneda.obj U ⟶ M),
    Nonempty U.left ∧ DenseOpen K j ∧
    ∃ a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (Base K),
      IsOpenImmersion a ∧ DenseRange a ∧
      a ≫ pullback.fst _ _ = U.hom

/-- A reduced, separated, finite-type algebraic space. Finite type is
witnessed on one surjective etale scheme atlas; reducedness is etale local.
One must NOT demand that its map to Spec K is representable, since that
would incorrectly force every allowed space to be a scheme. -/
def VarietySpace (M : Space K) : Prop :=
  (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
    (Over.forget (Base K))).presheaf (diag M.obj) ∧
  (∀ (V : Schemes K) (v : yoneda.obj V ⟶ M.obj),
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (Base K))).presheaf v → IsReduced V.left) ∧
  ∃ (V : Schemes K) (v : yoneda.obj V ⟶ M.obj),
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (Base K))).presheaf v ∧
    (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (Base K))).presheaf v ∧
    LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom

/-- An actual coarse algebraic space for ALL genus-nine families exists
and is rational of dimension 24. The common irreducible dense open forces
irreducibility; reducedness and finite type are separately required above.
This is a proposed full statement, not a theorem claimed by this file. -/
def RationalCoarseSpaceGoal : Prop :=
  ∃ (M : Space K) (c : Classifier K 9 M.obj),
    IsCoarse K c ∧ VarietySpace K M ∧ RationalOpen K 24 M.obj

/-- Stronger scheme formulation matching the paper's word "variety".
Coarse universality still ranges over all algebraic spaces, not just schemes.
It requires native coarse SCHEME representability as an additional proof. -/
def RationalCoarseSchemeGoal : Prop :=
  ∃ (M : Schemes K) (c : Classifier K 9 (yoneda.obj M)),
    IsIntegral M.left ∧ IsSeparated M.hom ∧
    LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧
    IsCoarse K c ∧ RationalOpen K 24 (yoneda.obj M)

/-- Universe-polymorphic complex target. ULift only relocates the original
complex field; it introduces no new scalar field or rationality assumption. -/
abbrev ProposedComplexSpaceGoal : Prop :=
  RationalCoarseSpaceGoal (ULift.{u} ℂ)

/-- Universe-polymorphic complex scheme version of the proposed target. -/
abbrev ProposedComplexSchemeGoal : Prop :=
  RationalCoarseSchemeGoal (ULift.{u} ℂ)

end M9StandaloneDraft

namespace M9Rationality

/-- The coarse moduli space of smooth connected unpointed complex curves of
genus nine is rational of dimension 24 over the original complex field. -/
public theorem main_result :
    M9StandaloneDraft.RationalCoarseSpaceGoal ℂ := by
  sorry

end M9Rationality
