module

public import M9StacksIntegration.MukaiBundle
public import M9StacksIntegration.CurveDivisorSections
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Pullback

/-!
# The actual rank-two preimage of a line in the quotient

The preimage is the literal categorical pullback `E ×_G L`. Its original
kernel and projection give the induced short exact sequence. The two
invertible ends prove rank two. Two actual line sections whose images
lift to E lift further to the pullback; exactness at H⁰ then adds their
two-dimensional image to the two-dimensional kernel contribution.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace M9Native.MukaiRankTwoPreimage

variable {X : Scheme.{u}}

/-- The actual inverse image of the original line morphism. -/
def preimage (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) : X.Modules :=
  pullback S.g j

def inclusion (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) :
    preimage S j ⟶ S.X₂ := pullback.fst S.g j

def projection (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) :
    preimage S j ⟶ L := pullback.snd S.g j

def kernelMap (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) :
    S.X₁ ⟶ preimage S j := pullback.lift S.f 0 (by rw [S.zero, zero_comp])

@[reassoc (attr := simp)] theorem kernelMap_inclusion
    (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) :
    kernelMap S j ≫ inclusion S j = S.f := by simp [kernelMap, inclusion]

@[reassoc (attr := simp)] theorem kernelMap_projection
    (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) :
    kernelMap S j ≫ projection S j = 0 := by simp [kernelMap, projection]

@[reassoc] theorem inclusion_condition (S : ShortComplex X.Modules)
    {L : X.Modules} (j : L ⟶ S.X₃) : inclusion S j ≫ S.g = projection S j ≫ j :=
  pullback.condition

instance inclusion_mono (S : ShortComplex X.Modules) {L : X.Modules}
    (j : L ⟶ S.X₃) [Mono j] : Mono (inclusion S j) := by
  dsimp [inclusion]
  infer_instance

/-- The literal induced sequence, with no separate exactness premise. -/
def sequence (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃) :
    ShortComplex X.Modules :=
  ShortComplex.mk (kernelMap S j) (projection S j) (kernelMap_projection S j)

/-- The original short exact sequence proves exactness of its actual
preimage sequence. Only the orientation of the categorical pullback
differs from Mathlib's native construction. -/
theorem sequence_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {L : X.Modules} (j : L ⟶ S.X₃) : (sequence S j).ShortExact := by
  let e : S.pull j ≅ sequence S j :=
    ShortComplex.isoMk (Iso.refl _) (pullbackSymmetry j S.g) (Iso.refl _)
      (by
        dsimp [sequence, kernelMap]
        apply pullback.hom_ext <;> simp)
      (by simp [sequence, projection])
  exact (ShortComplex.shortExact_iff_of_iso e).mp (hS.pull j)

/-- Two actual invertible ends prove that the original pullback is a
finite locally free sheaf of rank two. -/
theorem rank_two (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {L : X.Modules} (j : L ⟶ S.X₃)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (preimage S j) 2 := by
  exact MukaiBundle.extension_rank (sequence S j) (sequence_shortExact S hS j) 1 1
    (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X S.X₁)
    (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L)

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- The actual structure-sheaf Hom and H⁰ bijection, using exactly the
native comparison and ordinary global sections. No alternate H⁰ map is
introduced into the resulting lifting statement. -/
def unitHomH0Equiv (F : X.Modules) :
    (MukaiBundle.structureModule X ⟶ F) ≃ cohomologyOverField k f F 0 :=
  F.unitHomEquiv.trans ((Stacks.NonvanishingSpelling.sectionsEquiv X F).trans
    (cohomologyOverFieldZeroEquivSections k f F).symm)

theorem unitHomH0Equiv_naturality {F G : X.Modules}
    (a : MukaiBundle.structureModule X ⟶ F) (q : F ⟶ G) :
    unitHomH0Equiv f G (a ≫ q) = cohomologyOverFieldMap k f q 0 (unitHomH0Equiv f F a) := by
  apply (cohomologyOverFieldZeroEquivSections k f G).injective
  simp only [unitHomH0Equiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap]
  rfl

/-- Actual compatible H⁰ classes lift to the actual categorical pullback,
with both original projections pinned. No cohomological-surjectivity
assumption is made. -/
theorem exists_lift_H0 (S : ShortComplex X.Modules) {L : X.Modules} (j : L ⟶ S.X₃)
    (e : cohomologyOverField k f S.X₂ 0) (s : cohomologyOverField k f L 0)
    (h : cohomologyOverFieldMap k f S.g 0 e = cohomologyOverFieldMap k f j 0 s) :
    ∃ t : cohomologyOverField k f (preimage S j) 0,
      cohomologyOverFieldMap k f (inclusion S j) 0 t = e ∧
        cohomologyOverFieldMap k f (projection S j) 0 t = s := by
  let a := (unitHomH0Equiv f S.X₂).symm e
  let b := (unitHomH0Equiv f L).symm s
  have hab : a ≫ S.g = b ≫ j := by
    apply (unitHomH0Equiv f S.X₃).injective
    rw [unitHomH0Equiv_naturality, unitHomH0Equiv_naturality]
    simpa only [a, b, Equiv.apply_symm_apply] using h
  let t : MukaiBundle.structureModule X ⟶ preimage S j := pullback.lift a b hab
  refine ⟨unitHomH0Equiv f _ t, ?_, ?_⟩
  · rw [← unitHomH0Equiv_naturality]
    change unitHomH0Equiv f S.X₂ (pullback.lift a b hab ≫ pullback.fst S.g j) = e
    rw [pullback.lift_fst]
    exact (unitHomH0Equiv f S.X₂).apply_symm_apply e
  · rw [← unitHomH0Equiv_naturality]
    change unitHomH0Equiv f L (pullback.lift a b hab ≫ pullback.snd S.g j) = s
    rw [pullback.lift_snd]
    exact (unitHomH0Equiv f L).apply_symm_apply s

/-- Finiteness of actual H⁰ of the preimage follows from its proved rank
two and properness, rather than being supplied as a dimension premise. -/
theorem finite_H0 [IsProper f] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {L : X.Modules} (j : L ⟶ S.X₃)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    Module.Finite k (cohomologyOverField k f (preimage S j) 0) := by
  let : IsLocallyNoetherian X :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k f
  let hP := rank_two S hS j
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (preimage S j) := hP.isFiniteLocallyFree
  let : (preimage S j).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X (preimage S j)
  exact finiteDimensional_cohomologyOverField_of_isProper k f (preimage S j) 0

/-- The actual kernel H⁰ contribution plus independent quotient
sections in the original E-image bound H⁰ of the actual preimage. -/
theorem finrank_H0_ge [IsProper f] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {L : X.Modules} (j : L ⟶ S.X₃)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (a b : ℕ) (hη : a ≤ Module.finrank k (cohomologyOverField k f S.X₁ 0))
    (s : Fin b → cohomologyOverField k f L 0) (hs : LinearIndependent k s)
    (hlift : ∀ i, cohomologyOverFieldMap k f j 0 (s i) ∈
      LinearMap.range (cohomologyOverFieldMap k f S.g 0).hom) :
    a + b ≤ Module.finrank k (cohomologyOverField k f (preimage S j) 0) := by
  let := CurveDivisorSections.invertible_cohomology_zero_finite f S.X₁
  let := CurveDivisorSections.invertible_cohomology_zero_finite f L
  let := finite_H0 f S hS j
  let u := (cohomologyOverFieldMap k f (kernelMap S j) 0).hom
  let v := (cohomologyOverFieldMap k f (projection S j) 0).hom
  obtain ⟨_, hi, he, _, _⟩ :=
    exists_cohomologyOverField_longExactSequence k f (sequence_shortExact S hS j)
  have hu : Function.Injective u := hi
  have huv : Function.Exact u v := he 0
  have hmem (i : Fin b) : s i ∈ LinearMap.range v := by
    obtain ⟨e, he⟩ := hlift i
    obtain ⟨t, _, ht⟩ := exists_lift_H0 f S j e (s i) he
    exact ⟨t, ht⟩
  let z : Fin b → LinearMap.range v := fun i => ⟨s i, hmem i⟩
  have hz : LinearIndependent k z := by
    apply LinearIndependent.of_comp (LinearMap.range v).subtype
    change LinearIndependent k s
    exact hs
  have hb : b ≤ Module.finrank k (LinearMap.range v) := by
    simpa only [Fintype.card_fin] using hz.fintype_card_le_finrank
  have hker : Module.finrank k (LinearMap.ker v) =
      Module.finrank k (cohomologyOverField k f S.X₁ 0) := by
    rw [huv.linearMap_ker_eq, LinearMap.finrank_range_of_inj hu]
  have hdim := v.finrank_range_add_finrank_ker
  omega

/-- The genuine two-plus-two lifting step used by Mukai Proposition 5.3.
The induced sequence and rank of P are proved from the original sequence;
its four sections come from the original independent sections and their
actual membership in the original H⁰-image. -/
theorem rank_two_with_four_sections [IsProper f]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {L : X.Modules}
    (j : L ⟶ S.X₃) [Mono j]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (t : Fin 2 → cohomologyOverField k f S.X₁ 0) (ht : LinearIndependent k t)
    (s : Fin 2 → cohomologyOverField k f L 0) (hs : LinearIndependent k s)
    (hlift : ∀ i, cohomologyOverFieldMap k f j 0 (s i) ∈
      LinearMap.range (cohomologyOverFieldMap k f S.g 0).hom) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (preimage S j) 2 ∧
      4 ≤ Module.finrank k (cohomologyOverField k f (preimage S j) 0) := by
  let := CurveDivisorSections.invertible_cohomology_zero_finite f S.X₁
  have hη : 2 ≤ Module.finrank k (cohomologyOverField k f S.X₁ 0) := by
    simpa only [Fintype.card_fin] using ht.fintype_card_le_finrank
  exact ⟨rank_two S hS j, finrank_H0_ge f S hS j 2 2 hη s hs hlift⟩

end M9Native.MukaiRankTwoPreimage
