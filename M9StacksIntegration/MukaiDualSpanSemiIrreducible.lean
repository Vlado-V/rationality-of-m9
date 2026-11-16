module

public import M9StacksIntegration.MukaiSemiConstruction
public import M9StacksIntegration.MukaiPencilGeometry
public import M9StacksIntegration.MukaiLemmaFiveOne

/-!
# Mukai Proposition 5.3 for the actual nonsplit dual-span extension

The input is the original short exact sequence of actual native
sheaves with its actual Gamma-splitting. The two actual degree-eight
net line bundles have their actual canonical residual isomorphism.
Native pencil geometry constructs the degree-two/degree-six sequence
and both original evaluation epimorphisms. The original extension is
globally generated and has six sections by native H0 exactness. The
proved original-image saturation argument then establishes the exact
native complete semi-irreducibility predicate.

No semi-irreducibility, rank of E, section count, global generation,
auxiliary divisor, filtration, determinant-section bound, or
image-saturation equality is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiDualSpanSemiIrreducible

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The original nonsplit Gamma-split dual-span extension has a free,
semi-irreducible complete native rank-three system, with any original
complete basis of the actual degree-eight net. -/
theorem free_and_semiIrreducible_for_complete_basis
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A B : LinearSeries k f hdim 8 2)
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f B.L 0))
    (e : MukaiBundleDeterminant.tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f)
    (E : X.Modules)
    (i : dualSpan B.L (completeNetSections f B.L bβ) ⟶ E)
    (p : E ⟶ A.L) (w : i ≫ p = 0)
    (hT : (ShortComplex.mk i p w).ShortExact)
    (hnonsplit : ∀ t : A.L ⟶ E, t ≫ p ≠ 𝟙 _)
    (hγ : Function.Surjective (_root_.SheafOfModules.sectionsMap p)) :
    MukaiSemiIrreducible.GloballyGenerated E ∧
      MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 := by
  let := A.isInvertible
  let := B.isInvertible
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f hdim hg hnp
  obtain ⟨D,hD,hDdim,hlen,bξ,hξdegree,hξ0,hξepi,hβepi⟩ :=
    MukaiPencilGeometry.exists_completePencilData f hdim hg hnp B bβ
  let := hD
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let Q := dualSpan B.L (completeNetSections f B.L bβ)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2 :=
    dualSpan_rank B.L (completeNetSections f B.L bβ) hβepi
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A.L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X A.L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 :=
    extension_rank (ShortComplex.mk i p w) hT 2 1 inferInstance inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  let : FiniteDimensional k (cohomologyOverField k f E 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 0
  let : FiniteDimensional k (cohomologyOverField k f Q 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f Q 0
  let : FiniteDimensional k (cohomologyOverField k f A.L 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f A.L
  have hQ0 := (MukaiLemmaFiveOne.lemma_five_one_for_complete_basis
    f hdim hg hnp B bβ A.L A.degree_eq).1
  have hA0 := (MukaiNoDegreeSevenNet.degree_eight_net_h0_eq_three_and_complete
    f hdim hg hnp A).1
  have h6 := finrank_H0_of_gammaSplit k f hT hγ
  change Module.finrank k (cohomologyOverField k f E 0) =
    Module.finrank k (cohomologyOverField k f Q 0) +
      Module.finrank k (cohomologyOverField k f A.L 0) at h6
  rw [hQ0,hA0] at h6
  norm_num at h6
  have hQgen : MukaiSemiIrreducible.GloballyGenerated Q :=
    MukaiSemiIrreducible.dualSpan_globallyGenerated B.L (completeNetSections f B.L bβ) hβepi
  let bα := MukaiLemmaFiveOne.completeNetBasis f hdim hg hnp A
  have hαepi := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi
    f hdim hno7 A bα
  have hAgen : MukaiSemiIrreducible.GloballyGenerated A.L :=
    ⟨⟨ULift.{u} (Fin 3),completeNetSections f A.L bα,hαepi⟩⟩
  have hEgen := MukaiSemiIrreducible.globallyGenerated_extension (ShortComplex.mk i p w)
    hT hγ hQgen hAgen
  let S := MukaiPencilQuotient.completePencilSequence f D B.L bξ bβ hξepi hβepi
  have hS := MukaiPencilQuotient.completePencilSequence_shortExact f D B.L bξ bβ hξepi hβepi
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁ := by
    change SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (Stacks.Divisors.divisorSheaf D)
    exact Stacks.Divisors.invertibleSheaf_isInvertible D
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃ := by
    change SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (CurveDivisorSections.twistDown D B.L)
    exact CurveDivisorSections.twistDown_isInvertible D B.L
  let : FiniteDimensional k (cohomologyOverField k f S.X₁ 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f S.X₁
  have hDdegree : invertibleCurveDegree k f hdim S.X₁ = 2 := by
    have hd := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
    change invertibleCurveDegree k f hdim S.X₁ =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) at hd
    rw [hlen] at hd
    exact hd
  refine ⟨hEgen,?_⟩
  exact MukaiSemiConstruction.completeSemiIrreducible_of_no_pencil
    k f hdim hnp S hS hQgen hDdegree hξdegree E A.L i p w hT hnonsplit A.degree_eq
    hEgen B.L B.degree_eq e hg h6

/-- The complete net basis is constructed from the original native
degree-eight net, with no basis-existence or semirreducibility premise. -/
theorem free_and_semiIrreducible
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A B : LinearSeries k f hdim 8 2)
    (e : MukaiBundleDeterminant.tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f)
    (E : X.Modules)
    (i : dualSpan B.L (completeNetSections f B.L (MukaiLemmaFiveOne.completeNetBasis f hdim hg hnp B)) ⟶ E)
    (p : E ⟶ A.L) (w : i ≫ p = 0)
    (hT : (ShortComplex.mk i p w).ShortExact)
    (hnonsplit : ∀ t : A.L ⟶ E, t ≫ p ≠ 𝟙 _)
    (hγ : Function.Surjective (_root_.SheafOfModules.sectionsMap p)) :
    MukaiSemiIrreducible.GloballyGenerated E ∧
      MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 :=
  free_and_semiIrreducible_for_complete_basis f hdim hg hnp A B
    (MukaiLemmaFiveOne.completeNetBasis f hdim hg hnp B) e E i p w hT hnonsplit hγ

end M9Native.MukaiDualSpanSemiIrreducible
