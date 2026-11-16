module

public import M9StacksIntegration.LagrangianIntegral
public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.LagrangianLinearSections
public import M9StacksIntegration.HyperplaneCoefficientIndependence
public import M9StacksIntegration.SplitMatrixGrassmannian
public import M9StacksIntegration.IteratedLineSectionCuts
public import M9StacksIntegration.LagrangianHyperplaneCoordinates
public import M9StacksIntegration.LagrangianHyperplaneRows
public import M9StacksIntegration.IntegralLineSectionCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmoothIrreducibleMember
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionEquality

/-!
# Five genuine smooth integral hyperplane cuts of the actual native LG

The same original fourteen-dimensional linear system is retained through
actual pullback. Each actual new cut has a nonzero restricted section, so
its original coefficient vector lies outside the span of the previous
ones. Independence and the actual rank-five Grassmannian point are
conclusions of the construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Bertini

universe u

namespace M9Native.SmoothIntegralHyperplaneCuts

variable (D : FamilyDivisors.{u,u})

/-- A genuine successive-cut state, retaining its actual closed map to
the original scheme and its original coefficient vectors. -/
structure CutState (d r : ℕ) where
  X : Scheme.{u}
  toRoot : X ⟶ D.X
  closed : IsClosedImmersion toRoot
  smooth : Smooth (toRoot ≫ D.toBase)
  integral : IsIntegral X
  dimension : topologicalKrullDim X = (d : WithBot ℕ∞)
  coefficients : Fin r → D.V
  vanish : ∀ j, (D.pullbackAlong toRoot).sectionOf (coefficients j) = 0
  independent : LinearIndependent D.k coefficients
  factorization : ∀ {T : Scheme.{u}} (f : T ⟶ D.X),
    (∃ g : T ⟶ X, g ≫ toRoot = f) ↔
      ∀ j, pullbackGlobalSections f D.L (D.sectionOf (coefficients j)) = 0

abbrev currentSystem {d r : ℕ} (S : CutState D d r) : FamilyDivisors.{u,u} :=
  D.pullbackAlong S.toRoot

/-- Actual restriction along a composite uses the actual native
pullback-composition isomorphism on the original line. -/
theorem sectionOf_comp {X Z : Scheme.{u}} (f : X ⟶ D.X) (g : Z ⟶ X) (v : D.V) :
    (D.pullbackAlong (g ≫ f)).sectionOf v =
      ((Scheme.Modules.pullbackComp g f).hom.app D.L).app ⊤
        (pullbackGlobalSections g (D.pullbackAlong f).L
          ((D.pullbackAlong f).sectionOf v)) :=
  (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp g f D.L (D.sectionOf v)).symm

/-- Genuine vanishing of a section persists through an actual further restriction. -/
theorem sectionOf_comp_eq_zero {X Z : Scheme.{u}} (f : X ⟶ D.X) (g : Z ⟶ X) (v : D.V)
    (h : pullbackGlobalSections g (D.pullbackAlong f).L ((D.pullbackAlong f).sectionOf v) = 0) :
    (D.pullbackAlong (g ≫ f)).sectionOf v = 0 := by
  rw [sectionOf_comp D f g v, h, map_zero]

/-- The actual zero-scheme inclusion annihilates its defining actual section. -/
theorem sectionOf_zero_on_divisor (v : D.V) :
    pullbackGlobalSections (D.divisor v).subschemeι D.L (D.sectionOf v) = 0 :=
  (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme D.X D.L
    (D.sectionOf v) (D.divisor v).subschemeι).mpr ⟨𝟙 _, by
      simp only [Category.id_comp]
      rfl⟩

section Successor
variable [IsAlgClosed D.k] [IsProper D.toBase]

/-- Native Bertini and native Cartier dimension drop produce a genuine
next cut; its original vector is proved independent of earlier equations. -/
theorem exists_next (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    ∃ v : D.V, (currentSystem D S).sectionOf v ≠ 0 ∧
      Smooth (((currentSystem D S).divisor v).subschemeι ≫ (currentSystem D S).toBase) ∧
      IsIntegral ((currentSystem D S).divisor v).subscheme ∧
      topologicalKrullDim ((currentSystem D S).divisor v).subscheme =
        ((d+1 : ℕ) : WithBot ℕ∞) ∧
      v ∉ Submodule.span D.k (Set.range S.coefficients) := by
  let E := currentSystem D S
  let : IsClosedImmersion S.toRoot := S.closed
  let : Smooth E.toBase := S.smooth
  let : IsIntegral E.X := S.integral
  let : IsAlgClosed E.k := (inferInstance : IsAlgClosed D.k)
  let : IsProper E.toBase := by
    change IsProper (S.toRoot ≫ D.toBase)
    infer_instance
  have hegen : E.Generates :=
    FamilyDivisors.generates_pullbackAlong (D := D) S.toRoot hgen
  have heimm (m : ℕ) (b : Module.Basis (Fin (m+1)) E.k E.V) :
      E.IsImmersive b (E.generatesBy_basis hegen b) :=
    FamilyDivisors.isImmersive_pullbackAlong (D := D) S.toRoot (himm m b)
  have htwo : (2 : WithBot ℕ∞) ≤ topologicalKrullDim E.X := by
    rw [show topologicalKrullDim E.X = ((d+2 : ℕ) : WithBot ℕ∞) from S.dimension]
    exact_mod_cast (show 2 ≤ d+2 by omega)
  obtain ⟨v, hv, hsm, hirr⟩ := E.exists_smooth_irreducibleSpace_divisor hegen heimm htwo
  let := hsm
  let := hirr
  have hint : IsIntegral (E.divisor v).subscheme :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth ((E.divisor v).subschemeι ≫ E.toBase)
  let : Nonempty (Stacks.Divisors.zeroScheme E.X E.L (E.sectionOf v)).subscheme :=
    (inferInstance : Nonempty (E.divisor v).subscheme)
  have hdim : topologicalKrullDim (E.divisor v).subscheme = ((d+1 : ℕ) : WithBot ℕ∞) :=
    Stacks.Chow.topologicalKrullDim_zeroScheme_eq_of_ne_zero E.toBase E.L (E.sectionOf v) hv
      (by
        change topologicalKrullDim S.X = ((d+1+1 : ℕ) : WithBot ℕ∞)
        simpa only [Nat.add_assoc] using S.dimension)
  have hnot : v ∉ Submodule.span D.k (Set.range S.coefficients) := by
    intro hmem
    have hspan : Submodule.span D.k (Set.range S.coefficients) ≤ LinearMap.ker E.ψ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact S.vanish j
    exact hv (hspan hmem)
  exact ⟨v, hv, hsm, hint, hdim, hnot⟩

/-- Actual original coefficients chosen from the proved native Bertini locus. -/
def nextCoefficients (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) : D.V :=
  Classical.choose (exists_next D hgen himm S)

/-- The actual next divisor, retaining the genuine zero ideal and its
defining nonzero restricted original section. -/
def nextDivisor (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) : S.X.IdealSheafData :=
  (currentSystem D S).divisor (nextCoefficients D hgen himm S)

theorem nextDivisor_section_ne_zero (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    (currentSystem D S).sectionOf (nextCoefficients D hgen himm S) ≠ 0 :=
  (Classical.choose_spec (exists_next D hgen himm S)).1

/-- The actual chosen cut is an effective Cartier divisor, because its
actual restricted section is nonzero on the actual integral prefix. -/
theorem nextDivisor_cartier (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    Stacks.Divisors.IsEffectiveCartierDivisor (nextDivisor D hgen himm S) := by
  let : IsIntegral (currentSystem D S).X := S.integral
  exact IntegralLineSectionCartier.cartier (currentSystem D S).L
    ((currentSystem D S).sectionOf (nextCoefficients D hgen himm S))
    (nextDivisor_section_ne_zero D hgen himm S)

/-- The actual restricted original line is the actual divisor line of
the genuine chosen cut, rather than an assumed divisor class. -/
def nextDivisorLineIso (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    (currentSystem D S).L ≅ Stacks.Divisors.invertibleSheaf' (nextDivisor D hgen himm S) := by
  let : IsIntegral (currentSystem D S).X := S.integral
  exact IntegralLineSectionCartier.lineIso (currentSystem D S).L
    ((currentSystem D S).sectionOf (nextCoefficients D hgen himm S))
    (nextDivisor_section_ne_zero D hgen himm S)

/-- The original defining section becomes the actual Cartier canonical
section under the actual divisor-line isomorphism. -/
theorem nextDivisorLineIso_section (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    (nextDivisorLineIso D hgen himm S).hom.app ⊤
        ((currentSystem D S).sectionOf (nextCoefficients D hgen himm S)) =
      (Stacks.Divisors.canonicalSection' (nextDivisor D hgen himm S)).val (op ⊤) := by
  let : IsIntegral (currentSystem D S).X := S.integral
  exact IntegralLineSectionCartier.lineIso_section (currentSystem D S).L
    ((currentSystem D S).sectionOf (nextCoefficients D hgen himm S))
    (nextDivisor_section_ne_zero D hgen himm S)

/-- The successor is the actual zero scheme, and its original equations
are all proved to vanish there. -/
def nextState (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) : CutState D (d+1) (r+1) := by
  let E := currentSystem D S
  let v := nextCoefficients D hgen himm S
  let I := nextDivisor D hgen himm S
  have hs := Classical.choose_spec (exists_next D hgen himm S)
  refine {
    X := I.subscheme
    toRoot := I.subschemeι ≫ S.toRoot
    closed := ?_
    smooth := ?_
    integral := hs.2.2.1
    dimension := hs.2.2.2.1
    coefficients := Fin.snoc S.coefficients v
    vanish := ?_
    independent := ?_
    factorization := ?_ }
  · let : IsClosedImmersion S.toRoot := S.closed
    infer_instance
  · have hsm : Smooth (I.subschemeι ≫ (S.toRoot ≫ D.toBase)) := hs.2.1
    simpa only [Category.assoc] using hsm
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.snoc_last]
      exact sectionOf_comp_eq_zero D S.toRoot I.subschemeι v (sectionOf_zero_on_divisor E v)
    · rw [Fin.snoc_castSucc]
      apply sectionOf_comp_eq_zero
      rw [S.vanish k, map_zero]
  · exact S.independent.finSnoc hs.2.2.2.2
  · intro T f
    have hcut :
        (∃ g : T ⟶ I.subscheme, g ≫ (I.subschemeι ≫ S.toRoot) = f) ↔
          (∃ g : T ⟶ S.X, g ≫ S.toRoot = f) ∧
            pullbackGlobalSections f D.L (D.sectionOf v) = 0 :=
      IteratedLineSectionCuts.cut_factors_iff D.L f (Over.mk S.toRoot) (D.sectionOf v)
    rw [hcut, S.factorization f]
    constructor
    · rintro ⟨hold, hnew⟩ j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hnew
      · simpa using hold i
    · intro hall
      exact ⟨fun i => by simpa using hall i.castSucc,
        by simpa using hall (Fin.last r)⟩

/-- The actual inclusion of the next divisor into its original prefix. -/
def nextCutInclusion (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    (nextState D hgen himm S).X ⟶ S.X :=
  (nextDivisor D hgen himm S).subschemeι

@[reassoc]
theorem nextCutInclusion_comp (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m+1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {d r : ℕ} (S : CutState D (d+2) r) :
    nextCutInclusion D hgen himm S ≫ S.toRoot = (nextState D hgen himm S).toRoot := rfl

end Successor

section Lagrangian
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

abbrev initialSystem : FamilyDivisors.{u,u} :=
  Stacks.Bertini.ProjectiveSubscheme.family (LagrangianPlucker.primitivePlucker K)

omit [IsAlgClosed K] in
theorem initialSystem_toBase : (initialSystem K).toBase = LagrangianGrassmannian.projection K :=
  LagrangianPlucker.primitivePlucker_projection K

omit [IsAlgClosed K] in
/-- The native Bertini system uses the literal original fourteen
coordinates with the actual structural-map scalar convention. -/
theorem initialSystem_section (v : Fin 14 → K) :
    (initialSystem K).sectionOf v = LagrangianHyperplaneCoordinates.linearSection K v := by
  change (Fintype.linearCombination K
    (M := Stacks.Bertini.globalSections K (initialSystem K).toBase (initialSystem K).L)
    (LagrangianHyperplaneCoordinates.coordinateSection K) v) = _
  rw [Fintype.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Stacks.Bertini.globalSections, ModuleCat.restrictScalars.smul_def]
  congr 1
  exact (congrArg (fun f : LagrangianGrassmannian.space K ⟶ Spec (.of K) =>
    Stacks.Bertini.baseRingHom K f (v i)) (initialSystem_toBase K)).trans (by
      simp only [Stacks.Bertini.baseRingHom, LagrangianHyperplaneCoordinates.coefficientMap,
        LagrangianPlucker.coefficientMap, Category.id_comp]
      rfl)

instance initialSystem_proper : IsProper (initialSystem K).toBase := by
  have : IsProper (pullback.fst (terminal.from (Spec (.of K)))
      (terminal.from (projectiveSpaceAtUniverse.{u} 13))) :=
    isProper_projectiveSpaceOver 13 (Spec (.of K))
  infer_instance

instance initialSystem_smooth : Smooth (initialSystem K).toBase := by
  change Smooth (LagrangianPlucker.primitivePlucker K ≫ pullback.fst _ _)
  rw [LagrangianPlucker.primitivePlucker_projection]
  infer_instance

omit [IsAlgClosed K] in
theorem initialSystem_generates : (initialSystem K).Generates :=
  Stacks.Bertini.ProjectiveSubscheme.family_generates (LagrangianPlucker.primitivePlucker K)

omit [IsAlgClosed K] in
theorem initialSystem_immersive (m : ℕ)
    (b : Module.Basis (Fin (m+1)) (initialSystem K).k (initialSystem K).V) :
    (initialSystem K).IsImmersive b ((initialSystem K).generatesBy_basis
      (initialSystem_generates K) b) :=
  Stacks.Bertini.ProjectiveSubscheme.family_isImmersive (LagrangianPlucker.primitivePlucker K) m b

/-- On every actual prefix, the original native hyperplane restriction
is identified with the actual restriction of the original quotient determinant. -/
def originalRestrictionLineIso {d r : ℕ} (S : CutState (initialSystem K) d r) :
    (currentSystem (initialSystem K) S).L ≅
      (Scheme.Modules.pullback S.toRoot).obj (LagrangianPluckerQuotient.determinantLine K) :=
  (Scheme.Modules.pullback S.toRoot).mapIso (LagrangianHyperplaneCoordinates.lineIso K)

/-- The actual original determinant restriction is the actual divisor
line of the next genuine hyperplane cut. -/
def nextOriginalDivisorLineIso {d r : ℕ} (S : CutState (initialSystem K) (d+2) r) :
    (Scheme.Modules.pullback S.toRoot).obj (LagrangianPluckerQuotient.determinantLine K) ≅
      Stacks.Divisors.invertibleSheaf'
        (nextDivisor (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S) :=
  (originalRestrictionLineIso K S).symm ≪≫
    nextDivisorLineIso (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) S

def initialState : CutState (initialSystem K) 6 0 where
  X := LagrangianGrassmannian.space K
  toRoot := 𝟙 _
  closed := inferInstance
  smooth := by simpa only [Category.id_comp] using (inferInstance : Smooth (initialSystem K).toBase)
  integral := inferInstance
  dimension := LagrangianIntegral.space_dimension K
  coefficients := Fin.elim0
  vanish := by intro j; exact Fin.elim0 j
  independent := linearIndependent_empty_type
  factorization := by
    intro T f
    constructor
    · intro _ j
      exact Fin.elim0 j
    · intro _
      exact ⟨f, by simp⟩

def firstState : CutState (initialSystem K) 5 1 :=
  nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) (d := 4) (initialState K)
def secondState : CutState (initialSystem K) 4 2 :=
  nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) (d := 3) (firstState K)
def thirdState : CutState (initialSystem K) 3 3 :=
  nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) (d := 2) (secondState K)
def fourthState : CutState (initialSystem K) 2 4 :=
  nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) (d := 1) (thirdState K)
def fifthState : CutState (initialSystem K) 1 5 :=
  nextState (initialSystem K) (initialSystem_generates K) (initialSystem_immersive K) (d := 0) (fourthState K)

abbrev fiveCutCurve : Scheme.{u} := (fifthState K).X
abbrev fiveCutToLG : fiveCutCurve K ⟶ LagrangianGrassmannian.space K := (fifthState K).toRoot

theorem fiveCutCurve_integral : IsIntegral (fiveCutCurve K) := (fifthState K).integral

theorem fiveCutCurve_connected : ConnectedSpace (fiveCutCurve K) := by
  let := fiveCutCurve_integral K
  infer_instance

theorem fiveCutCurve_smooth : Smooth (fiveCutToLG K ≫ (initialSystem K).toBase) :=
  (fifthState K).smooth

theorem fiveCutCurve_dimension : topologicalKrullDim (fiveCutCurve K) = (1 : WithBot ℕ∞) :=
  (fifthState K).dimension

/-- The actual five-cut curve is the simultaneous zero scheme of its
five original sections on every test scheme, with scheme structure retained. -/
theorem fiveCut_factors_iff {T : Scheme.{u}}
    (f : T ⟶ LagrangianGrassmannian.space K) :
    (∃ g : T ⟶ fiveCutCurve K, g ≫ fiveCutToLG K = f) ↔
      ∀ j, pullbackGlobalSections f (initialSystem K).L
        ((initialSystem K).sectionOf ((fifthState K).coefficients j)) = 0 :=
  (fifthState K).factorization f

abbrev coefficientMatrix : Matrix (Fin 5) (Fin 14) K := (fifthState K).coefficients

/-- The actual five-cut scheme represents the simultaneous vanishing
of the five original determinant sections, on every test scheme. -/
theorem fiveCut_factors_iff_determinantSection {T : Scheme.{u}}
    (f : T ⟶ LagrangianGrassmannian.space K) :
    (∃ g : T ⟶ fiveCutCurve K, g ≫ fiveCutToLG K = f) ↔
      ∀ j, pullbackGlobalSections f (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (coefficientMatrix K j)) = 0 := by
  rw [fiveCut_factors_iff]
  apply forall_congr'
  intro j
  rw [initialSystem_section]
  exact LagrangianHyperplaneCoordinates.pullback_linearSection_zero_iff K f _

theorem coefficientMatrix_independent : LinearIndependent K (coefficientMatrix K) :=
  (fifthState K).independent

theorem coefficientMatrix_surjective : Function.Surjective (Matrix.mulVec (coefficientMatrix K)) :=
  (coefficientMatrix_independent K).mulVec_surjective

/-- The actual rank-five quotient point of the original universal parameter scheme. -/
def parameterPoint : Spec (.of K) ⟶ LagrangianLinearSections.parameter K :=
  SplitMatrixGrassmannian.fieldPoint 9 14 K (coefficientMatrix K) (coefficientMatrix_surjective K)

theorem parameterPoint_projection : parameterPoint K ≫ LagrangianLinearSections.parameterProjection K = 𝟙 _ :=
  SplitMatrixGrassmannian.fieldPoint_projection 9 14 K (coefficientMatrix K) (coefficientMatrix_surjective K)

end Lagrangian

end M9Native.SmoothIntegralHyperplaneCuts
