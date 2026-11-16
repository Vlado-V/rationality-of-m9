module

public import M9StacksIntegration.LagrangianFundamentalClasses
public import M9StacksIntegration.FlagTowerProper
public import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ChowSteps

/-!
# Fundamental classes on the two actual flag towers over Gr(3,6)

The full flag of the original universal rank-three quotient and the
three-step flag of the original free rank-six sheaf are the two native
descriptions of the same flag scheme.  Their fundamental classes are
constructed by the three actual flat projective-bundle pullbacks.
The native dimension bounds identify both constructions with the
identity-closed-subscheme class in degree twelve.  Proper pushforward
along the native flag isomorphism preserves these classes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow Stacks.FlagTower

universe u

namespace M9Native.LagrangianFlagFundamentalTransport

/-- The actual class of the identity closed subscheme, in its original Chow group. -/
def fundamentalClass (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) : chowGroup C q k :=
  QuotientAddGroup.mk' (rationalEquivalences C q k)
    (cycleAssociatedToClosedSubscheme C q (𝟙 X) k)

/-- Transport only along a proved equality of the original structure maps. -/
def structureMapCast (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q q' : X ⟶ C.S) [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (h : q = q') (k : ℤ) (α : chowGroup C q k) : chowGroup C q' k := by
  subst q'
  exact α

theorem structureMapCast_fundamentalClass (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q q' : X ⟶ C.S) [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (h : q = q') (k : ℤ) :
    structureMapCast C q q' h k (fundamentalClass C q k) = fundamentalClass C q' k := by
  subst q'
  rfl

/-- Transport a genuinely constructed fundamental class together with its proof.
The proof is obtained here for a variable scheme, before specializing to either native tower. -/
def transportFundamental (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q q' : X ⟶ C.S) [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (h : q = q') (k : ℤ)
    (a : {α : chowGroup C q k // α = fundamentalClass C q k}) :
    {α : chowGroup C q' k // α = fundamentalClass C q' k} :=
  ⟨structureMapCast C q q' h k a.val,
    (congrArg (structureMapCast C q q' h k) a.property).trans
      (structureMapCast_fundamentalClass C q q' h k)⟩

/-- The native flat fundamental-class formula, retaining any proved structure-map equality. -/
theorem bundlePullback_fundamentalClass (C : ChowSituation.{u}) {X P : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (qP : P ⟶ C.S) [LocallyOfFiniteType qP]
    (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (h : π ≫ q = qP)
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension π d) (k : ℤ)
    (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    bundlePullback C q qP π h d hd k (fundamentalClass C q k) =
      fundamentalClass C qP (k + d) := by
  subst qP
  exact SectionZeroScheme.flatPullbackChow_mk_fundamental C q π d hd k hX _

namespace Three

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {M N : T.Modules} (f : M ⟶ N) : HasKernel f :=
  HasKernels.has_limit f

variable (n : ℕ) {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} D]

abbrev space1 : Scheme.{u} := bundle D
abbrev kernel1 : (space1 D).Modules := kernel (bundleTautological D)
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 D) :=
  Stacks.FlagTower.isFiniteLocallyFree_kernel_bundleTautological D
abbrev space2 : Scheme.{u} := bundle (kernel1 D)
abbrev kernel2 : (space2 D).Modules := kernel (bundleTautological (kernel1 D))
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 D) :=
  Stacks.FlagTower.isFiniteLocallyFree_kernel_bundleTautological (kernel1 D)
abbrev space3 : Scheme.{u} := bundle (kernel2 D)
abbrev projection1 : space1 D ⟶ X := bundleProj D
abbrev projection2 : space2 D ⟶ space1 D := bundleProj (kernel1 D)
abbrev projection3 : space3 D ⟶ space2 D := bundleProj (kernel2 D)

/-- The literal native three-stage projection, with its original parentheses. -/
theorem towerProjection_eq :
    (tower 3 D).2 = (projection3 D ≫ projection2 D) ≫ projection1 D := by
  change ((𝟙 _ ≫ projection3 D) ≫ projection2 D) ≫ projection1 D = _
  rw [Category.id_comp]

theorem towerProjection_lft : LocallyOfFiniteType (tower 3 D).2 := by
  rw [towerProjection_eq D]
  infer_instance

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

abbrev q1 : space1 D ⟶ C.S := projection1 D ≫ q
abbrev q2 : space2 D ⟶ C.S := projection2 D ≫ q1 D C q
abbrev q3 : space3 D ⟶ C.S := projection3 D ≫ q2 D C q

omit [LocallyOfFiniteType q] in
theorem projection3_comp : projection3 D ≫ q2 D C q = q3 D C q := rfl

omit [LocallyOfFiniteType q] in
/-- Only associativity and the native identity stage relate the two structure maps. -/
theorem q3_eq_tower : q3 D C q = (tower 3 D).2 ≫ q := by
  change projection3 D ≫ (projection2 D ≫ (projection1 D ≫ q)) =
    (((𝟙 (space3 D) ≫ projection3 D) ≫ projection2 D) ≫ projection1 D) ≫ q
  rw [Category.id_comp]
  exact (Category.assoc (projection3 D) (projection2 D) (projection1 D ≫ q)).symm.trans
    (Category.assoc (projection3 D ≫ projection2 D) (projection1 D) q).symm

/-- Finite-type structure of the literal three-stage composite. -/
theorem q3_lft : LocallyOfFiniteType (q3 D C q) := inferInstance

variable [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D (n + 3)]

theorem kernel1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel1 D) (n + 2) :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological D (n + 2) hD

theorem kernel2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel2 D) (n + 1) :=
  Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological (kernel1 D) (n + 1)
    (kernel1Rank n D)

/-- First actual flat pullback, of relative dimension n+2. -/
def pull1 (k : ℤ) : chowGroup C q k →+ chowGroup C (q1 D C q) (k + (n + 2)) := by
  letI := @Stacks.Chow.flat_bundleProj X D (n + 2) hD
  exact bundlePullback C q (q1 D C q) (projection1 D) rfl (n + 2)
    (@Stacks.Chow.relativeDimension_bundleProj X D (n + 2) hD) k

/-- Second actual flat pullback, of relative dimension n+1. -/
def pull2 (k : ℤ) :
    chowGroup C (q1 D C q) k →+ chowGroup C (q2 D C q) (k + (n + 1)) := by
  letI := @Stacks.Chow.flat_bundleProj (space1 D) (kernel1 D) (n + 1) (kernel1Rank n D)
  exact bundlePullback C (q1 D C q) (q2 D C q) (projection2 D) rfl (n + 1)
    (@Stacks.Chow.relativeDimension_bundleProj (space1 D) (kernel1 D) (n + 1)
      (kernel1Rank n D)) k

/-- Third actual flat pullback, to the original native tower structure map. -/
def pull3 (k : ℤ) :
    chowGroup C (q2 D C q) k →+ chowGroup C (q3 D C q) (k + n) := by
  letI := @Stacks.Chow.flat_bundleProj (space2 D) (kernel2 D) n (kernel2Rank n D)
  exact bundlePullback C (q2 D C q) (q3 D C q) (projection3 D) (projection3_comp D C q) n
    (@Stacks.Chow.relativeDimension_bundleProj (space2 D) (kernel2 D) n
      (kernel2Rank n D)) k

/-- The three original flat pullbacks, without a normalization cap or supplied comparison. -/
def iteratedPull (k : ℤ) (α : chowGroup C q k) :
    chowGroup C (q3 D C q) (((k + (n + 2)) + (n + 1)) + n) :=
  pull3 n D C q ((k + (n + 2)) + (n + 1))
    (pull2 n D C q (k + (n + 2)) (pull1 n D C q k α))

theorem delta_dimension_first {k : ℤ} (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    schemeDeltaDimension C (q1 D C q) ≤ ((k + (n + 2) : ℤ) : EInt) := by
  let := @Stacks.Chow.flat_bundleProj X D (n + 2) hD
  exact SectionZeroScheme.schemeDeltaDimension_bundle_le C q D (n + 2)
    (@Stacks.Chow.relativeDimension_bundleProj X D (n + 2) hD) hX

theorem delta_dimension_second {k : ℤ} (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    schemeDeltaDimension C (q2 D C q) ≤ (((k + (n + 2)) + (n + 1) : ℤ) : EInt) := by
  let := @Stacks.Chow.flat_bundleProj (space1 D) (kernel1 D) (n + 1) (kernel1Rank n D)
  exact SectionZeroScheme.schemeDeltaDimension_bundle_le C (q1 D C q) (kernel1 D) (n + 1)
    (@Stacks.Chow.relativeDimension_bundleProj (space1 D) (kernel1 D) (n + 1)
      (kernel1Rank n D)) (delta_dimension_first n D C q hX)

/-- Each projective layer carries the genuine fundamental class to the next one. -/
theorem iteratedPull_fundamentalClass (k : ℤ)
    (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    iteratedPull n D C q k (fundamentalClass C q k) =
      fundamentalClass C (q3 D C q) (((k + (n + 2)) + (n + 1)) + n) := by
  let := @Stacks.Chow.flat_bundleProj X D (n + 2) hD
  let := @Stacks.Chow.flat_bundleProj (space1 D) (kernel1 D) (n + 1) (kernel1Rank n D)
  let := @Stacks.Chow.flat_bundleProj (space2 D) (kernel2 D) n (kernel2Rank n D)
  have h1 := bundlePullback_fundamentalClass C q (q1 D C q) (projection1 D) rfl (n + 2)
    (@Stacks.Chow.relativeDimension_bundleProj X D (n + 2) hD) k hX
  have h2 := bundlePullback_fundamentalClass C (q1 D C q) (q2 D C q) (projection2 D) rfl (n + 1)
    (@Stacks.Chow.relativeDimension_bundleProj (space1 D) (kernel1 D) (n + 1)
      (kernel1Rank n D)) (k + (n + 2)) (delta_dimension_first n D C q hX)
  have h3 := bundlePullback_fundamentalClass C (q2 D C q) (q3 D C q) (projection3 D)
    (projection3_comp D C q) n
    (@Stacks.Chow.relativeDimension_bundleProj (space2 D) (kernel2 D) n
      (kernel2Rank n D)) ((k + (n + 2)) + (n + 1)) (delta_dimension_second n D C q hX)
  exact (congrArg (fun α => pull3 n D C q ((k + (n + 2)) + (n + 1))
      (pull2 n D C q (k + (n + 2)) α)) h1).trans
    ((congrArg (pull3 n D C q ((k + (n + 2)) + (n + 1))) h2).trans h3)

/-- The actual iterated flat class and the proved native fundamental-class identity. -/
def iteratedFundamental (k : ℤ) (hX : schemeDeltaDimension C q ≤ (k : EInt)) :
    {α : chowGroup C (q3 D C q) (((k + (n + 2)) + (n + 1)) + n) //
      α = fundamentalClass C (q3 D C q) (((k + (n + 2)) + (n + 1)) + n)} :=
  ⟨iteratedPull n D C q k (fundamentalClass C q k),
    iteratedPull_fundamentalClass n D C q k hX⟩

end Three

section ActualFlags

variable (K : Type u) [Field K]

abbrev spaceA : Scheme.{u} := (towerA 3 6 (Spec (.of K))).1
abbrev spaceB : Scheme.{u} := (towerB 3 6 (Spec (.of K))).1
abbrev qA : spaceA K ⟶ (fieldChowSituation K).S := towerAProj 3 6 (Spec (.of K))
abbrev qB : spaceB K ⟶ (fieldChowSituation K).S := (towerB 3 6 (Spec (.of K))).2

/-- The native flag quotient is literally the original quotient used to define LG. -/
theorem universalQuotient_eq_original :
    Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K)) =
      M9Native.LagrangianGrassmannian.universalQuotient K := rfl

local instance actualQuotientRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target (0 + 3) :=
  Stacks.FlagTower.rank_universalQuotient 3 6 (Spec (.of K))
local instance actualFreeRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.FlagTower.freeModule 6 (Spec (.of K))) (3 + 3) :=
  Stacks.FlagTower.rank_freeModule 6 (Spec (.of K))

local instance actualQuotientFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target :=
  Stacks.FlagTower.isFiniteLocallyFree_universalQuotient 3 6 (Spec (.of K))
local instance actualFreeFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Stacks.FlagTower.freeModule 6 (Spec (.of K))) :=
  Stacks.FlagTower.isFiniteLocallyFree_freeModule 6 (Spec (.of K))

instance qA_lft : LocallyOfFiniteType (qA K) := by
  change LocallyOfFiniteType
    ((tower 3 (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target).2 ≫
      M9Native.LagrangianGrassmannian.grassmannianProjection K)
  let := Three.towerProjection_lft
    (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target
  infer_instance

instance qB_lft : LocallyOfFiniteType (qB K) :=
  Three.towerProjection_lft (Stacks.FlagTower.freeModule 6 (Spec (.of K)))

/-- The literal identity fundamental class of the rank-three quotient flag. -/
def fundamentalA : chowGroup (fieldChowSituation K) (qA K) 12 :=
  fundamentalClass (fieldChowSituation K) (qA K) 12

/-- The literal identity fundamental class of the free rank-six three-step flag. -/
def fundamentalB : chowGroup (fieldChowSituation K) (qB K) 12 :=
  fundamentalClass (fieldChowSituation K) (qB K) 12

/-- The original point's degree-zero fundamental class. -/
def baseFundamental : chowGroup (fieldChowSituation K) (𝟙 (Spec (.of K))) 0 :=
  fundamentalClass (fieldChowSituation K) (𝟙 (Spec (.of K))) 0

theorem base_delta_dimension :
    schemeDeltaDimension (fieldChowSituation K) (𝟙 (Spec (.of K))) = (0 : EInt) := by
  have hd : topologicalKrullDim (Spec (.of K)) = (0 : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum K) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  exact schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (𝟙 (Spec (.of K))) hd

/-- The first actual flat construction, with its identity-class proof retained. -/
def fundamentalDataA :
    {α : chowGroup (fieldChowSituation K) (qA K) 12 // α = fundamentalA K} :=
  transportFundamental (fieldChowSituation K)
    (Three.q3 (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target
      (fieldChowSituation K) (M9Native.LagrangianGrassmannian.grassmannianProjection K))
    (qA K)
    (Three.q3_eq_tower (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target
      (fieldChowSituation K) (M9Native.LagrangianGrassmannian.grassmannianProjection K)) 12
    (Three.iteratedFundamental 0
      (Stacks.FlagTower.universalQuotient 3 6 (Spec (.of K))).target
      (fieldChowSituation K) (M9Native.LagrangianGrassmannian.grassmannianProjection K) 9
      (le_of_eq (M9Native.LagrangianDegree.ambient_delta_dimension K)))

/-- The second actual flat construction, with its identity-class proof retained. -/
def fundamentalDataB :
    {α : chowGroup (fieldChowSituation K) (qB K) 12 // α = fundamentalB K} :=
  transportFundamental (fieldChowSituation K)
    (Three.q3 (Stacks.FlagTower.freeModule 6 (Spec (.of K)))
      (fieldChowSituation K) (𝟙 (Spec (.of K)))) (qB K)
    ((Three.q3_eq_tower (Stacks.FlagTower.freeModule 6 (Spec (.of K)))
      (fieldChowSituation K) (𝟙 (Spec (.of K)))).trans (Category.comp_id _)) 12
    (Three.iteratedFundamental 3 (Stacks.FlagTower.freeModule 6 (Spec (.of K)))
      (fieldChowSituation K) (𝟙 (Spec (.of K))) 0
      (le_of_eq (base_delta_dimension K)))

/-- The actual successive pullbacks in relative dimensions 2, 1, and 0 from Gr(3,6).
Its input identity class is definitionally the original ambientFundamental. -/
def iteratedPullA : chowGroup (fieldChowSituation K) (qA K) 12 :=
  (fundamentalDataA K).val

/-- The actual successive pullbacks in relative dimensions 5, 4, and 3 from Spec K. -/
def iteratedPullB : chowGroup (fieldChowSituation K) (qB K) 12 :=
  (fundamentalDataB K).val

theorem iteratedPullA_eq_fundamentalA : iteratedPullA K = fundamentalA K :=
  (fundamentalDataA K).property

theorem iteratedPullB_eq_fundamentalB : iteratedPullB K = fundamentalB K :=
  (fundamentalDataB K).property

/-- The original native flag isomorphism, with no replacement flag variety. -/
abbrev towerIso : spaceA K ≅ spaceB K := flagTowerIso 3 6 (Spec (.of K)) (by decide)

theorem towerIso_hom_comp : (towerIso K).hom ≫ qB K = qA K :=
  flagTowerIso_hom_comp 3 6 (Spec (.of K)) (by decide)

/-- Actual proper Chow pushforward along the original flag isomorphism. -/
def isoChowPush (k : ℤ) :
    chowGroup (fieldChowSituation K) (qA K) k →+
      chowGroup (fieldChowSituation K) (qB K) k :=
  properChowPushforward (fieldChowSituation K) (qA K) (qB K) (towerIso K).hom
    (towerIso_hom_comp K) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ k)

theorem isoChowPush_fundamentalA : isoChowPush K 12 (fundamentalA K) = fundamentalB K := by
  unfold isoChowPush fundamentalA fundamentalB fundamentalClass
  rw [properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  congr 1
  exact cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) (qB K)
    (𝟙 _ ≫ (towerIso K).hom) (𝟙 _) (towerIso K) (by simp) 12

/-- The two genuine iterated flat constructions agree under the actual native isomorphism. -/
theorem isoChowPush_iteratedPullA : isoChowPush K 12 (iteratedPullA K) = iteratedPullB K := by
  rw [iteratedPullA_eq_fundamentalA, iteratedPullB_eq_fundamentalB,
    isoChowPush_fundamentalA]

end ActualFlags

end M9Native.LagrangianFlagFundamentalTransport
