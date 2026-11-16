module

public import M9StacksIntegration.MukaiGeneratedImageDegree
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Equal-degree monomorphisms of bundles on an integral proper curve

The cokernel is the literal categorical cokernel of the original map.
Its generic stalk vanishes by additivity of generic rank. Its support is
therefore zero-dimensional. Euler additivity and the equality of the
original native curve degrees force its actual H0 to vanish; the native
decomposition into the stalks along its support then kills the cokernel.
No torsion, support, determinant-isomorphism, or zero-cokernel premise is
supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.CurveBundleMonoDegreeIso

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]

include f

/-- Properness over a field supplies coherence for an actual bundle. -/
theorem bundle_isCoherent (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r] : F.IsCoherent := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F

/-- An actual zero-dimensional coherent sheaf with H0 of dimension zero
is zero. The proof uses the native actual global-section/stalk decomposition. -/
theorem isZero_of_support_dim_le_zero_of_h0_eq_zero (T : X.Modules) [T.IsCoherent]
    (hT : topologicalKrullDim (SheafOfModules.supp T) ≤ 0)
    (h0 : Module.finrank k (cohomologyOverField k f T 0) = 0) : IsZero T := by
  classical
  let : Module.Finite k (cohomologyOverField k f T 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f T 0
  let : Subsingleton (cohomologyOverField k f T 0) :=
    (Module.finrank_zero_iff.mp h0)
  let : Subsingleton Γ(T, ⊤) :=
    (cohomologyOverFieldZeroEquivSections k f T).symm.subsingleton
  let : Subsingleton (∀ x : ↥(SheafOfModules.supp T), T.presheaf.stalk x.1) :=
    (suppStalkPiAddEquiv k f T hT).symm.toEquiv.subsingleton
  apply _root_.SheafOfModules.isZero_of_supp_eq_empty T
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hmem : x ∈ SheafOfModules.supp T := hx
  obtain ⟨a, ha⟩ := hx
  have hz : (Pi.single ⟨x, hmem⟩ a :
      ∀ y : ↥(SheafOfModules.supp T), T.presheaf.stalk y.1) = 0 :=
    Subsingleton.elim _ _
  exact ha (by simpa using congrFun hz ⟨x, hmem⟩)

variable [IsIntegral X]

/-- An equal-rank monomorphism has actual cokernel supported in dimension
zero. The final topological step is the nowhere-dense support argument of
the pinned native `Curves.VanishingResults.GenericPointSupport` provider,
replayed here using the already checked elementary dimension API. -/
theorem cokernel_support_dim_le_zero (hdim : topologicalKrullDim X ≤ 1)
    (r : ℕ) {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r]
    (j : F ⟶ G) [Mono j] :
    topologicalKrullDim (SheafOfModules.supp (cokernel j)) ≤ 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let hF : F.IsCoherent := bundle_isCoherent f F r
  let hG : G.IsCoherent := bundle_isCoherent f G r
  let hC : (cokernel j).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel hF hG j
  let : (cokernel j).IsFiniteType := hC.isFiniteType
  let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel j }
  have hr := Scheme.Modules.fiberRank_genericPoint_add_of_shortExact S hS
  change Scheme.Modules.fiberRank G (genericPoint X) =
    Scheme.Modules.fiberRank F (genericPoint X) +
      Scheme.Modules.fiberRank (cokernel j) (genericPoint X) at hr
  rw [Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank F r,
    Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank G r] at hr
  have hrC : Scheme.Modules.fiberRank (cokernel j) (genericPoint X) = 0 := by omega
  have hη : genericPoint X ∉ SheafOfModules.supp (cokernel j) := by
    let : Field (X.presheaf.stalk (genericPoint X)) :=
      inferInstanceAs (Field X.functionField)
    let : Module (X.presheaf.stalk (genericPoint X))
        ((cokernel j).presheaf.stalk (genericPoint X)) :=
      Stacks.SheafOfModules.FlatShortExact.stalkModule (cokernel j) (genericPoint X)
    let : Module.Finite (X.presheaf.stalk (genericPoint X))
        ((cokernel j).presheaf.stalk (genericPoint X)) :=
      Scheme.Modules.finite_stalk_of_isCoherent (cokernel j) (genericPoint X)
    have hdimC := (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk
      (cokernel j)).symm.trans hrC
    let : Subsingleton ((cokernel j).presheaf.stalk (genericPoint X)) :=
      Module.finrank_zero_iff.mp hdimC
    have hz : ∀ a : (cokernel j).presheaf.stalk (genericPoint X), a = 0 :=
      fun a => Subsingleton.elim a 0
    rintro ⟨a, ha⟩
    exact ha (hz a)
  have hcl : IsClosed (SheafOfModules.supp (cokernel j)) :=
    SheafOfModules.isClosed_supp (cokernel j)
  have hnd : IsNowhereDense (SheafOfModules.supp (cokernel j)) := by
    rw [IsNowhereDense, hcl.closure_eq, interior_eq_empty_iff_dense_compl]
    exact hcl.isOpen_compl.dense ⟨genericPoint X, hη⟩
  have h1 := le_trans (hnd.topologicalKrullDim_add_one_le hcl) hdim
  rcases eq_or_ne (topologicalKrullDim (SheafOfModules.supp (cokernel j))) ⊥ with hb | hb
  · exact hb.trans_le bot_le
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hb
  rw [← hn] at h1 ⊢
  have h2 : n + 1 ≤ 1 := by exact_mod_cast h1
  have hn0 : n < 1 := by
    rcases eq_or_ne n ⊤ with rfl | hne
    · simp at h2
    · exact (ENat.add_one_le_iff hne).mp h2
  exact_mod_cast (Order.lt_one_iff.mp hn0).le

/-- Equal native curve degree kills the actual cokernel of the original
equal-rank monomorphism. -/
theorem cokernel_isZero_of_curveDegree_eq (hdim : topologicalKrullDim X ≤ 1)
    (r : ℕ) {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r]
    (j : F ⟶ G) [Mono j]
    (hdeg : curveDegree k f hdim F r = curveDegree k f hdim G r) :
    IsZero (cokernel j) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let hF : F.IsCoherent := bundle_isCoherent f F r
  let hG : G.IsCoherent := bundle_isCoherent f G r
  let : (cokernel j).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel hF hG j
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hC := cokernel_support_dim_le_zero f hdim r j
  have hS : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_cokernel j }
  have hχ := eulerCharacteristic_add_of_shortExact k f hS
  change eulerCharacteristic k f G =
    eulerCharacteristic k f F + eulerCharacteristic k f (cokernel j) at hχ
  rw [curveDegree_eq_eulerCharacteristic_sub,
    curveDegree_eq_eulerCharacteristic_sub] at hdeg
  rw [eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero
    k f (cokernel j) hC] at hχ
  apply isZero_of_support_dim_le_zero_of_h0_eq_zero f (cokernel j) hC
  omega

/-- A monomorphism between bundles of equal rank and equal native degree
on a proper integral scheme of dimension at most one is an isomorphism. -/
theorem isIso_of_curveDegree_eq (hdim : topologicalKrullDim X ≤ 1)
    (r : ℕ) {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G r]
    (j : F ⟶ G) [Mono j]
    (hdeg : curveDegree k f hdim F r = curveDegree k f hdim G r) : IsIso j := by
  have hC := cokernel_isZero_of_curveDegree_eq f hdim r j hdeg
  let : Epi j := Abelian.epi_of_cokernel_π_eq_zero j (hC.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi j

omit [IsIntegral X]

/-- The original rank-two curve criterion needed for the comparison of
the generated image with its prescribed saturation. -/
theorem rank_two_isIso_of_curveDegree_eq [IsCurve k f] {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 2]
    (j : F ⟶ G) [Mono j]
    (hdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le F 2 =
      curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le G 2) : IsIso j :=
  isIso_of_curveDegree_eq f (IsCurve.topologicalKrullDim_eq_one f).le 2 j hdeg

end M9Native.CurveBundleMonoDegreeIso
