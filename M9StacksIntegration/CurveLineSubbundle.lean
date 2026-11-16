module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.InvertibleFiltration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsoInCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual

/-!
# An actual line subbundle on a smooth integral curve

The unconditional projective-bundle splitting theorem constructs an
invertible quotient after a modification. A modification of a regular
integral scheme of dimension at most one is an isomorphism: the native
codimension-one isomorphism theorem covers every point. Pulling its
constructed quotient back along the inverse gives an invertible quotient
of the original rank-two bundle. Its actual categorical kernel has rank
one and is invertible. The quotient is torsion free, so this is a saturated
line subbundle.

No line, quotient map, exact sequence, or splitting is assumed. The
projective-bundle construction and the modification-isomorphism theorem
are independently proved native providers. Validation and the complete
axiom audit are recorded separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.CurveLineSubbundle

/-- Every point of a scheme of dimension at most one has local-ring
dimension at most one. -/
theorem stalk_dimension_le_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  exact (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x).trans
    ((topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X).symm.le.trans hdim)

/-- The restriction above the entire target detects an isomorphism. -/
theorem isIso_of_morphismRestrict_top {Y X : Scheme.{u}} (π : Y ⟶ X)
    [IsIso (π ∣_ (⊤ : X.Opens))] : IsIso π := by
  have htop {Z : Scheme.{u}} (U : Z.Opens) (hU : U = ⊤) : IsIso U.ι := by
    subst U
    exact Z.topIso.isIso_hom
  have := htop (⊤ : X.Opens) rfl
  have := htop (π ⁻¹ᵁ (⊤ : X.Opens)) (by simp)
  have : IsIso ((π ⁻¹ᵁ (⊤ : X.Opens)).ι ≫ π) := by
    rw [← morphismRestrict_ι π ⊤]
    infer_instance
  exact IsIso.of_isIso_comp_left (π ⁻¹ᵁ (⊤ : X.Opens)).ι π

/-- An invertible sheaf on a regular integral scheme is torsion free. -/
theorem isTorsionFree_of_isInvertible_on_regular
    {X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    (M : X.Modules)
    (hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M) :
    Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := hM
  exact Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_of_isReflexive M
    (isReflexive_of_isInvertible X M)

/-- An invertible quotient constructed after an isomorphic pullback gives
an invertible quotient of the original sheaf. The map is transported by
the actual inverse pullback equivalence, and pullback preserves its epimorphy. -/
theorem exists_invertible_quotient_of_isIso_pullback
    {Y X : Scheme.{u}} (π : Y ⟶ X) [IsIso π] (F : X.Modules)
    (h : ∃ M : Y.Modules,
      SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
        ∃ q : (Scheme.Modules.pullback π).obj F ⟶ M, Epi q) :
    ∃ M : X.Modules,
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
        ∃ q : F ⟶ M, Epi q := by
  obtain ⟨M,hM,q,hq⟩ := h
  let e : (Scheme.Modules.pullback (inv π)).obj ((Scheme.Modules.pullback π).obj F) ≅ F :=
    (Scheme.Modules.pullbackComp (inv π) π).app F ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id π)).app F ≪≫
        (Scheme.Modules.pullbackId X).app F
  have hpres : (Scheme.Modules.pullback (inv π)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction (inv π))
  let := hq
  let := hpres
  let : Stacks.Ample.IsInvertibleModule Y M := hM
  have hM' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback (inv π)).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback (inv π) M
  refine ⟨(Scheme.Modules.pullback (inv π)).obj M, hM',
    e.inv ≫ (Scheme.Modules.pullback (inv π)).map q, ?_⟩
  infer_instance

/-- When the kernel of an invertible quotient has rank one, it is an
actual saturated invertible subsheaf, with the categorical kernel sequence. -/
theorem kernel_is_saturated_invertible_line
    {X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    {F M : X.Modules} (q : F ⟶ M) [Epi q]
    (hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (hLrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) 1) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (kernel q) ∧
      Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M ∧
      (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact := by
  refine ⟨(Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    X (kernel q)).mpr hLrank, isTorsionFree_of_isInvertible_on_regular hreg M hM, ?_⟩
  exact { exact := ShortComplex.exact_kernel q }

/-- The modification supplied by the splitting theorem is already an
isomorphism when the original integral scheme is regular of dimension one
or less. -/
theorem isIso_modification_of_regular_dimension_le_one
    {Y X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 1) (π : Y ⟶ X) (hπ : IsModification π) :
    IsIso π := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : IsNormal X := isNormal_of_isRegular X hreg
  obtain ⟨U,hU,hcover⟩ := IsModification.exists_isIso_morphismRestrict_of_isNormal π hπ
  have hUtop : U = ⊤ := eq_top_iff.mpr fun x _ =>
    hcover x (stalk_dimension_le_one X hdim x)
  subst U
  let := hU
  exact isIso_of_morphismRestrict_top π

/-- A filtration of length two supplies an actual invertible quotient.
The map is extracted from the constructed filtration, not postulated. -/
theorem exists_invertible_quotient_of_filtration_two
    {X : Scheme.{u}} {F : X.Modules}
    (hF : Stacks.WeilCohomology.HasInvertibleFiltration X F 2) :
    ∃ (M : X.Modules),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
        ∃ q : F ⟶ M, Epi q := by
  cases hF with
  | step i q w hS hM hF hsub =>
    exact ⟨_,hM,q,hS.epi_g⟩

/-- A rank-two bundle on the original regular integral curve has an
actual invertible quotient, by descending the constructed modification. -/
theorem exists_invertible_quotient
    {X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) :
    ∃ (M : X.Modules),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
        ∃ q : F ⟶ M, Epi q := by
  obtain ⟨Y,π,hπ,hfil⟩ :=
    Stacks.ProjectiveBundleSplitting.exists_modification_hasInvertibleFiltration' 2 X F hF
  let : IsIso π := isIso_modification_of_regular_dimension_le_one hreg hdim π hπ
  exact exists_invertible_quotient_of_isIso_pullback π F
    (exists_invertible_quotient_of_filtration_two hfil)

/-- The actual kernel of the constructed rank-one quotient is an
invertible rank-one subbundle of the original bundle. The quotient is
torsion free, which is the saturation condition. -/
theorem exists_saturated_invertible_line_subbundle
    {X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) :
    ∃ (L M : X.Modules),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ∧
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
      Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M ∧
      ∃ (i : L ⟶ F) (q : F ⟶ M) (w : i ≫ q = 0),
        (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨M,hM,q,hq⟩ := exists_invertible_quotient hreg hdim F hF
  let := hq
  have hLrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
      q hq hM 1 hF
  obtain ⟨hL,htf,hS⟩ := kernel_is_saturated_invertible_line hreg q hM hLrank
  exact ⟨kernel q,M,hL,hM,htf,kernel.ι q,q,kernel.condition q,hS⟩

/-- In particular, every genuine rank-two bundle on a smooth integral
curve has the line-bundle exact sequence used in Mukai Proposition 1.2.
Properness is not needed for this step. -/
theorem exists_line_subbundle_on_smooth_curve
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2) :
    ∃ (L M : X.Modules),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ∧
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M ∧
      Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M ∧
      ∃ (i : L ⟶ F) (q : F ⟶ M) (w : i ≫ q = 0),
        (ShortComplex.mk i q w).ShortExact :=
  exists_saturated_invertible_line_subbundle (isRegular_of_smooth_over_field f)
    (IsCurve.topologicalKrullDim_eq_one f).le F hF

end M9Native.CurveLineSubbundle
