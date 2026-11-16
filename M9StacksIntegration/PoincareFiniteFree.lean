module

public import M9StacksIntegration.PoincareFieldLine
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Actual finite free modules and their actual bundle K-zero classes

Over a field spectrum the native associated-sheaf equivalence turns
an actual basis of global sections into an actual finite free sheaf.
The class of that free sheaf is computed using actual split short
exact sequences, rather than an imposed rank relation in K-zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.PoincareChern

private def freeIndexIso (X : Scheme.{u}) {I J : Type u} (e : I ≃ J) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      SheafOfModules.free (R := X.ringCatSheaf) J :=
  (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso

/-- The actual free sheaf on a finite sum of index types obeys the
actual split-sequence relation in the actual bundle Grothendieck group. -/
theorem classOf_free_sum (X : Scheme.{u}) (I J : Type u) [Finite I] [Finite J] :
    VectorBundleKZero.classOf X (SheafOfModules.free (R := X.ringCatSheaf) (I ⊕ J)) =
      VectorBundleKZero.classOf X (SheafOfModules.free (R := X.ringCatSheaf) I) +
        VectorBundleKZero.classOf X (SheafOfModules.free (R := X.ringCatSheaf) J) := by
  let E : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
  let F : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) J
  let e : SheafOfModules.free (R := X.ringCatSheaf) (I ⊕ J) ≅ E ⊞ F :=
    (SheafOfModules.freeSumIso (R := X.ringCatSheaf) I J).symm ≪≫
      (biprod.isoCoprod E F).symm
  have hfree : Stacks.FiniteLocallyFree.IsFiniteLocallyFree
      (SheafOfModules.free (R := X.ringCatSheaf) (I ⊕ J)) := inferInstance
  have hmid : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (E ⊞ F) :=
    @Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso _ _ _ _ _ _ _ _ e hfree
  let a : E ⟶ E ⊞ F := biprod.inl
  let b : E ⊞ F ⟶ F := biprod.snd
  have w : a ≫ b = 0 := biprod.inl_snd
  have hs : (ShortComplex.mk a b w).ShortExact :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct E F).shortExact
  exact (VectorBundleKZero.classOf_eq_of_iso e hfree).trans
    (@VectorBundleKZero.classOf_shortExact X E (E ⊞ F) F a b
      hs.mono_f hs.epi_g w inferInstance hmid inferInstance hs.exact)

/-- The actual free sheaf of rank `r` represents `r[O]` in actual
bundle K-zero. -/
theorem classOf_free_fin (X : Scheme.{u}) (r : ℕ) :
    VectorBundleKZero.classOf X
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) =
      r • (1 : VectorBundleKZero X) := by
  have hone : VectorBundleKZero.classOf X
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1))) = 1 := by
    let e := freeIndexIso X (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit.{u + 1}) ≪≫
      Stacks.SheafOfModules.Site.freePUnitIso
    exact (VectorBundleKZero.classOf_eq_of_iso e inferInstance).trans
      (VectorBundleKZero.classOf_unit X)
  induction r with
  | zero =>
      have hz : IsZero
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 0))) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply (SheafOfModules.free
          (R := X.ringCatSheaf) (ULift.{u} (Fin 0))).freeHomEquiv.injective
        funext i
        exact Fin.elim0 i.down
      simpa only [zero_nsmul] using
        (VectorBundleKZero.classOf_eq_of_iso hz.isoZero inferInstance).trans
          (VectorBundleKZero.classOf_zero X)
  | succ r ih =>
      let ei : ULift.{u} (Fin (r + 1)) ≃ ULift.{u} (Fin r) ⊕ ULift.{u} (Fin 1) :=
        Equiv.ulift.trans ((finSumFinEquiv (m := r) (n := 1)).symm.trans
          (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))
      let e := freeIndexIso X ei
      calc
        _ = VectorBundleKZero.classOf X
            (SheafOfModules.free (R := X.ringCatSheaf)
              (ULift.{u} (Fin r) ⊕ ULift.{u} (Fin 1))) :=
          VectorBundleKZero.classOf_eq_of_iso e inferInstance
        _ = _ := by rw [classOf_free_sum, ih, hone, succ_nsmul]

/-- An actual finite-dimensional space of global sections on the
actual field spectrum gives an actual trivialization of the sheaf. -/
def specFieldIsoFiniteFree (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules)
    [Module.Finite (CommRingCat.of K) (moduleSpecΓFunctor.obj M)]
    (r : ℕ) (hr : Module.finrank (CommRingCat.of K) (moduleSpecΓFunctor.obj M) = r) :
    M ≅ SheafOfModules.free (R := (Spec (.of K)).ringCatSheaf) (ULift.{u} (Fin r)) := by
  let R := CommRingCat.of K
  let V : ModuleCat R := moduleSpecΓFunctor.obj M
  haveI : IsIso M.fromTildeΓ := SpecField.isIso_fromTildeΓ (Field.toIsField K) M
  let b := Module.finBasis R V
  let e : M ≅ (tilde.functor R).obj (ModuleCat.of R (Fin (Module.finrank R V) → R)) :=
    (asIso M.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b.equivFun.toModuleIso
  let e' : M ≅ (tilde.functor R).obj (ModuleCat.of R (Fin r → R)) :=
    e ≪≫ eqToIso (by rw [hr])
  let el : (Fin r → R) ≃ₗ[R] (ULift.{u} (Fin r) → R) :=
    LinearEquiv.funCongrLeft R R Equiv.ulift
  let ef : (ULift.{u} (Fin r) → R) ≃ₗ[R] (ULift.{u} (Fin r) →₀ R) :=
    (Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin r)) :
      (ULift.{u} (Fin r) →₀ R) ≃ₗ[R] (ULift.{u} (Fin r) → R)).symm
  exact e' ≪≫ (tilde.functor R).mapIso (el.trans ef).toModuleIso ≪≫
    tildeFinsupp (R := R) (ULift.{u} (Fin r))

/-- The actual class of an actual field-spectrum sheaf with `r`
independent global basis vectors is `r[O]`. -/
theorem classOf_specField_eq_nsmul_of_finrank (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules)
    [Module.Finite (CommRingCat.of K) (moduleSpecΓFunctor.obj M)]
    (r : ℕ) (hr : Module.finrank (CommRingCat.of K) (moduleSpecΓFunctor.obj M) = r) :
    VectorBundleKZero.classOf (Spec (.of K)) M =
      r • (1 : VectorBundleKZero (Spec (.of K))) := by
  let e := specFieldIsoFiniteFree K M r hr
  have hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree M :=
    @Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso _ _ _ _ _ _ _ _ e.symm inferInstance
  exact (VectorBundleKZero.classOf_eq_of_iso e hM).trans (classOf_free_fin _ r)

/-- An arbitrary actual scheme pullback preserves the actual finite
free sheaf and its displayed rank. -/
def pullbackFiniteFreeIso {Y S : Scheme.{u}} (f : Y ⟶ S) (r : ℕ) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)) := by
  let F := Scheme.Modules.pullback f
  letI : F.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction f).isLeftAdjoint
  have hp : PreservesColimitsOfShape.{u, u} (Discrete (ULift.{u} (Fin r))) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F
    (ULift.{u} (Fin r)) hp (Scheme.Modules.pullbackUnitIso f).symm).symm

/-- A finite locally free module of the specified rank on an actual
field spectrum is actually free of that same rank.  A member of its
native trivializing cover contains the unique point and hence is the
whole spectrum. -/
theorem nonempty_specFieldIsoFiniteFreeOfRank (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules) (r : ℕ)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    Nonempty (M ≅ SheafOfModules.free
      (R := (Spec (.of K)).ringCatSheaf) (ULift.{u} (Fin r))) := by
  haveI : Subsingleton (Spec (.of K)) := SpecField.subsingleton_carrier (Field.toIsField K)
  let x : Spec (.of K) := Classical.choice inferInstance
  obtain ⟨q, hq, hr⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  have hcov : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff (Spec (.of K)) q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := hcov.exists_mem x
  let U : (Spec (.of K)).Opens := q.X i
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim y x) ▸ hxi
  haveI : IsIso U.ι := by
    rw [hU]
    exact (Spec (.of K)).topIso.isIso_hom
  obtain ⟨ei⟩ := hr i
  obtain ⟨eU⟩ := Scheme.Modules.nonempty_restrict_iso_free_of_isLocallyFreeData M q hq i
  let F := Scheme.Modules.pullback U.ι
  letI : (Scheme.Modules.pushforward (asIso U.ι).symm.hom).IsEquivalence :=
    (Scheme.Modules.pushforwardEquivOfIso (asIso U.ι).symm).isEquivalence_functor
  letI : F.IsEquivalence := Functor.isEquivalence_of_iso
    (Scheme.Modules.pullbackIsoPushforward (asIso U.ι).symm).symm
  let ef : SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ≅
      F.obj (SheafOfModules.free (R := (Spec (.of K)).ringCatSheaf) (ULift.{u} (Fin r))) :=
    (pullbackFiniteFreeIso U.ι r).symm
  exact ⟨F.preimageIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ eU ≪≫
      freeIndexIso U.toScheme (ei.trans Equiv.ulift.symm) ≪≫ ef)⟩

/-- A chosen actual free trivialization supplied by the preceding
proved existence theorem. -/
def specFieldIsoFiniteFreeOfRank (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules) (r : ℕ)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    M ≅ SheafOfModules.free (R := (Spec (.of K)).ringCatSheaf) (ULift.{u} (Fin r)) :=
  (nonempty_specFieldIsoFiniteFreeOfRank K M r hM).some

/-- Rank on an actual field spectrum determines its actual bundle
K-zero class, by the proved actual trivialization. -/
theorem classOf_specField_eq_nsmul_of_rank (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules) (r : ℕ)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    VectorBundleKZero.classOf (Spec (.of K)) M =
      r • (1 : VectorBundleKZero (Spec (.of K))) := by
  let e := specFieldIsoFiniteFreeOfRank K M r hM
  have hf : Stacks.FiniteLocallyFree.IsFiniteLocallyFree M :=
    @Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso _ _ _ _ _ _ _ _ e.symm inferInstance
  exact (VectorBundleKZero.classOf_eq_of_iso e hf).trans (classOf_free_fin _ r)

end M9Native.PoincareChern
