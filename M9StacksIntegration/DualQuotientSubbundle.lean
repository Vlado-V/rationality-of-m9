module

public import M9StacksIntegration.SheafFieldKernelObstruction
public import M9StacksIntegration.HomSectionPullback
public import M9StacksIntegration.PullbackKernelComparison
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackMonoDualMap
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# The actual subbundle dual to a quotient of a pulled-back dual

For a quotient `q : π* E∨ → Q`, finite locally free duality gives the
actual map `Q∨ → π* E`. It stays monic after arbitrary scheme pullback
when `q` is epi and `Q` is finite locally free. At a field point, a
rank-three such subbundle cannot lie in an actual kernel of dimension
at most two. This also gives nonvanishing of the actual pulled Hom
section, using the proved monoidal pullback comparison.

The construction is applied to the actual rank-three quotient on the
native tower of three projective bundles. No duality or fiber
comparison is supplied as an extra hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DualQuotientSubbundle

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The genuine pullback-dual comparison and genuine double-dual
isomorphism identify `(π* E∨)∨` with `π* E`. -/
def dualPullbackDualIso :
    dualSheaf ((Scheme.Modules.pullback π).obj (dualSheaf E)) ≅
      (Scheme.Modules.pullback π).obj E := by
  let hD := isFiniteLocallyFree_dualSheaf E inferInstance
  let hbc := Stacks.Chow.pullbackDualMap_isIso π (dualSheaf E) hD
  let hdd := isIso_toDoubleDual_of_isFiniteLocallyFree E
  exact (@asIso _ _ _ _ (Stacks.Chow.pullbackDualMap π (dualSheaf E)) hbc).symm ≪≫
    (Scheme.Modules.pullback π).mapIso (@asIso _ _ _ _ (toDoubleDual E) hdd).symm

/-- The actual dual quotient map, followed by actual native duality. -/
def inclusion {Q : Y.Modules}
    (q : (Scheme.Modules.pullback π).obj (dualSheaf E) ⟶ Q) :
    dualSheaf Q ⟶ (Scheme.Modules.pullback π).obj E :=
  dualMap q ≫ (dualPullbackDualIso π E).hom

/-- A finite locally free quotient gives an inclusion preserved under
every base change. No flatness hypothesis is imposed. -/
theorem pullback_inclusion_mono {Q : Y.Modules}
    (q : (Scheme.Modules.pullback π).obj (dualSheaf E) ⟶ Q) (hq : Epi q)
    (hQ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q)
    {T : Scheme.{u}} (f : T ⟶ Y) :
    Mono ((Scheme.Modules.pullback f).map (inclusion π E q)) := by
  have hD := isFiniteLocallyFree_dualSheaf E inferInstance
  have hPD := Stacks.Chow.isFiniteLocallyFree_pullback π (dualSheaf E) hD
  let : Mono ((Scheme.Modules.pullback f).map (dualMap q)) :=
    mono_pullback_map_dualMap_of_epi f q hq hPD hQ
  change Mono ((Scheme.Modules.pullback f).map
    (dualMap q ≫ (dualPullbackDualIso π E).hom))
  rw [Functor.map_comp]
  infer_instance

/-- At an actual field point, the rank-three dual quotient restriction
of a rank-ten bundle map is nonzero if its kernel has dimension at
most two on the actual native section space. -/
theorem fieldPoint_restriction_ne_zero
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {Q : Y.Modules} (q : (Scheme.Modules.pullback π).obj (dualSheaf E) ⟶ Q)
    (hq : Epi q) (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 3)
    {F : X.Modules} (v : E ⟶ F)
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ Y)
    (hker : Module.finrank K (LinearMap.ker
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback π).map v))).hom) ≤ 2) :
    (Scheme.Modules.pullback f).map
      (inclusion π E q ≫ (Scheme.Modules.pullback π).map v) ≠ 0 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback π).obj E) 10 :=
    @isFiniteLocallyFreeOfRank_pullback _ _ π E 10 hE
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback π).obj E)) 10 :=
    isFiniteLocallyFreeOfRank_pullback f _ 10
  have hDQ := isFiniteLocallyFreeOfRank_dualSheaf Q 3 hQ
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj (dualSheaf Q)) 3 :=
    @isFiniteLocallyFreeOfRank_pullback _ _ f _ 3 hDQ
  let := pullback_inclusion_mono π E q hq hQ.isFiniteLocallyFree f
  simpa only [Functor.map_comp] using
    SheafFieldKernelObstruction.comp_ne_zero_of_kernel_finrank_le_two K
      ((Scheme.Modules.pullback f).map (inclusion π E q))
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback π).map v)) hker

/-- The preceding genuine rank obstruction gives nonvanishing of the
actual global section of the actual pulled-back native Hom bundle. -/
theorem fieldPoint_homSection_ne_zero
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {Q : Y.Modules} (q : (Scheme.Modules.pullback π).obj (dualSheaf E) ⟶ Q)
    (hq : Epi q) (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 3)
    {F : X.Modules} (v : E ⟶ F)
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ Y)
    (hker : Module.finrank K (LinearMap.ker
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullback π).map v))).hom) ≤ 2) :
    pullbackGlobalSections f
      (CurriedHomSection.homBundle (dualSheaf Q) ((Scheme.Modules.pullback π).obj F))
      (CurriedHomSection.homSection
        (inclusion π E q ≫ (Scheme.Modules.pullback π).map v)) ≠ 0 :=
  HomSectionPullback.pullback_homSection_ne_zero f _
    (fieldPoint_restriction_ne_zero π E hE q hq hQ v K f hker)

/-- The same actual nonvanishing statement with the actual Picard-fiber
kernel expressed at the composite field-valued point. The actual
iterated-pullback comparison transports the kernel bound. -/
theorem fieldPoint_homSection_ne_zero_of_compositeKernel
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 10)
    {Q : Y.Modules} (q : (Scheme.Modules.pullback π).obj (dualSheaf E) ⟶ Q)
    (hq : Epi q) (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 3)
    {F : X.Modules} (v : E ⟶ F)
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ Y)
    (hker : Module.finrank K (LinearMap.ker
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (f ≫ π)).map v)).hom) ≤ 2) :
    pullbackGlobalSections f
      (CurriedHomSection.homBundle (dualSheaf Q) ((Scheme.Modules.pullback π).obj F))
      (CurriedHomSection.homSection
        (inclusion π E q ≫ (Scheme.Modules.pullback π).map v)) ≠ 0 := by
  apply fieldPoint_homSection_ne_zero π E hE q hq hQ v K f
  rw [PullbackKernelComparison.finrank_iteratedPullbackKernel K f π v]
  exact hker

end M9Native.DualQuotientSubbundle
