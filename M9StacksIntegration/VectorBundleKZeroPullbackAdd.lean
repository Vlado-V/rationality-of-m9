module

public import M9StacksIntegration.SectionKZero
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackMonoDualMap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# The actual additive pullback on vector-bundle K-zero

The native K-zero universal property constructs pullback from the actual
sheaf pullback. A short exact sequence with finite locally free quotient
splits on stalks, hence its first map stays monic under every pullback;
the left adjunction preserves the actual cokernel. These genuine native
facts prove that the construction respects actual K-zero relations.

Only the additive map and its unit/generator formulas are needed by the
incidence and inverse-Chern argument. No Adams operations or extra
compatibility hypothesis is imported.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.VectorBundleKZeroPullbackAdd

variable {X Y : Scheme.{u}}

/-- Actual pullback preserves a short exact sequence whose actual
quotient is finite locally free, without a flatness premise. -/
theorem shortExact_pullback (p : Y ⟶ X) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} S.X₃) :
    (S.map (Scheme.Modules.pullback p)).ShortExact := by
  have hm : Mono ((Scheme.Modules.pullback p).map S.f) :=
    mono_pullback_map_of_forall_stalk_splitInjective p S.f fun x =>
      exists_stalkHom_retraction S.f S.g S.zero hS.mono_f hS.epi_g hS.exact
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hQ) x
  have hc : IsColimit (CokernelCofork.ofπ (S.map (Scheme.Modules.pullback p)).g
      (S.map (Scheme.Modules.pullback p)).zero) :=
    CokernelCofork.mapIsColimit _ hS.gIsCokernel (Scheme.Modules.pullback p)
  exact ShortComplex.ShortExact.mk'
    ((S.map (Scheme.Modules.pullback p)).exact_of_g_is_cokernel hc) hm
    (Limits.epi_of_isColimit_cofork hc)

def classOfPullback (p : Y ⟶ X) (M : X.Modules) : VectorBundleKZero Y :=
  open scoped Classical in
  if SheafOfModules.IsFiniteLocallyFree.{u,u,u} M then
    VectorBundleKZero.classOf Y ((Scheme.Modules.pullback p).obj M) else 0

theorem classOfPullback_of_finiteLocallyFree (p : Y ⟶ X) (M : X.Modules)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u,u,u} M) :
    classOfPullback p M = VectorBundleKZero.classOf Y ((Scheme.Modules.pullback p).obj M) := by
  simp only [classOfPullback,ite_eq_left hM]

def pullbackAddHom (p : Y ⟶ X) : VectorBundleKZero X →+ VectorBundleKZero Y :=
  VectorBundleKZero.liftAddHom (classOfPullback p)
    (fun M hM => by simp only [classOfPullback,ite_eq_right hM])
    (fun {E F G} f g w hE hF hG hf hg hex => by
      rw [classOfPullback_of_finiteLocallyFree p F hF,
        classOfPullback_of_finiteLocallyFree p E hE,
        classOfPullback_of_finiteLocallyFree p G hG]
      have hS : (ShortComplex.mk f g w).ShortExact := ShortComplex.ShortExact.mk' hex hf hg
      have hPB := shortExact_pullback p _ hS hG
      exact @VectorBundleKZero.classOf_shortExact Y _ _ _ _ _ hPB.mono_f hPB.epi_g _
        (Stacks.Chow.isFiniteLocallyFree_pullback p E hE)
        (Stacks.Chow.isFiniteLocallyFree_pullback p F hF)
        (Stacks.Chow.isFiniteLocallyFree_pullback p G hG) hPB.exact)

theorem pullbackAddHom_classOf (p : Y ⟶ X) (M : X.Modules)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u,u,u} M) :
    pullbackAddHom p (VectorBundleKZero.classOf X M) =
      VectorBundleKZero.classOf Y ((Scheme.Modules.pullback p).obj M) :=
  (VectorBundleKZero.liftAddHom_classOf _ _ _ M).trans
    (classOfPullback_of_finiteLocallyFree p M hM)

theorem pullbackAddHom_one (p : Y ⟶ X) :
    pullbackAddHom p (1 : VectorBundleKZero X) = 1 := by
  rw [← VectorBundleKZero.classOf_unit X,pullbackAddHom_classOf p _ (isFiniteLocallyFree_unit X)]
  exact (VectorBundleKZero.classOf_eq_of_iso (Scheme.Modules.pullbackUnitIso p)
    (Stacks.Chow.isFiniteLocallyFree_pullback p _ (isFiniteLocallyFree_unit X))).trans
      (VectorBundleKZero.classOf_unit Y)

/-- Actual multiples of the unit class remain actual multiples of
the unit class after the constructed additive pullback. -/
theorem classOf_pullback_eq_nsmul_unit (p : Y ⟶ X) (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F) (n : ℕ)
    (hclass : VectorBundleKZero.classOf X F = n • (1 : VectorBundleKZero X)) :
    VectorBundleKZero.classOf Y ((Scheme.Modules.pullback p).obj F) =
      n • (1 : VectorBundleKZero Y) := by
  rw [← pullbackAddHom_classOf p F hF,hclass,map_nsmul,pullbackAddHom_one]

end M9Native.VectorBundleKZeroPullbackAdd
