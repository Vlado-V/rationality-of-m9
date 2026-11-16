module

public import M9StacksIntegration.SectionZeroSubbundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso

/-! The FULL hyperplane zero scheme of a genuinely split quotient onto
a line is that line's actual projective bundle, hence the original
base. The proof uses factorization on every scheme, including
nonreduced schemes, and constructs the inverse scheme maps. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeProj
universe u
namespace M9Native.SplitLineProjectiveZero

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (q : F ⟶ G) [Epi q] (S : UnitSplitting q)

instance twist_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tautologicalDatumTwist F) 1 := by
  let : SheafOfModules.IsInvertible (projectiveBundle X F).presheaf
      (projectiveBundle X F).ringCatSheaf.2 (tautologicalDatumTwist F) :=
    (tautologicalDatum F).invertible
  exact Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme _ _

def zeroIdeal : (projectiveBundle X F).IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal (projectiveBundle X F)
    (tautologicalDatumTwist F) (hyperplaneSection S.σ)

/-- Pullback of an actual section is zero exactly when pullback of its
actual unit-to-module morphism is zero. -/
theorem pullback_section_eq_zero_iff {Y T : Scheme.{u}} (f : T ⟶ Y)
    (L : Y.Modules) (s : Γ(L,⊤)) :
    pullbackGlobalSections f L s = 0 ↔
      (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop L s) = 0 := by
  rw [Scheme.Modules.pullback_map_unitHomEquivTop]
  change pullbackGlobalSections f L s = 0 ↔
    (Scheme.Modules.pullbackUnitIso f).hom ≫
      Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)
        (pullbackGlobalSections f L s) = 0
  constructor
  · intro h
    rw [h, Scheme.Modules.unitHomEquivTop_zero, comp_zero]
  · intro h
    have hz : Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)
        (pullbackGlobalSections f L s) = 0 :=
      (cancel_epi (Scheme.Modules.pullbackUnitIso f).hom).mp (by simpa using h)
    exact (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj L)).injective
      (hz.trans (Scheme.Modules.unitHomEquivTop_zero _).symm)

/-- The native split-quotient factorization criterion detects the full
section zero scheme on ALL test schemes. -/
theorem factors_iff {T : Scheme.{u}} (f : T ⟶ projectiveBundle X F) :
    (∃ h : T ⟶ projectiveBundle X G, h ≫ projectiveBundleMapOfEpi q = f) ↔
      pullbackGlobalSections f (tautologicalDatumTwist F) (hyperplaneSection S.σ) = 0 := by
  rw [pullback_section_eq_zero_iff, unitHomEquivTop_hyperplaneSection,
    pullback_map_hyperplaneSectionHom]
  have h := exists_comp_projectiveBundleMapOfEpi_iff q S.σ S.τ S.σ' S.hsplit S.hσu f
  constructor
  · intro hf
    rw [h.mp hf, comp_zero]
  · intro hf
    apply h.mpr
    exact (cancel_epi ((Scheme.Modules.pullback f).map
      (Scheme.Modules.pullbackUnitIso (projectiveBundleToBase X F)).inv)).mp
        (by simpa only [comp_zero] using hf)

/-- Equality of genuine ideal sheaves, retaining every nilpotent. -/
theorem zeroIdeal_eq_kernel : zeroIdeal q S = (projectiveBundleMapOfEpi q).ker := by
  apply SectionZeroSubbundle.ideal_eq_of_all_factors
  intro T f
  dsimp only [zeroIdeal]
  rw [← SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (tautologicalDatumTwist F) 1 (hyperplaneSection S.σ) f]
  rw [← factors_iff q S f, factorsThrough_ideal_iff_ideal_le_ker]
  constructor
  · rintro ⟨h,hh⟩
    rw [← hh]
    exact h.le_ker_comp _
  · intro h
    exact ⟨IsClosedImmersion.lift (projectiveBundleMapOfEpi q) f h,
      IsClosedImmersion.lift_fac _ _ _⟩

def quotientToZero : projectiveBundle X G ⟶ (zeroIdeal q S).subscheme :=
  IsClosedImmersion.lift (zeroIdeal q S).subschemeι (projectiveBundleMapOfEpi q)
    (by rw [Scheme.IdealSheafData.ker_subschemeι, zeroIdeal_eq_kernel])

@[reassoc]
theorem quotientToZero_fac : quotientToZero q S ≫ (zeroIdeal q S).subschemeι =
    projectiveBundleMapOfEpi q := IsClosedImmersion.lift_fac _ _ _

instance quotientToZero_isIso : IsIso (quotientToZero q S) := by
  apply IsClosedImmersion.isIso_of_ker_eq (projectiveBundleMapOfEpi q)
    (zeroIdeal q S).subschemeι (quotientToZero q S) (quotientToZero_fac q S)
  rw [Scheme.IdealSheafData.ker_subschemeι, zeroIdeal_eq_kernel]

def zeroIsoQuotient : (zeroIdeal q S).subscheme ≅ projectiveBundle X G :=
  (asIso (quotientToZero q S)).symm

variable (hG : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 G)

def zeroIsoBase : (zeroIdeal q S).subscheme ≅ X := by
  letI := isIso_projectiveBundleToBase_of_isInvertible G hG
  exact zeroIsoQuotient q S ≪≫ asIso (projectiveBundleToBase X G)

/-- The isomorphism's projection is the literal original projection. -/
theorem zeroIsoBase_hom : (zeroIsoBase q S hG).hom =
    (zeroIdeal q S).subschemeι ≫ projectiveBundleToBase X F := by
  apply (cancel_epi (quotientToZero q S)).mp
  change quotientToZero q S ≫
      ((zeroIsoQuotient q S).hom ≫ projectiveBundleToBase X G) = _
  rw [← Category.assoc]
  change (quotientToZero q S ≫ inv (quotientToZero q S)) ≫
      projectiveBundleToBase X G = _
  rw [IsIso.hom_inv_id, Category.id_comp, ← Category.assoc, quotientToZero_fac,
    projectiveBundleMapOfEpi_comp_toBase]

end M9Native.SplitLineProjectiveZero
