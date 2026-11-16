module

public import M9StacksIntegration.FiniteFreeBasisPullback
public import M9StacksIntegration.LagrangianFreeMatrixPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorComparison

/-! Canonical finite-basis coordinates for an actual associated sheaf and
its pullback. The basis-section formula is proved from the coproduct
universal property used by the native `tildeFinsupp` construction. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module

universe u

namespace M9Native.MukaiConstantFreeBasis

variable (R : CommRingCat.{u}) (ι : Type u)

theorem tildeFinsupp_lsingle (i : ι) :
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
      (tildeFinsupp (R := R) ι).hom =
      (tildeSelf (R := R)).hom ≫ SheafOfModules.ιFree i := by
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R ι)) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R ι)
  let e : (Discrete.functor fun (_ : ι) => ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ : ι => SheafOfModules.unit (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ => tildeSelf (R := R))
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H)
    (coproductIsCoproduct _) (Discrete.mk i)
  change (𝟙 (tilde (ModuleCat.of R R))) ≫
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
      (tildeFinsupp (R := R) ι).hom = SheafOfModules.ιFree i at h
  simpa only [Category.id_comp, tildeSelf, Iso.refl_hom] using h

theorem tildeSelf_toOpen_one :
    (tildeSelf (R := R)).hom.app ⊤
      ((tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R)) = (1 : Γ(Spec R, ⊤)) := by
  change StructureSheaf.toOpenₗ R R ⊤ 1 = 1
  exact StructureSheaf.const_one ⊤

theorem tildeFinsupp_single_section (i : ι) :
    (tildeFinsupp (R := R) ι).hom.app ⊤
      ((tilde.toOpen (ModuleCat.of R (ι →₀ R)) ⊤).hom (Finsupp.single i 1)) =
      (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i).val.app (op ⊤) (1 : Γ(Spec R, ⊤)) := by
  let z := (tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R)
  have hn := TildeTensor.toOpen_map_app_apply
    (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ⊤ (1 : R)
  have hc := congrArg (fun a => a.app ⊤ z) (tildeFinsupp_lsingle R ι i)
  calc
    _ = (tildeFinsupp (R := R) ι).hom.app ⊤
        ((tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R)))).app ⊤ z) :=
      congrArg (fun t => (tildeFinsupp (R := R) ι).hom.app ⊤ t) hn.symm
    _ = (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i).val.app (op ⊤)
        ((tildeSelf (R := R)).hom.app ⊤ z) := hc
    _ = _ := congrArg ((SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i).val.app (op ⊤))
      (tildeSelf_toOpen_one R)

def tildeBasisIso (M : ModuleCat.{u} R) (b : Basis ι R M) :
    tilde M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) ι :=
  (tilde.functor R).mapIso (LinearEquiv.toModuleIso
    (X₁ := M) (X₂ := ModuleCat.of R (ι →₀ R)) b.repr) ≪≫
    tildeFinsupp (R := R) ι

theorem tildeBasisIso_basis (M : ModuleCat.{u} R) (b : Basis ι R M) (i : ι) :
    (tildeBasisIso R ι M b).hom.app ⊤ ((tilde.toOpen M ⊤).hom (b i)) =
      (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i).val.app (op ⊤) (1 : Γ(Spec R, ⊤)) := by
  have h := TildeTensor.toOpen_map_app_apply
    (ModuleCat.ofHom b.repr.toLinearMap) ⊤ (b i)
  change (tildeFinsupp (R := R) ι).hom.app ⊤
    ((tilde.map (ModuleCat.ofHom b.repr.toLinearMap)).app ⊤
      ((tilde.toOpen M ⊤).hom (b i))) = _
  calc
    _ = (tildeFinsupp (R := R) ι).hom.app ⊤
        ((tilde.toOpen (ModuleCat.of R (ι →₀ R)) ⊤).hom (b.repr (b i))) :=
      congrArg (fun t => (tildeFinsupp (R := R) ι).hom.app ⊤ t) h
    _ = _ := by rw [Basis.repr_self]; exact tildeFinsupp_single_section R ι i

open AlgebraicGeometry.Grassmannian LagrangianMatrixChart
open SectionZeroIdealFactorization LagrangianFreeMatrixPullback

/-- The actual pulled constant module, in the chosen finite basis. -/
def constantBasisIso {X : Scheme.{u}} (f : X ⟶ Spec R) (M : ModuleCat.{u} R)
    (r : ℕ) (b : Basis (ULift.{u} (Fin r)) R M) :
    (Scheme.Modules.pullback f).obj (tilde M) ≅ freeOn X r :=
  (Scheme.Modules.pullback f).mapIso (tildeBasisIso R (ULift.{u} (Fin r)) M b) ≪≫
    pullbackFreeIso f r

/-- Every original ground-field basis section maps to the corresponding
native free basis section, with scalar exactly one. -/
theorem constantBasisIso_basis {X : Scheme.{u}} (f : X ⟶ Spec R) (M : ModuleCat.{u} R)
    (r : ℕ) (b : Basis (ULift.{u} (Fin r)) R M) (i : Fin r) :
    (constantBasisIso R f M r b).hom.app ⊤
      (pullbackGlobalSections f (tilde M) ((tilde.toOpen M ⊤).hom (b (ULift.up i)))) =
      freeBasisSection X r i := by
  change (pullbackFreeIso f r).hom.app ⊤
    (((Scheme.Modules.pullback f).map
      (tildeBasisIso R (ULift.{u} (Fin r)) M b).hom).app ⊤
      (pullbackGlobalSections f (tilde M) ((tilde.toOpen M ⊤).hom (b (ULift.up i))))) = _
  rw [pullback_map_app_pullbackGlobalSections, tildeBasisIso_basis]
  exact FiniteFreeBasisPullback.freeBasisSection_pullback f r i

def baseScalar {X : Scheme.{u}} (f : X ⟶ Spec R) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom

def topSection (M : ModuleCat.{u} R) (m : M) : Γ(tilde M, ⊤) :=
  TildeTensor.topSec M m

theorem topSection_sum (M : ModuleCat.{u} R) {I : Type*} (S : Finset I) (a : I → M) :
    topSection R M (∑ i ∈ S, a i) = ∑ i ∈ S, topSection R M (a i) :=
  map_sum (tilde.toOpen M ⊤).hom a S

theorem topSec_smul (M : ModuleCat.{u} R) (a : R) (m : M) :
    topSection R M (a • m) =
      (Scheme.ΓSpecIso R).inv.hom a • topSection R M m := by
  have h := TildeTensor.topSec_smul M a m
  have hc : TildeTensor.cTop a = (Scheme.ΓSpecIso R).inv.hom a := by
    change ((Spec R).presheaf.map (𝟙 (op (⊤ : (Spec R).Opens)))).hom
      ((Scheme.ΓSpecIso R).inv.hom a) = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hc] at h
  exact h

theorem pulled_topSec_smul {X : Scheme.{u}} (f : X ⟶ Spec R)
    (M : ModuleCat.{u} R) (a : R) (m : M) :
    pullbackGlobalSections f (tilde M) (topSection R M (a • m)) =
      baseScalar R f a • pullbackGlobalSections f (tilde M) (topSection R M m) := by
  rw [topSec_smul, SectionsEqualizer.pullbackGlobalSections_smul]
  rfl

/-- Literal coordinates of every original constant section, with the
actual structural ring homomorphism on its coefficients. -/
theorem constantBasisIso_coordinates {X : Scheme.{u}} (f : X ⟶ Spec R)
    (M : ModuleCat.{u} R) (r : ℕ) (b : Basis (ULift.{u} (Fin r)) R M)
    (m : M) (i : Fin r) :
    freeSectionCoordinates X r
      ((constantBasisIso R f M r b).hom.app ⊤
        (pullbackGlobalSections f (tilde M) ((tilde.toOpen M ⊤).hom m))) i =
      baseScalar R f (b.repr m (ULift.up i)) := by
  classical
  have hsec : pullbackGlobalSections f (tilde M) (topSection R M m) =
      ∑ j : ULift.{u} (Fin r), baseScalar R f (b.repr m j) •
        pullbackGlobalSections f (tilde M) (topSection R M (b j)) := by
    conv_lhs => rw [← b.sum_repr m]
    rw [topSection_sum]
    simp only [map_sum, pulled_topSec_smul]
  change freeSectionCoordinates X r
    ((constantBasisIso R f M r b).hom.app ⊤
      (pullbackGlobalSections f (tilde M) (topSection R M m))) i = _
  rw [hsec]
  have hb (j : ULift.{u} (Fin r)) :
      (constantBasisIso R f M r b).hom.app ⊤
        (pullbackGlobalSections f (tilde M) (topSection R M (b j))) =
      freeBasisSection X r j.down := constantBasisIso_basis R f M r b j.down
  simp only [map_sum, Scheme.Modules.Hom.app_smul, hb, map_smul,
    Finset.sum_apply, Pi.smul_apply, freeCoordinates_basis, smul_eq_mul]
  have hi (j : ULift.{u} (Fin r)) : i = j.down ↔ j = ULift.up i := by
    cases j
    simp [eq_comm]
  simp [hi]

end M9Native.MukaiConstantFreeBasis
