/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modified thin replay, 2026-11-14, of AxiomMath/Stacks at commit
c496df0d9beea9deaeabcea8492605f9a0a2313b. The exact source files and
SHA256 hashes are recorded in audits/section-zero-ideal/provenance.json.
Changes: use only the small compiled provider closure; move declarations
into the project namespace; spell the zero ideal by its literal native
construction; derive finite presentation directly from the native provider;
replay the affine-frame basis without the unrelated higher-direct-image wrapper.
-/
module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# The actual section-zero ideal and its factorization property

The ideal is literally `IdealSheafData.ofIdeals` applied to evaluation
against all linear forms on each affine open. The proofs below replay the
native finite locally free argument over the actual bundle and section.
There is no hypothesis asserting a factorization property.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace M9Native.SectionZeroIdealFactorization

open Stacks.SheafOfModules Stacks.Divisors

/-- The native dual-evaluation ideal of an actual global section. -/
def sectionZeroIdeal (X : Scheme.{u}) (F : X.Modules) (s : Γ(F, ⊤)) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (fun U =>
    Ideal.span {a : Γ(X, U.1) | ∃ φ : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1),
      a = φ (F.presheaf.map (homOfLE le_top).op s)})


/-- The sections of a finite locally free module over an affine open form a finitely presented
module over the functions on that open. -/
theorem finitePresentation_sections {X : Scheme.{u}} (F : X.Modules)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (U : X.affineOpens) :
    Module.FinitePresentation Γ(X, U.1) Γ(F, U.1) :=
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  have : F.IsFinitePresentation :=
    Stacks.FiniteLocallyFree.isFinitePresentation F
  AlgebraicGeometry.affineSections_of_isFinitePresentation F U.2

/-- The ideal of values of linear forms at a section of a finite locally free module commutes
with restriction to a principal open of an affine open. -/
theorem evalSpan_map_basicOpen {X : Scheme.{u}} (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (s : Γ(F, ⊤)) (U : X.affineOpens) (f : Γ(X, U.1)) :
    Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        (Ideal.span {a : Γ(X, U.1) | ∃ φ : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1),
          a = φ (F.presheaf.map (homOfLE le_top).op s)}) =
      Ideal.span {a : Γ(X, X.basicOpen f) |
        ∃ φ : Γ(F, X.basicOpen f) →ₗ[Γ(X, X.basicOpen f)] Γ(X, X.basicOpen f),
          a = φ (F.presheaf.map (homOfLE le_top).op s)} := by
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  let : IsLocalization (Submonoid.powers f) Γ(X, X.basicOpen f) :=
    AlgebraicGeometry.isLocalization_basicOpen_of_qcqs U.2.isCompact U.2.isQuasiSeparated f
  let : Module Γ(X, U.1) Γ(F, X.basicOpen f) :=
    Module.compHom Γ(F, X.basicOpen f)
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsLocalizedModule.Away f
      (Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le f))) :=
    AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F U.2.isCompact
      U.2.isQuasiSeparated f
  let : Module.FinitePresentation Γ(X, U.1) Γ(F, U.1) := finitePresentation_sections F U
  have hEval := Stacks.Divisors.evalSpan_map_of_isLocalizedModule (R := Γ(X, U.1))
    (S := Γ(X, X.basicOpen f)) (M := Γ(F, U.1)) (Mₛ := Γ(F, X.basicOpen f))
    (Submonoid.powers f)
    (Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le f)))
    (F.presheaf.map (homOfLE le_top).op s)
  have hres : Scheme.Modules.restrictionLinearMap F (homOfLE (X.basicOpen_le f))
      (F.presheaf.map (homOfLE le_top).op s) = F.presheaf.map (homOfLE le_top).op s := by
    change F.presheaf.map (homOfLE (X.basicOpen_le f)).op
      (F.presheaf.map (homOfLE le_top).op s) = _
    exact congrArg (fun k => (ConcreteCategory.hom k) s)
      (((F.presheaf.map_comp (homOfLE le_top).op (homOfLE (X.basicOpen_le f)).op).symm.trans
        (congrArg F.presheaf.map (Subsingleton.elim _ _))) :
          F.presheaf.map (homOfLE le_top).op ≫
              F.presheaf.map (homOfLE (X.basicOpen_le f)).op =
            F.presheaf.map (homOfLE (show X.basicOpen f ≤ ⊤ from le_top)).op)
  rw [hres] at hEval
  exact hEval

/-- **The defining ideal of the zero scheme of a section of a finite locally free module.** On
an affine open `U` the ideal of `Z(s)` is generated by the values `φ (s|_U)` of the
`Γ(X, U)`-linear forms on `Γ(ℰ, U)`: the prescribed affine-local family is already an ideal
sheaf, so `Scheme.IdealSheafData.ofIdeals` leaves it untouched. -/
theorem sectionZeroIdeal_ideal {X : Scheme.{u}} (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (s : Γ(F, ⊤)) (U : X.affineOpens) :
    (sectionZeroIdeal X F s).ideal U =
      Ideal.span {a : Γ(X, U.1) | ∃ φ : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1),
        a = φ (F.presheaf.map (homOfLE le_top).op s)} := by
  classical
  let A : ∀ V : X.affineOpens, Ideal Γ(X, V.1) := fun V =>
    Ideal.span {a : Γ(X, V.1) | ∃ φ : Γ(F, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1),
      a = φ (F.presheaf.map (homOfLE le_top).op s)}
  have hmap (V : X.affineOpens) (g : Γ(X, V.1)) :
      (A V).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
        A (X.affineBasicOpen g) :=
    evalSpan_map_basicOpen F s V g
  let J : X.IdealSheafData := { ideal := A, map_ideal_basicOpen := hmap }
  change (Scheme.IdealSheafData.ofIdeals A).ideal U = A U
  rw [show A = J.ideal from rfl, Scheme.IdealSheafData.ofIdeals_ideal J]

/-- **The ideal of values of all linear forms is generated by the coordinates.** If
`m = ∑ᵢ ψᵢ(m) • vᵢ` for every `m`, then the values at `m` of all linear forms generate the same
ideal as the coordinates `ψᵢ(m)`. -/
theorem span_eval_eq_span_coord {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] (ψ : ι → M →ₗ[R] R) (v : ι → M)
    (hdec : ∀ m, m = ∑ i, ψ i m • v i) (m : M) :
    Ideal.span {a : R | ∃ φ : M →ₗ[R] R, a = φ m} = Ideal.span (Set.range fun i => ψ i m) := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro a ⟨φ, rfl⟩
    have h : φ m = ∑ i, ψ i m * φ (v i) := by
      conv_lhs => rw [hdec m]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [h]
    refine Ideal.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · refine Ideal.span_le.2 ?_
    rintro a ⟨i, rfl⟩
    exact Ideal.subset_span ⟨ψ i, rfl⟩


section FrameNeighborhood

variable {X : Scheme.{u}} (F : X.Modules)

/-- A trivialization of a module over an open restricts to a trivialization over every smaller
open. -/
def restrictIsoFreeOfLE {I : Type u} {U V : X.Opens} (h : V ≤ U)
    (e : F.restrict U.ι ≅ SheafOfModules.free.{u} I) :
    F.restrict V.ι ≅ SheafOfModules.free.{u} I :=
  ((Scheme.Modules.restrictFunctorCongr
        (show X.homOfLE h ≫ U.ι = V.ι by simp)).app F).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app F) ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    (Scheme.Modules.restrictFreeIso (X.homOfLE h) I).symm

/-- **The affine opens trivializing a finite locally free module of rank `r` form a basis.**
Local freeness gives a trivializing neighbourhood of every point, the affine opens are a basis,
and a trivialization restricts to every smaller open. -/
theorem isBasis_frame (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r] :
    Opens.IsBasis {V : X.Opens | IsAffineOpen V ∧
      Nonempty (F.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r)))} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hxU
  obtain ⟨W, hxW, ⟨e⟩⟩ := (Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf F r) x
  have hmem : x ∈ U ⊓ W := ⟨hxU, hxW⟩
  obtain ⟨V, hVmem, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hmem
  exact ⟨V, ⟨hVmem, ⟨restrictIsoFreeOfLE F (hVle.trans inf_le_right) e⟩⟩, hxV,
    hVle.trans inf_le_left⟩


end FrameNeighborhood

/-- Every point of every open has an affine neighbourhood inside that open carrying a frame. -/
theorem exists_frame {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      Nonempty (F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  obtain ⟨U, ⟨hU, he⟩, hxU, hUW⟩ :=
    (Opens.isBasis_iff_nbhd.mp (isBasis_frame F r)) hx
  exact ⟨U, hU, hxU, hUW, he⟩

section Frame

variable {X : Scheme.{u}} (F : X.Modules) {r : ℕ} (U : X.Opens)
  (e : F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r)))

/-- The `i`-th coordinate of a frame, as a morphism of modules `ℰ|_U ⟶ 𝒪_U`. -/
def frameCoordHom (i : ULift.{u} (Fin r)) :
    F.restrict U.ι ⟶ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  e.hom ≫ freeProj i

/-- The scalar actions on the sections of `ℰ|_U` over `⊤` and on those of `ℰ` over `U.ι ''ᵁ ⊤`
agree, through the identifications `Γ(U, ⊤) ≅ Γ(X, U.ι ''ᵁ ⊤)` and
`Γ(ℰ|_U, ⊤) ≅ Γ(ℰ, U.ι ''ᵁ ⊤)`. -/
theorem restrict_smul_eq (a : Γ(X, U.ι ''ᵁ ⊤)) (m : Γ(F.restrict U.ι, ⊤)) :
    (Scheme.Modules.restrictAppIso U.ι F ⊤).hom ((Scheme.Hom.appIso U.ι ⊤).hom a • m) =
      a • (Scheme.Modules.restrictAppIso U.ι F ⊤).hom m := by
  have h2 := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι F ⊤
    ((Scheme.Hom.appIso U.ι ⊤).hom a) m
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply] at h2
  exact h2

omit F in
/-- The identification `Γ(X, U.ι ''ᵁ ⊤) ≅ Γ(U, ⊤)` sends each section to itself. -/
theorem appIso_ι_hom_apply (a : Γ(X, U.ι ''ᵁ ⊤)) : (Scheme.Hom.appIso U.ι ⊤).hom a = a := by
  rw [Scheme.Opens.ι_appIso]
  exact CategoryTheory.id_apply a

/-- The scalar action of `Γ(X, U.ι ''ᵁ ⊤)` on `Γ(ℰ, U.ι ''ᵁ ⊤)` is the action of `Γ(U, ⊤)` on
`Γ(ℰ|_U, ⊤)`. -/
theorem restrict_smul_eq' (a : Γ(X, U.ι ''ᵁ ⊤)) (m : Γ(F, U.ι ''ᵁ ⊤)) :
    a • m = @HSMul.hSMul Γ(U.toScheme, ⊤) Γ(F.restrict U.ι, ⊤) Γ(F.restrict U.ι, ⊤) instHSMul
      a m :=
  ((congrArg (fun y : Γ(F, U.ι ''ᵁ ⊤) => a • y) (CategoryTheory.id_apply m)).symm.trans
    (restrict_smul_eq F U a m).symm).trans
    ((CategoryTheory.id_apply _).trans
      (congrArg (fun c : Γ(U.toScheme, ⊤) =>
        @HSMul.hSMul Γ(U.toScheme, ⊤) Γ(F.restrict U.ι, ⊤) Γ(F.restrict U.ι, ⊤) instHSMul c m)
        (appIso_ι_hom_apply U a)))

/-- **The `i`-th coordinate form of a frame.** -/
def frameCoord (i : ULift.{u} (Fin r)) :
    Γ(F, U.ι ''ᵁ ⊤) →ₗ[Γ(X, U.ι ''ᵁ ⊤)] Γ(X, U.ι ''ᵁ ⊤) where
  toFun m := (frameCoordHom F U e i).app ⊤ m
  map_add' a b := map_add _ a b
  map_smul' a m :=
    (congrArg (fun y => (frameCoordHom F U e i).app ⊤ y) (restrict_smul_eq' F U a m)).trans
      (((frameCoordHom F U e i).val.app (op ⊤)).hom.map_smul a m)

/-- **The `i`-th frame vector.** -/
def frameVec (i : ULift.{u} (Fin r)) : Γ(F, U.ι ''ᵁ ⊤) :=
  (SheafOfModules.ιFree i ≫ e.inv).val.app (op ⊤) (unitOne (op ⊤))

/-- The `i`-th coordinate form of a frame is `frameCoordHom` evaluated on sections over `⊤`. -/
theorem frameCoord_apply (i : ULift.{u} (Fin r)) (m : Γ(F, U.ι ''ᵁ ⊤)) :
    frameCoord F U e i m = (frameCoordHom F U e i).app ⊤ m :=
  rfl

/-- The coordinates of a section are those of its image in the free module. -/
theorem frameCoord_eq_freeCoord (i : ULift.{u} (Fin r)) (m : Γ(F, U.ι ''ᵁ ⊤)) :
    frameCoord F U e i m = freeCoord (op ⊤) (e.hom.val.app (op ⊤) m) i :=
  rfl

/-- **The expansion of a section in a frame**: `m = ∑ᵢ cᵢ(m) bᵢ`. -/
theorem eq_sum_frameCoord_smul_frameVec (m : Γ(F, U.ι ''ᵁ ⊤)) :
    m = ∑ i, frameCoord F U e i m • frameVec F U e i := by
  classical
  have h1 :
      m = e.inv.val.app (op ⊤) (freeMk (op ⊤) (freeCoord (op ⊤) (e.hom.val.app (op ⊤) m))) := by
    rw [freeMk_freeCoord]
    exact (Stacks.SheafOfModules.inv_val_app_hom_val_app e (op ⊤) m).symm
  have h2 := app_freeMk e.inv (op ⊤) (freeCoord (op ⊤) (e.hom.val.app (op ⊤) m))
  rw [h2] at h1
  refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (restrict_smul_eq' F U (frameCoord F U e i m) (frameVec F U e i)).symm

/-- **The zero scheme on an affine open carrying a frame is cut out by the coordinates.** -/
theorem sectionZeroIdeal_ideal_frame
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (s : Γ(F, ⊤))
    (hU : IsAffineOpen (U.ι ''ᵁ ⊤)) :
    (sectionZeroIdeal X F s).ideal ⟨U.ι ''ᵁ ⊤, hU⟩ =
      Ideal.span (Set.range fun i =>
        frameCoord F U e i (F.presheaf.map (homOfLE le_top).op s)) := by
  rw [sectionZeroIdeal_ideal F s ⟨U.ι ''ᵁ ⊤, hU⟩]
  exact span_eval_eq_span_coord (frameCoord F U e) (frameVec F U e)
    (eq_sum_frameCoord_smul_frameVec F U e) _

end Frame


/-- The open image of the top of an affine open is affine. -/
theorem isAffineOpen_image_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (U.ι ''ᵁ ⊤) := by
  rwa [Scheme.Opens.ι_image_top]

/-- The coordinate forms and frame vectors of a frame decompose the identity. -/
theorem id_eq_sum_frame {X : Scheme.{u}} {M : X.Modules} {r : ℕ}
    (e : M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    𝟙 M = ∑ i, (e.hom ≫ freeProj i) ≫ (SheafOfModules.ιFree i ≫ e.inv) := by
  classical
  refine (e.hom_inv_id.symm.trans
    ((congrArg (fun φ => e.hom ≫ φ) (Category.id_comp e.inv).symm).trans
      (congrArg (fun φ => e.hom ≫ φ ≫ e.inv) id_free_eq_sum))).trans ?_
  exact (congrArg (fun φ => e.hom ≫ φ) (Preadditive.sum_comp _ _ _)).trans
    ((Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun i _ =>
      (congrArg (fun φ => e.hom ≫ φ) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm))

/-- Pulling back sections is natural in the module. -/
theorem pullback_map_app_pullbackGlobalSections {X Y : Scheme.{u}} (g : Y ⟶ X) {M N : X.Modules}
    (φ : M ⟶ N) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullbackGlobalSections g M m) =
      pullbackGlobalSections g N (φ.app ⊤ m) :=
  (congrArg (fun z => ((Scheme.Modules.pullback g).map φ).app ⊤ z)
      (congrArg (fun ψ : Γ(M, ⊤) ⟶ Γ((Scheme.Modules.pullback g).obj M, ⊤) => ψ m)
        (pullbackGlobalSections_eq_unit g M))).trans
    ((pullbackGlobalSections_naturality g φ m).trans
      (congrArg (fun ψ : Γ(N, ⊤) ⟶ Γ((Scheme.Modules.pullback g).obj N, ⊤) =>
          ψ (φ.app ⊤ m)) (pullbackGlobalSections_eq_unit g N)).symm)

/-- Pulling back a composite acts on sections as the composite of the pullbacks. -/
theorem pullback_map_comp_app_apply {X Y : Scheme.{u}} (g : Y ⟶ X) {M N P : X.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (x : Γ((Scheme.Modules.pullback g).obj M, ⊤)) :
    ((Scheme.Modules.pullback g).map (a ≫ b)).app ⊤ x =
      ((Scheme.Modules.pullback g).map b).app ⊤ (((Scheme.Modules.pullback g).map a).app ⊤ x) := by
  rw [Functor.map_comp]
  rfl

/-- A finite sum of morphisms of modules acts on sections as the sum of the actions. -/
theorem sum_app_apply {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} (t : Finset ι)
    (φ : ι → (M ⟶ N)) (U : X.Opens) (m : Γ(M, U)) :
    (∑ i ∈ t, φ i).app U m = ∑ i ∈ t, (φ i).app U m :=
  Stacks.SheafOfModules.app_sum t φ (Opposite.op U) m

/-- **Over a frame, a pulled-back section vanishes exactly when the pullbacks of its coordinates
do.** -/
theorem pullbackGlobalSections_eq_zero_iff_frame {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    {r : ℕ} (e : M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) (m : Γ(M, ⊤))
    [(SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint]
    [(TopologicalSpace.Opens.map g.base).Final]
    [IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)] :
    pullbackGlobalSections g M m = 0 ↔
      ∀ i, g.app ⊤ ((e.hom ≫ freeProj i).app ⊤ m) = 0 := by
  have hunit : ∀ a : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤),
      pullbackGlobalSections g (SheafOfModules.unit X.ringCatSheaf) a = 0 ↔ g.app ⊤ a = 0 :=
    fun a => pullbackGlobalSections_eq_zero_iff_frame_appTop g _ (Iso.refl _) a
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · exact (hunit _).mp ((pullback_map_app_pullbackGlobalSections g _ m).symm.trans
      ((congrArg (fun z => ((Scheme.Modules.pullback g).map (e.hom ≫ freeProj i)).app ⊤ z) h).trans
        (map_zero _)))
  · have hi : ∀ i, ((Scheme.Modules.pullback g).map (e.hom ≫ freeProj i)).app ⊤
        (pullbackGlobalSections g M m) = 0 := fun i =>
      (pullback_map_app_pullbackGlobalSections g _ m).trans ((hunit _).mpr (h i))
    have hid : pullbackGlobalSections g M m =
        ((Scheme.Modules.pullback g).map (𝟙 M)).app ⊤ (pullbackGlobalSections g M m) := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hid, id_eq_sum_frame e, Functor.map_sum, sum_app_apply]
    exact Finset.sum_eq_zero fun i _ => (pullback_map_comp_app_apply g _ _ _).trans
      ((congrArg (fun z => ((Scheme.Modules.pullback g).map
        (SheafOfModules.ιFree i ≫ e.inv)).app ⊤ z) (hi i)).trans (map_zero _))

/-- Over a frame `(U, e)`, the pulled-back section vanishes on `f⁻¹(U)` exactly when the
pullbacks of the coordinates of `s|_U` vanish. -/
theorem pullbackGlobalSections_local_frame_iff {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    (s : Γ(F, ⊤)) (U : X.Opens) {r : ℕ}
    (e : F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (show (f ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
        (pullbackGlobalSections f F s) = 0 ↔
      ∀ i, f.app (U.ι ''ᵁ ⊤) (frameCoord F U e i (F.presheaf.map (homOfLE le_top).op s)) = 0 := by
  let g := f ∣_ U
  have hcomp : g ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  rw [← pullbackGlobalSections_open_eq_zero_iff,
    ← pullbackGlobalSections_comp_eq_zero_iff, ← hcomp,
    pullbackGlobalSections_comp_eq_zero_iff, ← pullbackGlobalSections_open U.ι F s]
  have : (TopologicalSpace.Opens.map g.base).Final := opensMap_final g
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal g.toRingCatSheafHom
  refine Iff.trans (pullbackGlobalSections_hom_eq_zero_iff g
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app F)
    (F.presheaf.map (homOfLE le_top).op s)) ?_
  refine Iff.trans (pullbackGlobalSections_eq_zero_iff_frame g (F.restrict U.ι) e
    (F.presheaf.map (homOfLE le_top).op s)) ?_
  refine forall_congr' fun i => ?_
  change g.app ⊤ ((e.hom ≫ freeProj i).app ⊤ (F.presheaf.map (homOfLE le_top).op s)) = 0 ↔
    f.app (U.ι ''ᵁ ⊤) ((e.hom ≫ freeProj i).app ⊤ (F.presheaf.map (homOfLE le_top).op s)) = 0
  dsimp only [g]
  rw [morphismRestrict_app]
  exact map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).injective

/-- Over an affine open carrying a frame, the pulled-back section vanishes on `f⁻¹(U)` exactly
when the ideal of the zero scheme on `U` is carried to zero by `f`. -/
theorem pullbackGlobalSections_local_ideal_iff {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (s : Γ(F, ⊤)) (U : X.affineOpens) {r : ℕ}
    (e : F.restrict U.1.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (show f ⁻¹ᵁ U.1 ≤ ⊤ from le_top)).op
        (pullbackGlobalSections f F s) = 0 ↔
      (sectionZeroIdeal X F s).ideal U ≤ RingHom.ker (f.app U.1).hom := by
  let W : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤, isAffineOpen_image_top U.2⟩
  have hW : W = U := Subtype.ext (by simp [W])
  have h := pullbackGlobalSections_local_frame_iff f F s U.1 e
  have hspan : (sectionZeroIdeal X F s).ideal W ≤ RingHom.ker (f.app W.1).hom ↔
      ∀ i, f.app W.1 (frameCoord F U.1 e i (F.presheaf.map (homOfLE le_top).op s)) = 0 := by
    rw [sectionZeroIdeal_ideal_frame F U.1 e s W.2, Ideal.span_le, Set.range_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    rfl
  rw [← hspan, hW] at h
  exact (restriction_eq_zero_congr ((Scheme.Modules.pullback f).obj F)
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U.1)).symm (pullbackGlobalSections f F s)).trans h

/-- **The universal property of the zero scheme, [Stacks, Tag 02OR] for a module of any rank.**
A global section `s` of a finite locally free module `ℰ` on `X` vanishes after pullback along
`f : Y ⟶ X` if and only if `f` factors through the zero scheme of `s`. -/
theorem pullbackGlobalSections_eq_zero_iff_factorsThrough {X : Scheme.{u}} (F : X.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (s : Γ(F, ⊤)) {Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackGlobalSections f F s = 0 ↔
      ∃ g : Y ⟶ (sectionZeroIdeal X F s).subscheme,
        g ≫ (sectionZeroIdeal X F s).subschemeι = f := by
  classical
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  rw [_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker]
  refine ⟨fun hs => ?_, fun hI => ?_⟩
  · apply ideal_le_ker_of_locally f (sectionZeroIdeal X F s)
    intro W x hx
    obtain ⟨U, hU, hxU, hUW, ⟨e⟩⟩ := exists_frame F r (W := W.1) hx
    refine ⟨⟨U, hU⟩, hxU, hUW, ?_⟩
    apply (pullbackGlobalSections_local_ideal_iff f F s ⟨U, hU⟩ e).mp
    simp [hs]
  · choose U hU hy _ e using fun y : Y => exists_frame F r (W := ⊤) (x := f y) trivial
    let V (y : Y) : Y.Opens := f ⁻¹ᵁ (U y)
    let G : TopCat.Sheaf AddCommGrpCat Y :=
      ⟨((Scheme.Modules.pullback f).obj F).presheaf,
        ((Scheme.Modules.pullback f).obj F).isSheaf⟩
    have hcover : (⊤ : Y.Opens) ≤ ⨆ y, V y := fun y _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
    apply G.eq_of_locally_eq' V ⊤ (fun _ => homOfLE le_top) hcover
    intro y
    simpa only [map_zero] using (pullbackGlobalSections_local_ideal_iff f F s ⟨U y, hU y⟩
      (e y).some).mpr ((hI ⟨U y, hU y⟩).trans (f.ideal_ker_le ⟨U y, hU y⟩))

/-- The section `s` vanishes on its zero scheme. -/
theorem pullbackGlobalSections_subschemeι_eq_zero {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (s : Γ(F, ⊤)) :
    pullbackGlobalSections (sectionZeroIdeal X F s).subschemeι F s = 0 :=
  (pullbackGlobalSections_eq_zero_iff_factorsThrough F r s
    (sectionZeroIdeal X F s).subschemeι).2 ⟨𝟙 _, by simp⟩

/-- **[Stacks, Tag 0B6Y] for a module of any rank.** The zero scheme of the pulled-back section
is the scheme-theoretic inverse image of the zero scheme: `Z(f^* s) = f⁻¹(Z(s))`. -/
theorem sectionZeroIdeal_pullback {X X' : Scheme.{u}} (f : X' ⟶ X) (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (s : Γ(F, ⊤)) :
    sectionZeroIdeal X' ((Scheme.Modules.pullback f).obj F) (pullbackGlobalSections f F s) =
      (sectionZeroIdeal X F s).comap f := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback f).obj F) r :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      f.base f.toRingCatSheafHom F r inferInstance
  let D' := sectionZeroIdeal X' ((Scheme.Modules.pullback f).obj F)
    (pullbackGlobalSections f F s)
  let D := sectionZeroIdeal X F s
  let i' := D'.subschemeι
  let i := D.subschemeι
  have hiff {T : Scheme.{u}} (t : T ⟶ X') :
      pullbackGlobalSections t ((Scheme.Modules.pullback f).obj F) (pullbackGlobalSections f F s) =
        0 ↔ pullbackGlobalSections (t ≫ f) F s = 0 := by
    rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp t f F s]
    exact (map_eq_zero_iff _ (pullbackGlobalSections_injective_pullbackComp t f F)).symm
  obtain ⟨g, hg⟩ :=
    (pullbackGlobalSections_eq_zero_iff_factorsThrough F r s (i' ≫ f)).mp ((hiff i').mp
      (pullbackGlobalSections_subschemeι_eq_zero _ r (pullbackGlobalSections f F s)))
  have hpb : IsPullback i' g f i := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk i' g hg.symm) ?_
    choose lift lift_fst using fun c : PullbackCone f i =>
      show ∃ l : c.pt ⟶ D'.subscheme, l ≫ i' = c.fst from
        (pullbackGlobalSections_eq_zero_iff_factorsThrough ((Scheme.Modules.pullback f).obj F) r
          (pullbackGlobalSections f F s) c.fst).mp <| (hiff c.fst).mpr <| by
          rw [c.condition,
            ← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp c.snd i F s,
            pullbackGlobalSections_subschemeι_eq_zero F r s]
          simp
    have lift_snd (c : PullbackCone f i) : lift c ≫ g = c.snd := by
      refine (cancel_mono i).1 ?_
      rw [Category.assoc, hg, ← Category.assoc, lift_fst, c.condition]
    exact PullbackCone.IsLimit.mk hg.symm lift lift_fst lift_snd
      fun c m hleft _ => (cancel_mono i').1 (hleft.trans (lift_fst c).symm)
  calc
    D' = Scheme.Hom.ker i' := (Scheme.IdealSheafData.ker_subschemeι D').symm
    _ = Scheme.Hom.ker (pullback.fst f i) :=
        (congrArg Scheme.Hom.ker hpb.isoPullback_hom_fst).symm.trans
          (Scheme.Hom.ker_comp_of_isIso _ _)
    _ = D.comap f := rfl



/-! ## Evaluation over an affine test scheme

These identities read the pulled-back section through the canonical native
extension-of-scalars isomorphism. They apply in particular to genuine
`Spec K` points, taking the source open to be `⊤`.
-/

open TensorProduct
open scoped ChangeOfRings

/-- The canonical affine base-change comparison sends the tensor of the
restricted original global section to its actual pullback on the source. -/
theorem affineBaseChange_one_tmul_global {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)) {U : X.Opens}
    (hU : IsAffineOpen U) (hY : IsAffineOpen (⊤ : Y.Opens))
    (hYU : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ U) :
    (affinePullbackSectionsBaseChangeIso f F hU hY hYU).hom
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, U), (f.appLE U ⊤ hYU).hom]
          (F.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) =
      pullbackGlobalSections f F s := by
  rw [affinePullbackSectionsBaseChangeIso_one_tmul,
    pullbackSection_res_source f F (le_top : U ≤ ⊤) (by simp) hYU s]
  rfl

/-- Affine base change identifies actual vanishing with the vanishing of
`1 ⊗ s`; no arbitrary vector-space comparison is chosen. -/
theorem pullbackGlobalSections_eq_zero_iff_one_tmul {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤))
    {U : X.Opens} (hU : IsAffineOpen U) (hY : IsAffineOpen (⊤ : Y.Opens))
    (hYU : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ U) :
    pullbackGlobalSections f F s = 0 ↔
      ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, U), (f.appLE U ⊤ hYU).hom]
        (F.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) = 0 := by
  rw [← affineBaseChange_one_tmul_global f F s hU hY hYU]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (affinePullbackSectionsBaseChangeIso f F hU hY hYU).hom).injective

/-- For an actual `Spec K` point, vanishing in the canonical base-change
module is exactly genuine factorization through the native zero subscheme. -/
theorem specPoint_factorsThrough_iff_one_tmul {X : Scheme.{u}}
    (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    (s : Γ(F, ⊤)) (K : Type u) [Field K] (f : Spec (.of K) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U)
    (hKU : (⊤ : (Spec (.of K)).Opens) ≤ f ⁻¹ᵁ U) :
    (∃ g : Spec (.of K) ⟶ (sectionZeroIdeal X F s).subscheme,
      g ≫ (sectionZeroIdeal X F s).subschemeι = f) ↔
    ((1 : Γ(Spec (.of K), ⊤)) ⊗ₜ[Γ(X, U), (f.appLE U ⊤ hKU).hom]
      (F.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) = 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  exact (pullbackGlobalSections_eq_zero_iff_factorsThrough F r s f).symm.trans
    (pullbackGlobalSections_eq_zero_iff_one_tmul f F s hU
      (isAffineOpen_top (Spec (.of K))) hKU)

end M9Native.SectionZeroIdealFactorization

end
