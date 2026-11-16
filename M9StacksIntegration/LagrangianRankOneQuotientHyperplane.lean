module

public import M9StacksIntegration.SymplecticRankOneFactor
public import M9StacksIntegration.LagrangianHyperplaneEpimorphism

/-!
# An actual rank-one quotient image produces an original hyperplane cokernel

For any original test scheme, an actual epimorphic quotient of its
restricted universal rank-three bundle whose original six-section image
has dimension at most one is an epimorphic quotient of an actual original
symplectic hyperplane cokernel. The nonzero original vector, functional,
whole-sheaf factorization and epimorphism are constructed internally.

No target hyperplane, model, reducedness, section basis, or desired
cokernel comparison is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianRankOneQuotientHyperplane

open LagrangianMatrixChart LagrangianUniversalSections
open LagrangianHyperplaneEvaluation LagrangianHyperplaneEpimorphism
open LagrangianAffineDeterminant LagrangianSectionGeneration

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (l : X ⟶ LagrangianGrassmannian.space K)

abbrev originalQuotientSections {T : X.Modules} (p : bundle K l ⟶ T) :
    (Fin 6 → K) →ₗ[K] cohomologyOverField K f T 0 :=
  (cohomologyOverFieldMap K f p 0).hom.comp (LagrangianUniversalSections.sectionMap K f l)

/-- The original six-section rank bound yields an actual whole-sheaf symplectic factor. -/
theorem exists_functional_factor {T : X.Modules} (p : bundle K l ⟶ T)
    (hp : Module.finrank K (LinearMap.range (originalQuotientSections K f l p)) ≤ 1) :
    ∃ (v : Fin 6 → K), v ≠ 0 ∧
      ∃ z : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ T,
        quotientMap K l ≫ p = omegaMap K f v ≫ z := by
  classical
  obtain ⟨v,hv,z,hz⟩ := SymplecticRankOneFactor.exists_original_vector_factor K
    (originalQuotientSections K f l p) hp
  let zs : Γ(T,⊤) := (cohomologyOverFieldZeroLinearIso K f T).hom z
  refine ⟨v,hv,Scheme.Modules.unitHomEquivTop T zs,?_⟩
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin 6)))
  intro i
  apply unitHom_ext_top_one
  change p.app ⊤ ((quotientMap K l).app ⊤ (freeBasisSection X 6 i.down)) =
    (Scheme.Modules.unitHomEquivTop T zs).app ⊤
      ((omegaMap K f v).app ⊤ (freeBasisSection X 6 i.down))
  have hbas : constantVector K f (Pi.single i.down 1) = freeBasisSection X 6 i.down := by
    simp [constantVector, Pi.single_apply]
  have homega := omegaMap_constant_pairing K f v (Pi.single i.down 1)
  rw [hbas] at homega
  rw [homega]
  have hscalar : ∀ a : Γ(X,⊤), (Scheme.Modules.unitHomEquivTop T zs).app ⊤ a = a • zs := by
    intro a
    calc
      (Scheme.Modules.unitHomEquivTop T zs).app ⊤ a =
          (Scheme.Modules.unitHomEquivTop T zs).app ⊤ (a • (1 : Γ(X,⊤))) := by
            congr 1
            exact (mul_one a).symm
      _ = a • (Scheme.Modules.unitHomEquivTop T zs).app ⊤ (1 : Γ(X,⊤)) :=
        Scheme.Modules.Hom.app_smul _ a _
      _ = a • zs := by rw [unitHom_top_one]
  rw [hscalar]
  have hh := congrArg ((cohomologyOverFieldZeroLinearIso K f T).hom)
    (hz (Pi.single i.down 1))
  change (cohomologyOverFieldZeroLinearIso K f T).hom
      ((cohomologyOverFieldMap K f p 0) (LagrangianUniversalSections.sectionMap K f l
        (Pi.single i.down 1))) =
    (cohomologyOverFieldZeroLinearIso K f T).hom
      (LagrangianRing.omega K v (Pi.single i.down 1) • z) at hh
  rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap,
    LagrangianUniversalSections.sectionMap_basis] at hh
  have hfieldscalar (a : K) : (cohomologyOverFieldZeroLinearIso K f T).hom (a • z) =
      ExteriorEvaluation.baseRingMap K f a • zs :=
    (cohomologyOverFieldZeroLinearIso K f T).hom.hom.map_smul a z
  rw [hfieldscalar] at hh
  simpa only [sectionH0, Iso.inv_hom_id_apply, quotientSection] using hh

/-- The actual quotient descends epimorphically from an actual original hyperplane cokernel. -/
theorem exists_hyperplaneCokernel_epi {T : X.Modules} (p : bundle K l ⟶ T) [Epi p]
    (hp : Module.finrank K (LinearMap.range (originalQuotientSections K f l p)) ≤ 1) :
    ∃ (v : Fin 6 → K), v ≠ 0 ∧
      ∃ a : hyperplaneCokernel K f l v ⟶ T, Epi a := by
  obtain ⟨v,hv,z,hz⟩ := exists_functional_factor K f l p hp
  have hzero : hyperplaneEvaluation K f l v ≫ p = 0 := by
    change (kernel.ι (omegaMap K f v) ≫ quotientMap K l) ≫ p = 0
    rw [Category.assoc, hz, ← Category.assoc, kernel.condition, zero_comp]
  let a := cokernel.desc (hyperplaneEvaluation K f l v) p hzero
  refine ⟨v,hv,a,?_⟩
  exact epi_of_epi_fac (cokernel.π_desc (hyperplaneEvaluation K f l v) p hzero)

end M9Native.LagrangianRankOneQuotientHyperplane
