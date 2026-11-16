module

public import M9StacksIntegration.LagrangianSymmetricPullback
public import M9StacksIntegration.LagrangianCotangentSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnitSectionMul

/-! The canonical symmetric pullback comparison preserves the original products of local
sections. The normalization is derived from the native generators and adjunction units. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.LagrangianSymmetricPullbackProduct

open LagrangianSymmetricPullback

variable {X Y : Scheme.{u}}

/-- The original, unrescaled product in the native symmetric square. -/
def product (F : X.Modules) (U : X.Opens) (α β : Γ(F,U)) :
    Γ((Scheme.Modules.symmetricAlgebra X F).piece 2,U) :=
  LagrangianCotangentSections.squareUnit F U
    (SymPow.sqMul LinearMap.id (α ⊗ₜ[Γ(X,U)] β))

theorem generator_eq_unit (F : X.Modules) (U : X.Opens) (α : Γ(F,U)) :
    (Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) α =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
          (PresheafOfModules.symPowInt (O := X.sheaf.obj) 1 F.val)) (op U)
        (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F.val) (op U) α) := by
  change ((PresheafOfModules.symPowIntGradedAlgebra F.val).sheafifyGen
    (𝟙 X.ringCatSheaf.obj) (PresheafOfModules.symPowIntGen F.val)).val.app (op U)
      ((Scheme.Modules.sheafificationIso X F).inv.val.app (op U) α) = _
  have hi : (Scheme.Modules.sheafificationIso X F).inv.val.app (op U) α =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) F.val) (op U) α :=
    PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 X.ringCatSheaf.obj) F (op U) α
  rw [hi]
  exact (PresheafOfModules.symPowIntGradedAlgebra F.val).sheafifyGen_unit
    (𝟙 X.ringCatSheaf.obj) (PresheafOfModules.symPowIntGen F.val) (op U) α

/-- The sheafification-unit product is exactly multiplication of the native generators. -/
theorem product_eq_mul_generators (F : X.Modules) (U : X.Opens) (α β : Γ(F,U)) :
    product F U α β = ((Scheme.Modules.symmetricAlgebra X F).mul 1 1).app (op U)
      ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) α)
      ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) β) := by
  have hp : ((PresheafOfModules.symPowIntGradedAlgebra F.val).mul 1 1).app (op U)
      (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F.val) (op U) α)
      (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F.val) (op U) β) =
        SymPow.sqMul LinearMap.id (α ⊗ₜ[Γ(X,U)] β) := by
    apply Subtype.ext
    rw [SymPow.sqMul_tmul]
    rfl
  have h := (PresheafOfModules.symPowIntGradedAlgebra F.val).sheafify_mul_unit
    (𝟙 X.ringCatSheaf.obj) 1 1 (op U)
    (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F.val) (op U) α)
    (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F.val) (op U) β)
  rw [hp] at h
  rw [generator_eq_unit,generator_eq_unit]
  exact h.symm

/-- The actual functorial map of symmetric squares preserves these products. -/
theorem symmetricMap_product {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens)
    (α β : Γ(F,U)) :
    (symmetricMap φ 2).val.app (op U) (product F U α β) =
      product G U (φ.val.app (op U) α) (φ.val.app (op U) β) := by
  let hF := Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F
  let hG := Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X G
  have hg (x : Γ(F,U)) : ((hF.map hG φ).app 1).val.app (op U)
      ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) x) =
      (Scheme.Modules.symmetricAlgebraGen X G).val.app (op U) (φ.val.app (op U) x) :=
    congrArg (fun ψ => ψ.val.app (op U) x) (hF.map_app_one hG φ)
  have h := (hF.map hG φ).map_mul 1 1 (op U)
    ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) α)
    ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U) β)
  rw [hg,hg] at h
  rw [product_eq_mul_generators,product_eq_mul_generators]
  exact h

/-- The actual ringed-space adjunction unit on local sections. -/
def pullbackUnit (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens) (α : Γ(F,U)) :
    Γ((Scheme.Modules.pullback g).obj F,g ⁻¹ᵁ U) :=
  ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
    F).val.app (op U) α

/-- The corresponding original four-field ringed-topos unit. -/
def fourFieldUnit (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens) (α : Γ(F,U)) :
    Γ(g.zariskiRingedToposModulesHom.pullbackModules.obj F,g ⁻¹ᵁ U) :=
  ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    g.zariskiRingedToposModulesHom).unit.app F).val.app (op U) α

theorem fourFieldUnit_natural (g : X ⟶ Y) {F G : Y.Modules} (φ : F ⟶ G)
    (U : Y.Opens) (α : Γ(F,U)) :
    (g.zariskiRingedToposModulesHom.pullbackModules.map φ).val.app (op (g ⁻¹ᵁ U))
      (fourFieldUnit g F U α) = fourFieldUnit g G U (φ.val.app (op U) α) := by
  have h := congrArg (fun ψ => ψ.val.app (op U) α)
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      g.zariskiRingedToposModulesHom).unit.naturality φ)
  exact h.symm

theorem fourFieldUnit_mul (g : X ⟶ Y)
    (A : SheafOfModules.GradedAlgebra.{u,u} Y.ringCatSheaf) (i j : ℤ)
    (U : Y.Opens) (a : Γ(A.piece i,U)) (b : Γ(A.piece j,U)) :
    ((Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra
      g.zariskiRingedToposModulesHom A).mul i j).app (op (g ⁻¹ᵁ U))
        (fourFieldUnit g (A.piece i) U a) (fourFieldUnit g (A.piece j) U b) =
      fourFieldUnit g (A.piece (i+j)) U ((A.mul i j).app (op U) a b) := by
  let f := g.zariskiRingedSiteHom.toRingedToposHom
  exact (Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_pullbackUnit_mul f
    (op U) (op (g ⁻¹ᵁ U)) (fun _ x => x) (fun _ _ => rfl) A i j a b).symm

/-- The four-field comparison preserves the actual products of unit images. -/
theorem fourFieldSymmetricPullbackIso_product (g : X ⟶ Y) (F : Y.Modules)
    (U : Y.Opens) (α β : Γ(F,U)) :
    (fourFieldSymmetricPullbackIso g F 2).hom.val.app (op (g ⁻¹ᵁ U))
      (product (g.zariskiRingedToposModulesHom.pullbackModules.obj F) (g ⁻¹ᵁ U)
        (fourFieldUnit g F U α) (fourFieldUnit g F U β)) =
      fourFieldUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β) := by
  let f := g.zariskiRingedSiteHom.toRingedToposHom
  let M := g.zariskiRingedToposModulesHom.pullbackModules.obj F
  let c := Stacks.Sheaves.GradedAlgebraEssentiallySmall.symmetricPullbackHom f
    (Scheme.Modules.symmetricAlgebraGen Y F)
    (fun V x y => eq_of_heq (Scheme.Modules.symmetricAlgebra_mul_comm Y F 1 1 V x y))
    (Scheme.Modules.symmetricAlgebraGen X M)
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X M)
  have hg (x : Γ(F,U)) : (c.app 1).val.app (op (g ⁻¹ᵁ U))
      ((Scheme.Modules.symmetricAlgebraGen X M).val.app (op (g ⁻¹ᵁ U))
        (fourFieldUnit g F U x)) =
      fourFieldUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 1) U
        ((Scheme.Modules.symmetricAlgebraGen Y F).val.app (op U) x) := by
    have h := congrArg (fun ψ => ψ.val.app (op (g ⁻¹ᵁ U)) (fourFieldUnit g F U x))
      (Stacks.Sheaves.GradedAlgebraEssentiallySmall.gen_comp_symmetricPullbackHom_app_one f
        (Scheme.Modules.symmetricAlgebraGen Y F)
        (fun V x y => eq_of_heq (Scheme.Modules.symmetricAlgebra_mul_comm Y F 1 1 V x y))
        (Scheme.Modules.symmetricAlgebraGen X M)
        (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X M))
    exact h.trans (fourFieldUnit_natural g (Scheme.Modules.symmetricAlgebraGen Y F) U x)
  have hm := c.map_mul 1 1 (op (g ⁻¹ᵁ U))
    ((Scheme.Modules.symmetricAlgebraGen X M).val.app (op (g ⁻¹ᵁ U))
      (fourFieldUnit g F U α))
    ((Scheme.Modules.symmetricAlgebraGen X M).val.app (op (g ⁻¹ᵁ U))
      (fourFieldUnit g F U β))
  rw [hg,hg] at hm
  have hu := fourFieldUnit_mul g (Scheme.Modules.symmetricAlgebra Y F) 1 1 U
    ((Scheme.Modules.symmetricAlgebraGen Y F).val.app (op U) α)
    ((Scheme.Modules.symmetricAlgebraGen Y F).val.app (op U) β)
  rw [← product_eq_mul_generators F U α β] at hu
  change (c.app 2).val.app (op (g ⁻¹ᵁ U))
    (product M (g ⁻¹ᵁ U) (fourFieldUnit g F U α) (fourFieldUnit g F U β)) = _
  rw [product_eq_mul_generators]
  exact hm.trans hu

/-- The canonical actual symmetric-square pullback comparison sends the product of the
actual pullback-unit images to the actual pullback-unit image of the original product. -/
theorem symmetricPullbackIso_product (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (α β : Γ(F,U)) :
    (symmetricPullbackIso g F 2).hom.val.app (op (g ⁻¹ᵁ U))
      (product ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U)
        (pullbackUnit g F U α) (pullbackUnit g F U β)) =
      pullbackUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β) := by
  have hi (x : Γ(F,U)) : (g.zariskiPullbackModulesIso.inv.app F).val.app (op (g ⁻¹ᵁ U))
      (pullbackUnit g F U x) = fourFieldUnit g F U x :=
    g.zariskiPullbackModulesIso_inv_app_unit F (op U) x
  have h₁raw := symmetricMap_product (g.zariskiPullbackModulesIso.inv.app F) (g ⁻¹ᵁ U)
    (pullbackUnit g F U α) (pullbackUnit g F U β)
  have h₁ := h₁raw.trans (congrArg₂
    (product (g.zariskiRingedToposModulesHom.pullbackModules.obj F) (g ⁻¹ᵁ U)) (hi α) (hi β))
  have h₂ := fourFieldSymmetricPullbackIso_product g F U α β
  have h₃ : (g.zariskiPullbackModulesIso.hom.app
      ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).val.app (op (g ⁻¹ᵁ U))
      (fourFieldUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β)) =
      pullbackUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β) := by
    have h := congrArg (fun z => (g.zariskiPullbackModulesIso.hom.app
      ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).val.app (op (g ⁻¹ᵁ U)) z)
      (g.zariskiPullbackModulesIso_inv_app_unit
        ((Scheme.Modules.symmetricAlgebra Y F).piece 2) (op U) (product F U α β))
    exact h.symm.trans (SheafOfModules.iso_inv_hom_app_apply
      (g.zariskiPullbackModulesIso.app ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).symm
      (op (g ⁻¹ᵁ U))
      (pullbackUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β)))
  change (g.zariskiPullbackModulesIso.hom.app
    ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).val.app (op (g ⁻¹ᵁ U))
      ((fourFieldSymmetricPullbackIso g F 2).hom.val.app (op (g ⁻¹ᵁ U))
        ((symmetricMap (g.zariskiPullbackModulesIso.inv.app F) 2).val.app (op (g ⁻¹ᵁ U))
          (product ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U)
            (pullbackUnit g F U α) (pullbackUnit g F U β)))) = _
  exact (congrArg (fun z => (g.zariskiPullbackModulesIso.hom.app
    ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).val.app (op (g ⁻¹ᵁ U))
      ((fourFieldSymmetricPullbackIso g F 2).hom.val.app (op (g ⁻¹ᵁ U)) z)) h₁).trans
    ((congrArg (fun z => (g.zariskiPullbackModulesIso.hom.app
      ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).val.app (op (g ⁻¹ᵁ U)) z) h₂).trans h₃)

/-- The same compatibility with the original sheafification units and products displayed
literally, with no trivialization or compatibility hypothesis. -/
theorem symmetricPullbackIso_squareUnit_product (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (α β : Γ(F,U)) :
    (symmetricPullbackIso g F 2).hom.val.app (op (g ⁻¹ᵁ U))
      (LagrangianCotangentSections.squareUnit ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U)
        (SymPow.sqMul LinearMap.id
          ((((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
            g.toLRSHom.toShHom).unit.app F).val.app (op U) α) ⊗ₜ[Γ(X,g ⁻¹ᵁ U)]
           (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
            g.toLRSHom.toShHom).unit.app F).val.app (op U) β)))) =
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        g.toLRSHom.toShHom).unit.app ((Scheme.Modules.symmetricAlgebra Y F).piece 2)).val.app
        (op U) (LagrangianCotangentSections.squareUnit F U
          (SymPow.sqMul LinearMap.id (α ⊗ₜ[Γ(Y,U)] β))) :=
  symmetricPullbackIso_product g F U α β

end M9Native.LagrangianSymmetricPullbackProduct
