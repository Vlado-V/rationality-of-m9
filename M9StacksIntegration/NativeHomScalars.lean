module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear

/-!
# The exact original native Hom scalar structures over a field

The pinned native `modulesLinearOverField` is the exposed abbreviation
for `modulesLinear k (Over.mk f)`. Thus the original Linear structures,
original scalar actions on every Hom, and original scalar identities
agree by kernel-checked definitional equality. No replacement action or
module-equality hypothesis is introduced. These literal letI formulas
are intended for the native deformation/Ext/cohomology comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped ModuleCat.Algebra

universe u

namespace M9Native.NativeHomScalars

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The two original native category-linear structures are definitionally identical. -/
theorem linear_structures_eq :
    modulesLinear k (Over.mk f) = modulesLinearOverField k f := rfl

/-- Original scalar multiplication on every Hom agrees in the two exact letI contexts. -/
theorem hom_smul_eq (c : k) {M N : X.Modules} (φ : M ⟶ N) :
    (letI : Linear k X.Modules := modulesLinear k (Over.mk f); (c • φ : M ⟶ N)) =
      (letI : Linear k X.Modules := modulesLinearOverField k f; (c • φ : M ⟶ N)) := rfl

/-- In particular the original scalar identities, used to define Ext scalars, agree. -/
theorem id_smul_eq (c : k) (M : X.Modules) :
    (letI : Linear k X.Modules := modulesLinear k (Over.mk f); (c • (𝟙 M) : M ⟶ M)) =
      (letI : Linear k X.Modules := modulesLinearOverField k f; (c • (𝟙 M) : M ⟶ M)) := rfl

end M9Native.NativeHomScalars
