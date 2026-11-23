module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0006

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    {I : LocId L p nV W Qq} {N : ℕ}

abbrev StepG.comp (S : StepG I N) : Type := compG sp.cm.sig S.J S.Uloc p

abbrev StepG.rep (S : StepG I N) (i : S.comp) : GAS S := repG sp.cm.sig S.J S.Uloc p i

end Formalism.L2.G
