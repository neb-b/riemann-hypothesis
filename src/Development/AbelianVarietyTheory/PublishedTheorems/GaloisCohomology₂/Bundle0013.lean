module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelLocalSC
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ArthurClozelLocalSC : Prop := LocalBC lbc

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelStrongSupp
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ArthurClozelStrongSupp : Prop := StrongBC lbc

end GlobalTheory.Published

end
end

