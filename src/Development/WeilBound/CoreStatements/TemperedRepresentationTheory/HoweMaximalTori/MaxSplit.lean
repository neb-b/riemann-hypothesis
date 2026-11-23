module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

noncomputable section

namespace PositivityTheory.HoweDualityUnitaryAlt

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def MaxAt {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F) : Prop :=
  ∀ N N', Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N' →
    N = N'

def MaxOn (Q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Chars F E → Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, Q F E X v →
      MaxAt om v ∧ MaxAt om' v

def MaxFinT : Prop := MaxOn fun _ _ _ _ _ _ _ _ _ => True

end PositivityTheory.HoweDualityUnitaryAlt

end
