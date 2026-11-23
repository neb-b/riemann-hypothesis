module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsPhi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DIsoDR0
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

def GlueL : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (Amp : ∀ M : Model l K, E.LineData M.X → Prop), B.CompatH l → E.RIn l → E.FirstChernUniqueEtale → (∀ M D, Amp M D → Etale D.f) →
    (∀ M : Model l K, M.Sm → ∃ D, Amp M D) → (dat Amp).Laws Model.Sm

def GlueE : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (Amp : ∀ M : Model l K, E.LineData M.X → Prop), E.EtMap l K → Nonempty (EMap Model.Sm (dat Amp))

def GlueB : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  (Amp : ∀ M : Model l K, E.LineData M.X → Prop), B.Main l → B.Compat l → B.FirstChernCompatible l →
    ∃ (β : BMap Model.Sm (dat Amp)) (β₁ : BPhi β), @β₁.pull = @datPull l _ K Amp

def BocksteinBaseChangeP : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ Amp : ∀ M : Model l K, E.LineData M.X → Prop, (∀ M D, Amp M D → Etale D.f) ∧ (∀ M : Model l K, M.Sm → ∃ D, Amp M D) ∧
    Nonempty (PMap Model.Sm (dat Amp)) ∧ ∀ r : Res l K, Nonempty (FMap Model.Sm r.perC r.iso (dat Amp) (datPull Amp))

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsCrystallineChernClassLimit
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Res.Cup (r : Res l K) : Type 1 :=
  ∀ (M : Model l K) (i j : ℕ), r.iso.D M i →ₗ[Wc.K₀ l r.k] r.iso.D M j →ₗ[Wc.K₀ l r.k] r.iso.D M (i + j)

def Res.IsCup (r : Res l K) (μ : r.Cup) : Prop := ∀ (M : Model l K) (i j : ℕ) (x : Pb.Lim r M i) (y : Pb.Lim r M j),
  ∃ z, Pb.LimCup r M rfl x y z ∧ μ M i j (Pb.toD r M i x) (Pb.toD r M j y) = Pb.toD r M (i + j) z

def CupEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K), ∃ μ, r.IsCup μ

end CrystallineSemistableComparison
end
end

