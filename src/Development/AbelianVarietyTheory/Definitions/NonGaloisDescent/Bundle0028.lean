module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DivisibleGroupTowerCompatibility
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DefiniteBC

attribute [local instance] host_isCMField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
variable {A : NAut N}

def CuspReadG (rc : RecMap A) : Prop :=
  ∀ (a : ℕ) (P : CuspSub H.E a), 1 ≤ a → P.IsCsd →
    (∀ w (σ : LocIrr w a), P.IsLocComp w σ → UpperTheory.Zero.LLC.Good (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)) →
    ∃ π : A.CG a, A.csd π ∧ (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w a σ) ∧ ∀ τ m, P.HasInfChar τ m → A.infG π τ = m

end GlobalTheory.DefiniteBC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsPresOfRealD
section
noncomputable section
namespace GlobalTheory.Present
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

theorem φ_mem (T : LocLat G Qp LL O) (x : ↥(DΔ W T)) : W.φD T x ∈ DΔ W T :=
  fun δ hδ => by rw [← W.φγ_comm, x.2 δ hδ]

theorem γ_mem (T : LocLat G Qp LL O) (g : W.Gam) (x : ↥(DΔ W T)) : W.γD T g x ∈ DΔ W T :=
  fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, x.2 δ hδ]

variable {W} {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam}

theorem Pres.j_φ' (p : Pres W F ι τ γ) {T A q} (h : Onto T A q) (i : ZMod n) (x : ↥(DΔ W T)) :
    p.j T A q i ⟨W.φD T x, φ_mem W T x⟩ = (F.D A).φ i (p.j T A q (i - 1) x) :=
  p.j_φ T A q h i x _ rfl

end GlobalTheory.Present

namespace GlobalTheory.TopSteps.TopSit
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.Present
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

end GlobalTheory.TopSteps.TopSit
end
end

