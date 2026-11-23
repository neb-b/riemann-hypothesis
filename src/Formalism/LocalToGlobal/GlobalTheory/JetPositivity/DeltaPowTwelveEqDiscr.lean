module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

section Pieces

variable {R : Ranks} (host : Host R) {LL : Type} [Field LL] [NumberField LL] (embLL : LL →+* ℂ)
  {Tau : Type} [Fintype Tau] (eTau : Tau ≃ R.Psi)

def lamOfH (cc : Ideal (𝓞 host.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * host.φ₀ (((c : host.K) : host.E))}

def embTH (τ : Tau) : host.E →+* ℂ := host.emb (eTau τ : R.GG)

def mmMH (M : IntermediateField ℚ ℂ) [NumberField M] : Submodule (𝓞 M) (Tau → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (host.AA0 : Submodule (𝓞 host.E) host.E),
    v = fun τ => TaylorLogMetric.liftM M (embTH host eTau τ a)}

def ellTH (M : IntermediateField ℚ ℂ) [NumberField M] (τ : Tau) : Submodule (𝓞 M) M :=
  (mmMH host eTau M).comap (LinearMap.single (𝓞 M) (fun _ : Tau => (M : Type)) τ)

structure CurveDat where
  δ : ℂ
  delta_pow_twelve_eq_discr : δ ^ 12 = TaylorLogMetric.discr (lamOfH host host.ccK 1)
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  eL : LL ≃+* M
  emb : ∀ y, ((eL y : M) : ℂ) = embLL y
  fr : Tau → M
  fr_ne : ∀ τ, fr τ ≠ 0
  gen : ∀ τ, ellTH host eTau M τ = Submodule.span (𝓞 M) {fr τ}

attribute [instance] CurveDat.nf

variable {host embLL eTau}

end Pieces

end Formalism.L2.GlobalTheoryTheory.Jets
