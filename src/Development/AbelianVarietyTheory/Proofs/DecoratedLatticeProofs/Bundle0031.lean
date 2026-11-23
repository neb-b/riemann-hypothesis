module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselStepPositionOneFinite
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PosOne.quotInt_one_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (e : GL (n' ⊕ Fin (c + 1)) k →₀ ℂ) (_ : SrcComb ψ ν P ρ' Φ e) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (z : GL (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g ∈ e.support, IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F (om μ g 1 Φ.1)) (z g)) → IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (comb e z) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν hν μ hμ μX _ μG _ ρ' hρ' Φ e he A _ _ σ hσ B hB F z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨Rr, hRr, hRrN⟩ := _root_.GlobalTheory.PosOne.RrLin.exists_linear_isQuotInt_tInt k n n' c P hP hPc ψ hψ hψ1 ν μ hμ μX μG A σ hσ B hB F ρ' hρ'
  have hone := _root_.GlobalTheory.PosOneIntegral.isQuotInt_toOne k n n' c P hP hPc ψ hψ hψ1 ν hν μ hμ μX μG A σ hσ B hB F ρ' hρ' Rr hRr Φ
  have hcomb : toOne ν ρ' P Rr Φ = comb e fun g => Rr (ρ' g Φ) := he Rr hRrN
  have heq : comb e z = comb e fun g => Rr (ρ' g Φ) := by
    unfold comb
    refine Finsupp.sum_congr fun g hg => ?_
    congr 1
    have h1 := hRr (ρ' g Φ)
    rw [hρ' g Φ] at h1
    exact ((GlobalTheory.QuotInt.quotInt_unique_exists k n c P hP hPc ν μX μG _).1 _ _ (hz g hg) h1)
  rw [heq, ← hcomb]
  exact hone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneUniformInLevel
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne.Unif

theorem comb_eq_lc {G : Type} (e : G →₀ ℂ) (F : G → ℂ) :
    comb e F = Finsupp.linearCombination ℂ F e := by
  simp [comb, Finsupp.linearCombination_apply, smul_eq_mul]

theorem comb_translate {G : Type} [Group G] (e : G →₀ ℂ) (f : G → G →₀ ℂ) (F : G → ℂ) :
    comb e (fun g => comb (f g) (fun h => F (h * g))) =
      comb (e.sum fun g a => a • (f g).mapDomain (· * g)) F := by
  conv_rhs => rw [comb_eq_lc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul, Finsupp.linearCombination_mapDomain, comb_eq_lc, smul_eq_mul]
  rfl

def conjSub {G : Type} [Group G] (U : Subgroup G) (g : G) : Subgroup G :=
  U.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSub {G : Type} [Group G] (U : Subgroup G) (g u : G) :
    u ∈ conjSub U g ↔ g⁻¹ * u * g ∈ U := by
  simp [conjSub]

theorem isOpen_conjSub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (g : G) : IsOpen (conjSub U g : Set G) := by
  have : (conjSub U g : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (U : Set G) := by
    ext x; simp [mem_conjSub]
  rw [this]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem fixed_conjSub {G A : Type} [Group G] [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ G A)
    (U : Subgroup G) (v : A) (hv : ∀ u ∈ U, σ u v = v) (g : G) :
    ∀ u ∈ conjSub U g, σ u (σ g v) = σ g v := by
  intro u hu
  rw [mem_conjSub] at hu
  have e1 : u * g = g * (g⁻¹ * u * g) := by group
  calc σ u (σ g v) = σ (u * g) v := by rw [map_mul]; rfl
    _ = σ g (σ (g⁻¹ * u * g) v) := by rw [e1, map_mul]; rfl
    _ = σ g v := by rw [hv _ hu]

end GlobalTheory.PosOne.Unif

namespace GlobalTheory.PosOne.Unif

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)

theorem toOne_comb (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k)
    (hsd : IsSelfDual ψ ν) : ∀ q : ℕ, q + 1 ≤ c → ∀ (U : Subgroup (GL (n ⊕ Fin c) k)),
    IsOpen (U : Set (GL (n ⊕ Fin c) k)) → ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ,
    ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
      (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ (q + 1) σ l → (∀ u ∈ U, σ u v = v) →
      toOne ν σ (q + 1) l v = comb e (fun g => l (σ g v)) ∧
        l v = comb e' fun g => toOne ν σ (q + 1) l (σ g v) := by
  haveI : ν.IsAddHaarMeasure := hsd.1
  intro q
  induction q with
  | zero =>
    intro _ U _
    refine ⟨Finsupp.single 1 1, Finsupp.single 1 1, ?_⟩
    intro A _ _ σ _ l v _ _
    simp [comb, toOne_one]
  | succ q ih =>
    intro hc U hU
    have hq1 : 1 ≤ q + 1 := by omega
    have hqc : q + 1 < c := by omega

    have H1 := fun g : GL (n ⊕ Fin c) k =>
      _root_.GlobalTheory.PosOne.exchange_eq_comb k n c (q + 1) hq1 hqc ψ hψc hψ1 ν (conjSub U g) (isOpen_conjSub U hU g)
    choose eg eg' heg using H1

    have H2 := fun g : GL (n ⊕ Fin c) k => ih (by omega) (conjSub U g) (isOpen_conjSub U hU g)
    choose E E' hE using H2
    obtain ⟨e₀, _e₀', he₀⟩ := ih (by omega) U hU
    obtain ⟨_e₁', e₁, he₁⟩ := _root_.GlobalTheory.PosOne.exchange_eq_comb k n c (q + 1) hq1 hqc ψ hψc hψ1 ν U hU
    refine ⟨e₀.sum fun g a => a • (eg g).mapDomain (· * g),
      e₁.sum fun g a => a • (E' g).mapDomain (· * g), ?_⟩
    intro A _ _ σ hsm l v hl hv
    obtain ⟨l', hl'eq, hl'pos⟩ :=
      (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqc ψ hψc hψ1 ν A σ hsm).2.1 l hl
    have hfun : (⇑l' : A → ℂ) = exDown ν (q + 1) σ ⇑l := funext hl'eq
    have htoOne : toOne ν σ (q + 1 + 1) ⇑l = toOne ν σ (q + 1) ⇑l' := by
      rw [hfun]; rfl
    have hmul : ∀ g h : GL (n ⊕ Fin c) k, σ h (σ g v) = σ (h * g) v := by
      intro g h; rw [map_mul]; rfl
    constructor
    · rw [htoOne, (he₀ A σ hsm l' v hl'pos hv).1]
      have : (fun g => l' (σ g v)) = fun g => comb (eg g) (fun h => l (σ (h * g) v)) := by
        funext g
        rw [hl'eq, (heg g A σ hsm l (σ g v) (fixed_conjSub σ U v hv g)).1 hl]
        simp only [hmul]
      rw [this]; exact comb_translate e₀ eg (fun g => l (σ g v))
    · have hback := ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqc ψ hψc hψ1 ν hsd A σ hsm l v).2 hl).symm
      rw [hback, ← hfun, (he₁ A σ hsm l' v hv).2 hl'pos]
      have : (fun g => l' (σ g v)) =
          fun g => comb (E' g) (fun h => toOne ν σ (q + 1 + 1) l (σ (h * g) v)) := by
        funext g
        rw [(hE g A σ hsm l' (σ g v) hl'pos (fixed_conjSub σ U v hv g)).2, htoOne]
        simp only [hmul]
      rw [this]; exact comb_translate e₁ E' (fun g => toOne ν σ (q + 1 + 1) l (σ g v))

end GlobalTheory.PosOne.Unif

open GlobalTheory.PosOne.Unif in
theorem GlobalTheory.PosOne.toOne_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ P σ l → (∀ u ∈ U, σ u v = v) → toOne ν σ P l v = comb e (fun g => l (σ g v)) ∧ l v = comb e' fun g => toOne ν σ P l (σ g v) := by
  intro k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hψ1 ν hsd U hU
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  obtain ⟨e, e', h⟩ := toOne_comb k n c ψ hψc hψ1 ν hsd q hPc U hU
  exact ⟨e, e', fun A _ _ σ hsm l v hl hv => h A σ hsm l v hl hv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearPositionMiddleVertex
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.MidVertex

theorem exists_bilPos_mid : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))) (_ : IsSrc μ₂ ρ₁), ∃ b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, BilPos ψ μ₁ ρ ρ₁ b ∧ (∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ ρ (tInt ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (b Ψ Φ₂)) ∧ ∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (toOne ν ρ₁ ρ (b Ψ) Φ₂) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hc ψ hψc hψ1 ν hsd μ₁ μ₂ hk₁ hk₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT F ρ₁ hsrc
  haveI : ν.IsAddHaarMeasure := hsd.1
  have h1 : 1 ≤ ρ := by omega
  have h2 : ρ ≤ c := by omega
  have hR := fun Ψ => _root_.GlobalTheory.PosOne.RrLin.exists_linear_isQuotInt_tInt k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc
  choose R hQ hN using hR
  have uniq : ∀ (f : GL (n₂ ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotInt ν m₂ G₂ ρ f z → IsQuotInt ν m₂ G₂ ρ f z' → z = z' :=
    fun f z z' => (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ h1 h2 ν m₂ G₂ f).1 z z'
  have lin := fun f f' a z z' => GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n₂ c ρ h1 h2 ν m₂ G₂ f f' a z z'
  have key : ∀ (a : ℂ) Ψ Ψ' Φ, R (a • Ψ + Ψ') Φ = a * R Ψ Φ + R Ψ' Φ := by
    intro a Ψ Ψ' Φ
    have h := lin _ _ a _ _ (hQ Ψ Φ) (hQ Ψ' Φ)
    have hf : (fun h => a * tInt ψ ν μ₂ ρ σ (T Ψ) F Φ.1 h + tInt ψ ν μ₂ ρ σ (T Ψ') F Φ.1 h) =
        tInt ψ ν μ₂ ρ σ (T (a • Ψ + Ψ')) F Φ.1 := by
      funext h
      simp only [tInt, app, map_add (f := _), map_smul]
      split_ifs <;> simp
    rw [hf] at h
    exact uniq _ _ _ (hQ _ Φ) h
  have hz : ∀ Φ, R 0 Φ = 0 := by
    intro Φ
    have := key 1 0 0 Φ
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  let b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := R
      map_add' := fun Ψ Ψ' => by
        ext Φ
        have := key 1 Ψ Ψ' Φ
        simpa using this
      map_smul' := fun a Ψ => by
        ext Φ
        have := key a Ψ 0 Φ
        simp only [add_zero] at this
        simp [this, hz] }
  refine ⟨b, ⟨fun Ψ => hN Ψ, ?_⟩, fun Ψ Φ₂ => hQ Ψ Φ₂, fun Ψ Φ₂ =>
    _root_.GlobalTheory.PosOneIntegral.isQuotInt_toOne k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν hsd μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc (R Ψ) (hQ Ψ) Φ₂⟩
  intro g Ψ Ψ₁ v hΨ
  show R Ψ₁ (ρ₁ (embX (c + 1) g) v) = _ * R Ψ v
  set s : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) with hs
  have hexp : ((((c + 1 : ℕ) : ℝ) + 1) / 2 - (ρ : ℝ)) = ((c : ℝ) + 2) / 2 - ρ := by push_cast; ring
  rw [hexp]
  have hfun : tInt ψ ν μ₂ ρ σ (T Ψ₁) F (ρ₁ (embX (c + 1) g) v).1 =
      fun h => (s - 1) * tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h + tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h := by
    funext h
    have hv : ((ρ₁ (embX (c + 1) g) v : SB _) : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) =
        om μ₂ (embX (c + 1) g) 1 v.1 := hsrc _ _
    have hcomm : om μ₂ 1 h (om μ₂ (embX (c + 1) g) 1 v.1) = om μ₂ (embX (c + 1) g) 1 (om μ₂ 1 h v.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    have hΦ' : om μ₂ 1 h v.1 ∈ SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := om_mem_SB μ₂ 1 h v.2
    have hX := (GlobalTheory.RootEx.opE_SB_and_linear k n₂ n₁ c ρ ψ hψc ν).1 _ hΦ'
    have hE' := (GlobalTheory.RootEx.opE_om_embX k n₂ n₁ c ρ h1 h2 ψ ν μ₂ (om μ₂ 1 h v.1)).2 g
    have hX' : om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) ∈ SB (Matrix n₂ n₁ k) := om_mem_SB μ₂ g 1 hX
    have hinv := hT.2 g Ψ Ψ₁ ⟨_, hX⟩ ⟨_, hX'⟩ hΨ rfl
    simp only [tInt]
    rw [hv, hcomm, hE']
    have e1 : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) •
        om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) = ((s • (⟨_, hX'⟩ : SB (Matrix n₂ n₁ k)) : SB _) : Matrix n₂ n₁ k → ℂ) := by
      rfl
    have e2 : app (T Ψ) (opE ψ ν ρ (om μ₂ 1 h v.1)) = T Ψ ⟨_, hX⟩ := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe _ ⟨_, hX⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e2, map_smul, hinv]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    ring
  have h := lin _ _ (s - 1) _ _ (hQ Ψ v) (hQ Ψ v)
  rw [← hfun] at h
  rw [uniq _ _ _ (hQ Ψ₁ _) h]
  ring

end GlobalTheory.PosOne.MidVertex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqAdicCompletionIntegers
section
open IsDedekindDomain NumberField IsLocalRing

namespace GlobalTheory.BinaryUnitForm

theorem exists_eq_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] (t n u : R)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : R, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  obtain ⟨r, s, hrs⟩ := GlobalTheory.UnramifiedHermitian.exists_binary_eq_of_finite
    (a := residue R t) (n := residue R n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R)).ne_zero)
    (residue R u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R (r ^ 2 + t * r * s + n * s ^ 2) = residue R u := by
    simpa only [map_add (f := _), map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + t * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu.map _).ne_zero
  obtain ⟨w, hw⟩ := hNu.exists_right_inv
  have he : u * w - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hw, map_one, sub_self]

  have hspan : Ideal.span {(2 : R), t} = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ hD
    rw [Ideal.mem_span_pair]
    exact ⟨-2 * n, t, by ring⟩
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (show (1 : R) ∈ Ideal.span {(2 : R), t} by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨T, hT⟩ := GlobalTheory.UnramifiedHermitian.exists_add_mul_sq_eq (maximalIdeal R)
    (α ^ 2 + t * α * β + n * β ^ 2) he
  refine ⟨r * (1 + T * α) - n * s * (T * β), r * (T * β) + (1 + T * α) * s + t * s * (T * β), ?_⟩
  linear_combination (r ^ 2 + t * r * s + n * s ^ 2) * T * hαβ
    + (r ^ 2 + t * r * s + n * s ^ 2) * hT + u * hw

theorem exists_eq_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by
  intro F _ _ v t n u hD hu
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  exact exists_eq_of_henselian t n u hD hu

end GlobalTheory.BinaryUnitForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeSeriesCellHasSum
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.LatticePair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsInt (A : GL (Fin n) k) : Prop := ∀ i j, A.1 i j ∈ 𝒪[k]

theorem isInt_mul {A B : GL (Fin n) k} (hA : IsInt A) (hB : IsInt B) : IsInt (A * B) := fun i j => by
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isInt_mul_KO_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (A * κ) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul hA h.1⟩
  have := isInt_mul hA h.2
  rwa [mul_inv_cancel_right] at this

theorem isInt_KO_mul_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (κ * A) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul h.1 hA⟩
  have := isInt_mul h.2 hA
  rwa [inv_mul_cancel_left] at this

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨u, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det u : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem ord_det_mul (a b : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det (a * b)) =
    ord k (Matrix.GeneralLinearGroup.det a) + ord k (Matrix.GeneralLinearGroup.det b) := by
  rw [map_mul, ord_mul]

theorem ord_det_inv (a : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det a⁻¹) =
    -ord k (Matrix.GeneralLinearGroup.det a) := by
  have := ord_det_mul a a⁻¹
  rw [mul_inv_cancel, map_one, ord_eq_zero (x := 1) (by simp)] at this
  omega

theorem valuation_det_le_one {A : GL (Fin n) k} (hA : IsInt A) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := by
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨A.1 i j, hA i j⟩
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = A.1 := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← hB, ← RingHom.map_det]
  exact B.det.2

theorem ord_nonneg_of_le_one {x : kˣ} (hx : valuation k (x : k) ≤ 1) : 0 ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  have h1 : φ (valuation k (x : k)) ≤ φ 1 := φ.strictMono.monotone hx
  rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  show 0 ≤ -WithZero.log (φ (valuation k (x : k)))
  omega

theorem ord_det_torusElt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) :
    ord k (Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e)) = ∑ i, e i := by
  have h1 : Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_torusElt, Matrix.det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have := map_zpow o ϖ (∑ i, e i)
  rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
    smul_eq_mul, mul_one, ← h1] at this
  exact this

theorem isInt_and_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (A : GL (Fin n) k)
    (e : Fin n → ℤ) : IsInt A ∧ IsInt (A * torusElt k (Fin n) ϖ e) ↔
      IsInt (A * torusElt k (Fin n) ϖ fun i => min (e i) 0) := by
  have hle : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have hpow : ∀ m : ℤ, 0 ≤ m → (ϖ : k) ^ m ∈ 𝒪[k] := fun m hm => by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact pow_mem hle m
  have hent : ∀ (f : Fin n → ℤ) i j, (A * torusElt k (Fin n) ϖ f).1 i j = A.1 i j * (ϖ : k) ^ f j :=
    fun f i j => by rw [Units.val_mul, val_torusElt, Matrix.mul_diagonal]
  have key : ∀ (x : k) (m : ℤ), (x ∈ 𝒪[k] ∧ x * (ϖ : k) ^ m ∈ 𝒪[k]) ↔ x * (ϖ : k) ^ min m 0 ∈ 𝒪[k] := by
    intro x m
    have hz : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rcases le_total m 0 with h | h
    · rw [min_eq_left h]
      refine ⟨And.right, fun h2 => ⟨?_, h2⟩⟩
      have : x = x * (ϖ : k) ^ m * (ϖ : k) ^ (-m) := by
        rw [mul_assoc, ← zpow_add₀ hz, add_neg_cancel, zpow_zero, mul_one]
      rw [this]
      exact mul_mem h2 (hpow _ (by omega))
    · rw [min_eq_right h, zpow_zero, mul_one]
      exact ⟨And.left, fun h2 => ⟨h2, mul_mem h2 (hpow _ h)⟩⟩
  simp only [IsInt, hent]
  constructor
  · rintro ⟨h1, h2⟩ i j
    exact (key _ _).1 ⟨h1 i j, h2 i j⟩
  · intro h
    exact ⟨fun i j => ((key _ _).2 (h i j)).1, fun i j => ((key _ _).2 (h i j)).2⟩

theorem out_eq_mul {r : GL (Fin n) k} {c : GL (Fin n) k ⧸ KO k (Fin n)}
    (h : (r : GL (Fin n) k ⧸ KO k (Fin n)) = c) : ∃ κ ∈ KO k (Fin n), c.out = r * κ := by
  subst h
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) r
  exact ⟨κ, κ.2, hκ⟩

theorem smul_out (u : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), (u • c).out = u * c.out * κ := by
  apply out_eq_mul
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem hasSum_pair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) (g : GL (Fin n) k)
    (hg : g ∈ cell k (Fin n) ϖ e) (X : ℂ) (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) :
    HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat +
        (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat))
      (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  obtain ⟨x, hx, y, hy, hgxy⟩ := DoubleCoset.mem_doubleCoset.1 hg
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = x * torusElt k (Fin n) ϖ fun i => min (e i) 0 := ⟨_, rfl⟩
  have hP : ∀ h : GL (Fin n) k, (IsInt h⁻¹ ∧ IsInt (h⁻¹ * g)) ↔ IsInt (h⁻¹ * u) := fun h => by
    rw [hgxy, hu, ← mul_assoc, ← mul_assoc, ← mul_assoc, isInt_mul_KO_iff hy, ← isInt_and_mul_torus_iff hϖ,
      isInt_mul_KO_iff hx]
  let E : {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]} ≃
      {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    (MulAction.toPerm u).subtypeEquiv fun c => by
      obtain ⟨κ, hκ, h⟩ := smul_out u c
      refine Iff.trans ?_ (hP (u • c).out).symm
      have : (u * c.out * κ)⁻¹ * u = κ⁻¹ * c.out⁻¹ := by group
      rw [h, this, isInt_KO_mul_iff (inv_mem hκ)]
      rfl
  have hN := (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n (fun _ => 1) (fun _ => 1) (isBorelSph_one k) (fun _ => one_ne_zero) (X ^ 2)
    fun i => by simpa only [inv_one, mul_one] using hX i).mul_left (X ^ (∑ i, |e i|).toNat)
  simp only [inv_one, mul_one] at hN
  rw [← E.hasSum_iff]
  refine (congrArg (HasSum · _) (funext fun c => ?_)).mpr hN
  obtain ⟨κ, hκ, h⟩ := smul_out u c.1
  have hE : (E c).1.out = u * c.1.out * κ := h
  have hj := ord_nonneg_of_le_one (valuation_det_le_one (A := c.1.out⁻¹) c.2)
  have habs : ∑ i, |e i| = ∑ i, e i - 2 * ∑ i, min (e i) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  have h1 : ∑ i, min (e i) 0 ≤ 0 := Finset.sum_nonpos fun i _ => min_le_right _ _
  have h2 : ∑ i, min (e i) 0 ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => min_le_left _ _
  have hou : ord k (Matrix.GeneralLinearGroup.det u) = ∑ i, min (e i) 0 := by
    rw [hu, ord_det_mul, ord_det_of_mem_KO hx, ord_det_torusElt hϖ, zero_add]
  have hog : ord k (Matrix.GeneralLinearGroup.det g) = ∑ i, e i := by
    rw [hgxy, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hx, ord_det_of_mem_KO hy, ord_det_torusElt hϖ,
      zero_add, add_zero]
  rw [ord_det_inv] at hj
  simp only [Function.comp_apply]
  rw [ord_det_mul, ord_det_inv, hE, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hκ, hou, hog,
    ← pow_mul, ← pow_add, habs]
  congr 1
  omega

end GlobalTheory.LatticePair
end
end

