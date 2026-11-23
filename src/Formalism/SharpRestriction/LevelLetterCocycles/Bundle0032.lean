module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0030
public import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0002
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerUnitAndQFactor
public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CrtFamDet
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem crt_fam {ι : Type} [DecidableEq ι] (x₀ : LetA O n) (x : ι → LetA O n) (hx₀ : x₀ ∈ W.AΔ)
    (hx : ∀ i, x i ∈ W.AΔ) (s : Finset ι) (h0 : ∀ i ∈ s, Cop W x₀ (x i))
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Cop W (x i) (x j)) :
    ∃ κ : ℕ, ∃ r₀ ∈ W.AΔ, ∃ R : ι → LetA O n, (∀ i ∈ s, R i ∈ W.AΔ) ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ = (∏ i ∈ s, x i) * r₀ + ∑ i ∈ s, x₀ * (∏ j ∈ s.erase i, x j) * R i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨κ, r₀, hr₀, R, hR, hsum⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    have hQ : Cop W (x a) (x₀ * ∏ i ∈ s, x i) :=
      cop_symm W (cop_mul W hx₀ (hx a) (h0 a (Finset.mem_insert_self a s))
        (cop_prod W s x hx (hx a) fun i hi => hp i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s) (fun h => ha (h ▸ hi))))
    obtain ⟨m, r, hr, t, ht, hm⟩ := hQ
    refine ⟨κ + m, r₀ * r, W.AΔ.mul_mem hr₀ hr,
      fun i => if i = a then Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * t else R i * r, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · simp only [hia, if_true]; exact W.AΔ.mul_mem (lA_mem W κ) ht
      · simp only [hia, if_false]
        exact W.AΔ.mul_mem (hR i ((Finset.mem_insert.1 hi).resolve_left hia)) hr
    · rw [Finset.sum_insert ha]
      dsimp only
      rw [if_pos rfl, Finset.erase_insert ha, Finset.prod_insert ha]
      have hs : ∑ i ∈ s, x₀ * (∏ j ∈ (insert a s).erase i, x j) *
          (if i = a then Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * t else R i * r) =
          (∑ i ∈ s, x₀ * (∏ j ∈ s.erase i, x j) * R i) * r * x a := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [if_neg hia, Finset.erase_insert_of_ne (Ne.symm hia),
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [hs, pow_add]
      linear_combination (r * x a) * hsum + Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * hm

variable [IsDomain O]

theorem cop_pi_ps (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) : Cop W W.π₀ (Formalism.MainNotions.ArcLiftingSetup.ps W s) := by
  obtain ⟨a, ha⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_π₀ (W := W) hR s
  have haΔ : a ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun _ => Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
    rw [← ha]; exact Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1
  have e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s
  refine ⟨1, -a, W.AΔ.neg_mem haΔ, 1, W.AΔ.one_mem, ?_⟩
  linear_combination (-1 : LetA O n) * e1 - ha

variable [NeZero n]

theorem cop_ps_ps (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s t : ℕ) (hst : s ≠ t) :
    Cop W (Formalism.MainNotions.ArcLiftingSetup.ps W s) (Formalism.MainNotions.ArcLiftingSetup.ps W t) := by
  obtain ⟨κ, a, ha, b, hb, e⟩ := Formalism.MainNotions.UnusedSlot80.KF.psCoprime_of W hR s t hst
  exact ⟨κ, a, ha, b, hb, e⟩

theorem crtLev (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (e : ℕ) (N : ℕ → ℕ) :
    ∃ κ : ℕ, ∃ u₀ ∈ W.AΔ, ∃ u : ℕ → LetA O n, (∀ s < e, u s ∈ W.AΔ) ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ = u₀ + ∑ s ∈ Finset.range e, u s ∧
      (∃ r ∈ W.AΔ, u₀ = (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * r) ∧
      ∀ s < e, ∃ r ∈ W.AΔ,
        u s = W.π₀ * (∏ t ∈ (Finset.range e).erase s, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * r := by
  have hps : ∀ t, Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1
  have hx : ∀ t, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t ∈ W.AΔ := fun t => W.AΔ.pow_mem (hps t) _
  obtain ⟨κ, r₀, hr₀, R, hRm, hsum⟩ := crt_fam W W.π₀ (fun t => Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) hR.1 hx
    (Finset.range e)
    (fun t _ => cop_symm W (cop_pow W (hps t) hR.1 (cop_symm W (cop_pi_ps W hR t)) (N t)))
    (fun i _ j _ hij => cop_pow W (hps i) (hx j)
      (cop_symm W (cop_pow W (hps j) (hps i) (cop_ps_ps W hR j i (Ne.symm hij)) (N j))) (N i))
  refine ⟨κ, _, W.AΔ.mul_mem (W.AΔ.prod_mem fun t _ => hx t) hr₀,
    fun s => W.π₀ * (∏ t ∈ (Finset.range e).erase s, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * R s,
    fun s hs => W.AΔ.mul_mem (W.AΔ.mul_mem hR.1 (W.AΔ.prod_mem fun t _ => hx t))
      (hRm s (Finset.mem_range.2 hs)), by dsimp only; exact hsum, ⟨r₀, hr₀, rfl⟩,
    fun s hs => ⟨R s, hRm s (Finset.mem_range.2 hs), rfl⟩⟩

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicFrobeniusPowerSeriesX
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem cyclotomicFrobeniusPowerSeries_X (W : LocWach PD LL O v n) : W.φ₀ X = (1 + X) ^ PD.p - 1 := by
  rw [W.φ₀_X, W.q₀_def]

theorem cyclo_comp_mul_X {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] :
    (Polynomial.cyclotomic p R).comp (Polynomial.X + 1) * Polynomial.X =
      (Polynomial.X + 1) ^ p - 1 := by
  rw [Polynomial.cyclotomic_prime]
  have hc : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i).comp (Polynomial.X + 1) =
      ∑ i ∈ Finset.range p, (Polynomial.X + 1) ^ i := by
    simp [Polynomial.comp, Polynomial.eval₂_finsetSum]
  have h := geom_sum_mul (Polynomial.X + 1 : Polynomial R) p
  rw [add_sub_cancel_right] at h
  rw [hc, h]

theorem glue2 [IsDomain O] (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have h0 := congrFun hw 0
  have hq : (baseIdOf hR).ι (baseIdOf hR).Bs.q = W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O) := by
    change (baseIdOf hR).ι (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = _
    rw [map_add (f := _), (baseIdOf hR).ι_X]
    congr 1
    exact (baseIdOf hR).ι.commutes _
  have hcyc : (W.q₀ : PowerSeries O) =
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
    have hX : (PowerSeries.X : PowerSeries O) ≠ 0 := PowerSeries.X_ne_zero
    apply mul_left_cancel₀ hX
    rw [W.q₀_def]
    have := congrArg (fun f : Polynomial O => (f : PowerSeries O)) (cyclo_comp_mul_X (R := O) PD.p)
    simp only [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_add, Polynomial.coe_one] at this
    rw [mul_comm, this, add_comm]
  have h0' : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O)) := by
    simpa [LocWach.q, Formalism.MainNotions.DeltaInvariantLattices.Eat, LocWach.π₀, Polynomial.aeval_add, Polynomial.aeval_X,
      Polynomial.aeval_C] using h0
  let w0 : (PowerSeries O)ˣ := Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w
  refine ⟨w0⁻¹, ?_⟩
  rw [hq, ← hcyc, h0']
  change _ = ((w0⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * ((w0 : PowerSeries O) * _)
  rw [← mul_assoc, Units.inv_mul, one_mul]

theorem rhoZ_exp [CharZero LL] (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π c ζ hζ
  have hE := (LevelStatements.Lv.expRescale LL E h0 h1).1
  rw [← hE, ← h2]
  rfl

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfHypotheses
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

theorem first_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hDS : DerivationPreservesQLattice W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W)
    (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W) (hFD : Sh.FilDim W)
    (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W := by
  intro d T₁ T₂ F b S η m hS
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  obtain ⟨hdom, hdvr, hfrac⟩ := hS.2.2.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9
  set a := ⌈aR PD.p (hpar n b S + η)⌉₊ with ha_def
  have hp1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hpos : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
  have haR : 0 ≤ aR PD.p (hpar n b S + η) := by
    have hlam := lam_nonneg_of_one_lt PD.p (hpar n b S + η) (by omega)
    unfold aR
    have : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
    linarith
  have hab : ∀ c, a + η < b c := by
    intro c
    have h1 := hS.2.2.2.2.2.2.2.2.1 c
    have h2 : (a : ℝ) < aR PD.p (hpar n b S + η) + 1 := Nat.ceil_lt_add_one haR
    have : (a : ℝ) + η < b c := by linarith
    exact_mod_cast this
  have hbh : ∀ c, b c ≤ hpar n b S := fun c =>
    le_trans (Finset.le_sup (f := b) (Finset.mem_univ c)) (Nat.le_add_right _ _)

  have hjw : ∀ c τ, Formalism.MainNotions.LiftingTheory.Over W τ c → JumpsInV PD T₂.ρ τ (JumpWinS d b S η c) :=
    fun c τ hτ => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  set Mb : ZMod n → ℕ := fun i => b i + S + η with hMb
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₂ Mb Mb := by
    intro i τ hτ x hx
    have h := hjw i τ hτ x hx
    unfold JumpWinS at h
    simp only [hMb, Set.mem_Icc]
    split_ifs at h <;> simp only [Set.mem_union, Set.mem_Icc] at h <;> omega
  obtain ⟨cO, hcO, hc0, hcv⟩ := step1Kill_cO W hV (hRN hA)
  set Sx : ZMod n → Finset ℤ := fun c => (step1Kill_roots W T₂ c (Mb c) (Mb c) a).filter (· ≠ 0)
    with hSx_def
  have hSx : ∀ c ∈ evens n d, ∀ x ∈ Sx c, x ≠ 0 ∧ ((1 - ((b c + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - b c) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ))) := by
    intro c hc x hx
    have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
    rw [hSx_def, Finset.mem_filter, step1Kill_roots, Finset.mem_image] at hx
    obtain ⟨⟨p, hp, rfl⟩, hx0⟩ := hx
    rw [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨hu, hj1, hj2⟩ := hp
    unfold jumpSetL at hu
    simp only [Finset.mem_filter] at hu
    obtain ⟨-, τ, hτ, hjmp⟩ := hu
    have hw := hjw c τ hτ p.1 hjmp
    simp only [JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    refine ⟨hx0, ?_⟩
    push_cast at hj1 hj2 ⊢
    omega

  have hbound : ∀ c ∈ evens n d,
      ((∑ x ∈ Sx c, padicValInt PD.p x : ℕ) : ℝ) ≤ B1 PD.p (hpar n b S) η S := by
    intro c hc
    have hv := padicValInt_sum_le PD.p (b c) S η a (hab c) (Sx c) (hSx c hc)
    have hv' : ((PD.p : ℝ) - 1) * ((∑ x ∈ Sx c, padicValInt PD.p x : ℕ) : ℝ) ≤
        2 * (a : ℝ) + 2 * η + S + ((PD.p : ℝ) - 1) * ((Nat.log PD.p (b c - a - 1) : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hv
      push_cast [Nat.cast_sub (by omega : 1 ≤ PD.p)] at this ⊢
      linarith
    have hH : (1 : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
      have h1 : 1 ≤ hpar n b S + η := by have := hab c; have := hbh c; omega
      have : (1 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hlog : (Nat.log PD.p (b c - a - 1) : ℝ) ≤ Real.logb PD.p (2 * ((hpar n b S + η : ℕ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (b c - a - 1) with hK0 | hKpos
      · rw [hK0, Nat.log_zero_right, Nat.cast_zero]
        exact Real.logb_nonneg hp1 hH
      · have hKle : ((b c - a - 1 : ℕ) : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
          have : b c - a - 1 ≤ hpar n b S + η := by have := hbh c; omega
          have : ((b c - a - 1 : ℕ) : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        calc (Nat.log PD.p (b c - a - 1) : ℝ) ≤ Real.logb PD.p ((b c - a - 1 : ℕ) : ℝ) :=
              Real.natLog_le_logb _ _
          _ ≤ _ := Real.logb_le_logb_of_le hp1 (by exact_mod_cast hKpos) hKle
    unfold B1 lam
    have hm := mul_le_mul_of_nonneg_left hlog hpos.le
    rw [show ((aN PD.p (hpar n b S + η) : ℕ) : ℝ) = (a : ℝ) from rfl, div_add' _ _ _ hpos.ne',
      le_div_iff₀ hpos]
    nlinarith
  have hB1 : 0 ≤ B1 PD.p (hpar n b S) η S := by
    unfold B1
    have := lam_nonneg_of_one_lt PD.p (hpar n b S + η) (by omega)
    have : 0 ≤ (2 * (aN PD.p (hpar n b S + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by positivity) hpos.le
    linarith
  set s₁ : ℕ := (evens n d).sup fun c => ∑ x ∈ Sx c, padicValInt PD.p x with hs₁_def
  have hs₁ : (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S := by
    have : s₁ ≤ ⌊B1 PD.p (hpar n b S) η S⌋₊ := Finset.sup_le (fun c hc => Nat.le_floor (hbound c hc))
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hB1)
  refine ⟨s₁, hs₁, ?_⟩
  intro FF _ _ _ _ g N y z μ ν hX
  haveI := hdom
  haveI := hdvr
  haveI := hfrac

  have hw : ∀ c, ∃ w : O, c ∈ evens n d →
      (C w * ∏ x ∈ Sx c, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s₁ := by
    intro c
    by_cases hc : c ∈ evens n d
    · obtain ⟨w, hw⟩ := step1Kill_norm hV W.v_l cO hcv (Sx c) (by simp [hSx_def]) s₁
        (Finset.le_sup (f := fun c => ∑ x ∈ Sx c, padicValInt PD.p x) hc)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose wc hwc using hw
  set R : ZMod n → Polynomial O := fun c => C (wc c) * ∏ x ∈ Sx c, (X - C (cO x)) with hR_def
  have hkill : ∀ c ∈ evens n d, ∀ y₀, QLattice W T₂ c a y₀ →
      Polynomial.aeval (derivationOnWachModule W T₂) (X * R c) y₀ ∈ W.N T₂ := by
    intro c _ y₀ hy
    have h := step1Kill_kill W T₂ hR hDS hD hA hT₂ Mb Mb hJ c cO hcO hc0 a hy
    have e : X * R c = C (wc c) * (X * ∏ x ∈ Sx c, (X - C (cO x))) := by
      simp only [hR_def]; ring
    rw [e, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact (W.N T₂).smul_of_tower_mem _ h

  obtain ⟨hX1, hX2⟩ := hX
  have hzΔ : ∀ f, ∀ δ ∈ W.DelF, W.γD T₂ δ (z f) = z f := by
    intro f δ hδ
    obtain ⟨x, -, hxe, -⟩ := hX1 f
    have h := delta_fixes_cocycle_second W T₂ x δ hδ
    rw [hxe] at h
    exact h
  let smE : W.EE → W.DD T₂ →ₗ[O] W.DD T₂ := fun e =>
    (LinearMap.lsmul W.EE (W.DD T₂) e).restrictScalars O
  let smA : LetA O n → W.DD T₂ →ₗ[O] W.DD T₂ := fun e =>
    (LinearMap.lsmul (LetA O n) (W.DD T₂) e).restrictScalars O
  let ms : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    Polynomial.aeval (derivationOnWachModule W T₂) (R c) ∘ₗ
        smE (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a) ∘ₗ ν c +
      Polynomial.aeval (derivationOnWachModule W T₂) (Polynomial.divX (R c)) ∘ₗ smE (uniformizerInverse W) ∘ₗ
        smA (letE c) ∘ₗ z
  have hcore := fun c (hc : c ∈ evens n d) (f : FF) =>
    lift_of_killing_polynomial W T₂ hR hDS hB hA hT₂ c a N s₁ (R c) (hwc c hc) (hkill c hc)
      ((letE c : LetA O n) • z f) (μ c f) (ν c f) (invariant_letter_idempotent_smul W T₂ (hzΔ f)) (hX2 c f).1
      (hX2 c f).2.1 (hX2 c f).2.2.1 (hX2 c f).2.2.2.2.2
  let uL : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    ((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c
  have hpass : ∀ c ∈ evens n d, (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, uL c f ∈ W.N T₂) ∧
      (m = 0 → ∀ f, uL c f ∈ W.N T₂) := by
    intro c hc
    obtain ⟨τ, hτ⟩ := exists_embedding_over_letter W hA c
    exact step1Pass_pass W T₂ hA hT₂ ζ hζ hEx hER hK hFD c τ hτ
      (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c) (uL c) a m
      (fun f => ⟨(hcore c hc f).2.2.1.1, (hcore c hc f).2.2.1.2, (hcore c hc f).2.2.2⟩)
      (sum_multV_le W hFD hS hE hC hQ c hc τ hτ a (by have := hab c; omega))
  have hout : ∀ F₁ : Submodule O FF, (∀ c ∈ evens n d, ∀ f ∈ F₁, uL c f ∈ W.N T₂) →
      Step1Out W T₂ d a N s₁ z μ F₁ ms := by
    intro F₁ hF c hc f
    exact ⟨(hcore c hc f).1, (hcore c hc f).2.1, (hcore c hc f).2.2.1.2, (hcore c hc f).2.2.2,
      fun hf => hF c hc f hf⟩
  by_cases hm0 : m = 0
  · exact ⟨⊤, ms, (PChain.refl _ _ _ ⊤).mono (Nat.zero_le _) le_rfl, fun _ => rfl,
      hout ⊤ (fun c hc f _ => (hpass c hc).2 hm0 f)⟩
  · obtain ⟨B, hBc, hBP⟩ := iter_chain (lenO := lenOl PD (O := O)) (m := m)
      (c := lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S)
      (fun c B => ∀ f ∈ B, uL c f ∈ W.N T₂) (· ∈ evens n d)
      (fun _ _ _ hBA hP f hf => hP f (hBA hf)) ⊤ 1 0 (fun c hc A _ => (hpass c hc).1 _ _ A)
      (evens n d).toList (fun c hc => Finset.mem_toList.1 hc) ⊤ le_rfl
    refine ⟨B, ms, ?_, fun h => absurd h hm0, hout B (fun c hc => hBP c (Finset.mem_toList.2 hc))⟩
    simpa [Finset.length_toList] using hBc

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GCoordProp
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def GCoordProp (W : LocWach PD LL O v n) : Prop :=
  ∀ (T : LocLat G Qp LL O) (i : ZMod n) (h c : ℕ) {r : ℕ} (e e' : Fin r → W.DD T)
    (_ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (P Z : Matrix (Fin r) (Fin r) (PowerSeries O)),
    (∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ h • W.φD T (e' k) = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P m k) • e m) →
    PowerSeries.constantCoeff W.π₀₁ = 0 →
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) →
    ∀ (k : Fin r), Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k ∈ W.N T →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k) →
      ∀ (a : Fin r → PowerSeries O),
        Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a l) • e l →
        ∀ l, (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l = (P * Z) l k

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
section
namespace Formalism.MainNotions.UnusedSlot80.CutU

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def RATCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (A : ArcP n) (a : ZMod n) (e : ℕ) (E₀ : ℕ) (E : ℕ → ℤ), E₀ ≤ 1 →
    (∀ s < e, -(A.Hs a e s : ℤ) ≤ E s ∧ E s ≤ A.Hs a e s) →
    ∀ f : W.EE, InFr W a 1 (abelian₂ W A a e) f →
      (∀ s < e, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a (ps W s ^ (E s).toNat)
          (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ A.Hs a e t) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) →
      (E₀ = 1 → ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a W.π₀ (abelian₂ W A a e) f₁ ∧ InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) →
      ∃ f₁ f₂ : W.EE, f = f₁ + f₂ ∧
        InFr W a (W.π₀ ^ E₀ * ∏ s ∈ Finset.range e, ps W s ^ (E s).toNat)
          (∏ s ∈ Finset.range e, ps W s ^ (-(E s)).toNat) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂

def InvLevCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (a : ZMod n) (s : ℕ) (T : Finset ℕ) (e : ℕ → ℕ), s ∉ T →
    ∀ f : W.EE, InFr W a 1 (∏ t ∈ T, ps W t ^ e t) f →
    (∃ κ : ℕ, InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t) (lE W κ * (W.γE W.gam f - f))) →
    ∃ (κ : ℕ) (x : O), InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE a) * algebraMap O W.EE x)

def KillWinFromCut [IsDomain O] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → Formalism.MainNotions.UnusedSlot80.KL.PsStable W → W.π₀ ∈ W.AΔ → RATCore W → InvLevCore W →
    Formalism.MainNotions.UnusedSlot80.UnivF.KillWinCore W

end Core

end Formalism.MainNotions.UnusedSlot80.CutU
end

