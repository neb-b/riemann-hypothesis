module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
section
noncomputable section

namespace GlobalTheory.ConvSer

open MvPowerSeries Finsupp

open MvPowerSeries Finsupp in
theorem _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (![f, g] : Fin 2 → MvPowerSeries Unit R) := by
  refine hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · exact hf
  · exact hg

open MvPowerSeries Finsupp in
theorem _root_.GlobalTheory.ConvSer.nMul_constantCoeff {R : Type*} [CommRing R] (F : FormalGroup R)
    (n : ℕ) : PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 := by
  induction n with
  | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
  | succ n ih =>
    rw [_root_.GlobalTheory.ConvSer.nMul_succ]
    refine constantCoeff_subst_eq_zero
      (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair ih PowerSeries.constantCoeff_X) (fun s => ?_) F.2
    fin_cases s
    · exact ih
    · exact PowerSeries.constantCoeff_X

theorem nMul_hasSubst {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.HasSubst (nMul F n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (nMul_constantCoeff F n)

theorem coeff_one_formalGroup_subst {R : Type*} [CommRing R] (F : FormalGroup R)
    {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) = PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  have key : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![f, g] : Fin 2 → MvPowerSeries Unit R) s ^ e)
      = (f ^ d 0 * g ^ d 1 : PowerSeries R) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    rfl
  have hc : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  rw [← hc, coeff_subst (nMul_hasSubst_pair hf hg),
    finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1})]
  · rw [Finset.sum_pair hne, key, key, hc, hc, F.lin_coeff_X, F.lin_coeff_Y]
    simp
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hn
    have h2 : d 0 + d 1 = 0 ∨ 2 ≤ d 0 + d 1 := by
      by_contra hh
      have : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
      rcases this with h | h
      · apply hn.1
        ext s
        fin_cases s <;> simp [h]
      · apply hn.2
        ext s
        fin_cases s <;> simp [h]
    have h0 : PowerSeries.coeff 1 (f ^ d 0 * g ^ d 1) = 0 := by
      rcases h2 with h | h
      · have h0 : d 0 = 0 := by omega
        have h1 : d 1 = 0 := by omega
        simp [h0, h1, PowerSeries.coeff_one]
      · have hd : (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) ∣ f ^ d 0 * g ^ d 1 := by
          rw [pow_add]
          exact mul_dvd_mul (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hf) _)
            (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hg) _)
        exact PowerSeries.X_pow_dvd_iff.1 hd 1 (by omega)
    show _ • _ = _
    rw [key, hc, h0, smul_zero]

theorem nMul_coeff_one {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (nMul F n) = (n : R) := by
  induction n with
  | zero => simp [nMul_zero]
  | succ n ih =>
    rw [nMul_succ, coeff_one_formalGroup_subst F (nMul_constantCoeff F n)
      PowerSeries.constantCoeff_X, ih]
    simp

theorem nMul_one {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 1 = PowerSeries.X := by
  rw [nMul_succ, nMul_zero]
  exact F.zeroX_eq_X

theorem nMul_add {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries
      = nMul F (i + j) := by
  induction j with
  | zero => exact F.add_zero (nMul_hasSubst F i)
  | succ j ih =>
    rw [← add_assoc, nMul_succ, nMul_succ, ← ih]
    exact (F.assoc' (nMul_hasSubst F i) (nMul_hasSubst F j) PowerSeries.HasSubst.X').symm

theorem nMul_subst_nMul {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    (nMul F i).subst (nMul F j) = nMul F (i * j) := by
  induction i with
  | zero =>
    rw [zero_mul, nMul_zero, ← PowerSeries.coe_substAlgHom (nMul_hasSubst F j), map_zero]
  | succ i ih =>
    rw [add_mul, one_mul, ← nMul_add F (i * j) j, nMul_succ F i, PowerSeries.subst,
      subst_comp_subst_apply
        (nMul_hasSubst_pair (nMul_constantCoeff F i) PowerSeries.constantCoeff_X)
        (nMul_hasSubst F j).const]
    congr! 2 with s
    fin_cases s
    · exact ih
    · exact PowerSeries.subst_X (nMul_hasSubst F j)

open MvPowerSeries Finsupp in
private theorem coeff_one_subst_pair_X {R : Type*} [CommRing R] (F : FormalGroup R)
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries : PowerSeries R) = PowerSeries.coeff 1 f + 1 := by
  have ha := _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair hf PowerSeries.constantCoeff_X
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![PowerSeries.X * g, PowerSeries.X] :
      Fin 2 → MvPowerSeries Unit R) s ^ e) = PowerSeries.X ^ (d 0 + d 1) * g ^ d 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    show (PowerSeries.X * g) ^ d 0 * PowerSeries.X ^ d 1 = _
    ring
  have hcoeff : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  show MvPowerSeries.coeff (single () 1) _ = _
  rw [coeff_subst ha, finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1}),
    Finset.sum_pair hne]
  · simp only [hprod, hcoeff, F.3, F.4]
    simp
  · intro d hd
    simp only [Function.mem_support, hprod, hcoeff, PowerSeries.coeff_X_pow_mul'] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h2 : d 0 + d 1 ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h | h
      · exfalso
        apply hd
        have hd0 : d = 0 := Finsupp.ext fun i => by fin_cases i <;> simp <;> omega
        simp [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.2]
      · have h0 : d 0 ≤ 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h0 | h0
        · right
          ext i
          fin_cases i <;> simp <;> omega
        · left
          ext i
          fin_cases i <;> simp <;> omega
    · exact absurd (by simp [h2]) hd


open MvPowerSeries Finsupp in
theorem _root_.GlobalTheory.ConvSer.nMul_props : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 ∧ PowerSeries.coeff 1 (_root_.GlobalTheory.ConvSer.nMul F n) = (n : R)) ∧ _root_.GlobalTheory.ConvSer.nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i, _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = _root_.GlobalTheory.ConvSer.nMul F (i + j)) ∧ (∀ i j, (_root_.GlobalTheory.ConvSer.nMul F i).subst (_root_.GlobalTheory.ConvSer.nMul F j) = _root_.GlobalTheory.ConvSer.nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (_root_.GlobalTheory.ConvSer.nMul F n) = _root_.GlobalTheory.ConvSer.nMul (F.map φ) n) := by
  intro R _ F
  have hc := _root_.GlobalTheory.ConvSer.nMul_constantCoeff F
  have hs : ∀ n, PowerSeries.HasSubst (_root_.GlobalTheory.ConvSer.nMul F n) :=
    fun n => PowerSeries.HasSubst.of_constantCoeff_zero' (hc n)
  have hX : PowerSeries.HasSubst (PowerSeries.X : PowerSeries R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
  have hadd : ∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i,
      _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries =
      _root_.GlobalTheory.ConvSer.nMul F (i + j) := by
    intro i j
    induction j with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.add_zero]
      exact F.add_zero (hs i)
    | succ j ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F j, show i + (j + 1) = (i + j) + 1 by omega,
        _root_.GlobalTheory.ConvSer.nMul_succ F (i + j), ← ih]
      exact (F.assoc' (hs i) (hs j) hX).symm
  refine ⟨fun n => ⟨hc n, ?_⟩, ?_, hadd, ?_, ?_⟩
  · induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, coeff_one_subst_pair_X F (hc n), ih]
      push_cast
      rfl
  · rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_zero]
    exact F.zero_add hX
  · intro i j
    induction i with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.zero_mul, _root_.GlobalTheory.ConvSer.nMul_zero,
        ← PowerSeries.coe_substAlgHom (hs j), map_zero]
    | succ i ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F i, Nat.succ_mul, ← hadd (i * j) j, ← ih]
      show MvPowerSeries.subst (fun _ => _root_.GlobalTheory.ConvSer.nMul F j) _ = _
      rw [MvPowerSeries.subst_comp_subst_apply
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc i) PowerSeries.constantCoeff_X)
        (hasSubst_of_constantCoeff_zero fun _ => hc j)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.subst_X (hs j)
  · intro S _ φ n
    induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_succ, FormalGroup.map_toPowerSeries,
        ← ih]
      show MvPowerSeries.map φ _ = _
      rw [MvPowerSeries.map_subst
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc n) PowerSeries.constantCoeff_X)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.map_X φ

end GlobalTheory.ConvSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivCombMem
section
open scoped BigOperators

namespace GlobalTheory.AlgJetComb

theorem pow_mem (δ : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : ∀ n, δ ^ n * iteratedDeriv n f 0 ∈ algebraicClosure ℚ ℂ) (a : ℕ) :
    ∀ n, δ ^ n * iteratedDeriv n (fun x => f x ^ a) 0 ∈ algebraicClosure ℚ ℂ := by
  induction a with
  | zero =>
    intro n
    simp only [pow_zero, iteratedDeriv_const]
    split_ifs with hn
    · subst hn; simpa using one_mem _
    · simpa using zero_mem _
  | succ a ih =>
    intro n
    have e : (fun x => f x ^ (a + 1)) = (fun x => f x ^ a) * f := by
      funext x; simp [pow_succ]
    have h1 : ContDiffAt ℂ n (fun x => f x ^ a) 0 := (hf.pow a).contDiff.contDiffAt
    have h2 : ContDiffAt ℂ n f 0 := hf.contDiff.contDiffAt
    rw [e, iteratedDeriv_mul h1 h2, Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e2 : δ ^ n * ((n.choose i : ℂ) * iteratedDeriv i (fun x => f x ^ a) 0
        * iteratedDeriv (n - i) f 0) = (n.choose i : ℂ) *
        ((δ ^ i * iteratedDeriv i (fun x => f x ^ a) 0)
          * (δ ^ (n - i) * iteratedDeriv (n - i) f 0)) := by
      have : δ ^ n = δ ^ i * δ ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [this]; ring
    rw [e2]
    exact mul_mem (natCast_mem _ _) (mul_mem (ih i) (h _))

theorem iteratedFDeriv_comb_mem :
    ∀ (g m k : ℕ) (δ : ℂ) (a : Fin g → ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ)
      (ys : Fin k → Fin g → ℂ), (∀ j i, Differentiable ℂ (f j i)) →
      (∀ j i n, δ⁻¹ ^ n * iteratedDeriv n (f j i) 0 ∈ algebraicClosure ℚ ℂ) →
      (∀ j, c j ∈ algebraicClosure ℚ ℂ) → (∀ l i, ys l i ∈ algebraicClosure ℚ ℂ) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, f j i (z i) ^ a i) 0
        (fun l => δ⁻¹ • ys l) ∈ algebraicClosure ℚ ℂ := by
  intro g m k δ a c f ys hf hj hc hy
  have hF : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, f j i (z i) ^ a i) := fun j =>
    contDiff_prod fun i _ => (((hf j i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)).pow _
  rw [iteratedFDeriv_fun_sum_apply (f := fun j (z : Fin g → ℂ) => c j * ∏ i, f j i (z i) ^ a i)
    (fun j _ => (contDiff_const.mul (hF j)).contDiffAt), ContinuousMultilinearMap.sum_apply]
  refine sum_mem fun j _ => ?_
  have e := iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hF j).contDiffAt
  simp only [smul_eq_mul] at e
  rw [e, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine mul_mem (hc j) ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k (fun i x => f j i x ^ a i) _
    (fun i => (hf j i).pow _)]
  refine sum_mem fun σ _ => ?_
  have hk : ∑ i, (Finset.univ.filter (fun l => σ l = i)).card = k := by
    rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := σ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp
  have e2 : (∏ l, (δ⁻¹ • ys l) (σ l)) *
      ∏ i, iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0
      = (∏ l, ys l (σ l)) * ∏ i, (δ⁻¹ ^ (Finset.univ.filter (fun l => σ l = i)).card *
        iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [e2]
  exact mul_mem (prod_mem fun l _ => hy _ _)
    (prod_mem fun i _ => pow_mem δ⁻¹ (f j i) (hf j i) (hj j i) _ _)

end GlobalTheory.AlgJetComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBounds
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.SubstSum

variable {K : Type} [NormedField K] [IsUltrametricDist K] {τ : Type}

def Decay (θ : ℝ) (m : ℕ) (S : MvPowerSeries τ K) : Prop :=
  ∀ μ : τ →₀ ℕ, ‖MvPowerSeries.coeff μ S‖ ≤ θ ^ (m - μ.degree)

omit [IsUltrametricDist K] in
theorem decay_one (θ : ℝ) : Decay θ 0 (1 : MvPowerSeries τ K) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem Decay.mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {m n : ℕ} {S T : MvPowerSeries τ K}
    (hS : Decay θ m S) (hT : Decay θ n T) : Decay θ (m + n) (S * T) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 _) fun p hp => ?_
  have hp' : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 S‖ * ‖MvPowerSeries.coeff p.2 T‖
      ≤ θ ^ (m - p.1.degree) * θ ^ (n - p.2.degree) :=
        mul_le_mul (hS _) (hT _) (norm_nonneg _) (pow_nonneg h0 _)
    _ = θ ^ ((m - p.1.degree) + (n - p.2.degree)) := (pow_add _ _ _).symm
    _ ≤ θ ^ (m + n - μ.degree) := by
        apply pow_le_pow_of_le_one h0 h1
        rw [← hp', map_add (f := _)]
        omega

theorem Decay.pow {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {S : MvPowerSeries τ K}
    (hS : Decay θ 1 S) (n : ℕ) : Decay θ n (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact decay_one θ
  | succ n ih => rw [pow_succ]; exact ih.mul h0 h1 hS

theorem decay_prod {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {σ : Type} (t : Finset σ)
    (s : σ → MvPowerSeries τ K) (hs : ∀ i, Decay θ 1 (s i)) (ν : σ → ℕ) :
    Decay θ (∑ i ∈ t, ν i) (∏ i ∈ t, s i ^ ν i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    exact decay_one θ
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Decay.pow h0 h1 (hs a) (ν a)).mul h0 h1 ih

omit [IsUltrametricDist K] in
theorem decay_of_small {θ : ℝ} {S : MvPowerSeries τ K} (hS : Intg S)
    (hθ : ‖MvPowerSeries.constantCoeff S‖ ≤ θ) : Decay θ 1 S := by
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hθ
  · have hd : μ.degree ≠ 0 := (Finsupp.degree_eq_zero_iff μ).not.2 hμ
    have : 1 - μ.degree = 0 := by omega
    rw [this, pow_zero]
    exact hS μ

theorem exists_decay {σ : Type} [Fintype σ] (s : σ → MvPowerSeries τ K) (hs : ∀ i, Small (s i)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ (ν : σ →₀ ℕ) (μ : τ →₀ ℕ),
      ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ θ ^ (ν.degree - μ.degree) := by
  classical
  set θ : ℝ := ((Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊ : NNReal) : ℝ)
    with hθdef
  have hsi : ∀ i, Intg (s i) ∧ ‖MvPowerSeries.constantCoeff (s i)‖ < 1 := hs
  have h0 : 0 ≤ θ := NNReal.coe_nonneg _
  have hlt : θ < 1 := by
    have : (Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊) < 1 :=
      (Finset.sup_lt_iff (by simp)).2 fun i _ => by
        have h := (hsi i).2
        rw [← coe_nnnorm] at h
        exact_mod_cast h
    exact_mod_cast this
  have hle : ∀ i, ‖MvPowerSeries.constantCoeff (s i)‖ ≤ θ := fun i => by
    rw [hθdef, ← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊)
      (Finset.mem_univ i)
  refine ⟨θ, h0, hlt, fun ν μ => ?_⟩
  have h := decay_prod h0 hlt.le Finset.univ s (fun i => decay_of_small (hsi i).1 (hle i)) ν μ
  rwa [← Finsupp.degree_eq_sum] at h

theorem tendsto_degree {σ : Type} [Fintype σ] :
    Filter.Tendsto (fun ν : σ →₀ ℕ => ν.degree) Filter.cofinite Filter.atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (0 : σ →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun _ => b)).subset
    fun ν hν => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hν
  refine Set.mem_Icc.2 ⟨zero_le, Finsupp.le_def.2 fun i => ?_⟩
  simpa using (Finsupp.le_degree i ν).trans hν.le

end GlobalTheory.ConvSer.SubstSum


open GlobalTheory.ConvSer.SubstSum in
theorem GlobalTheory.ConvSer.csub_hasSum_and_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  intro K _ _ _ σ τ _ s S hs hS
  obtain ⟨θ, h0, h1, hθ⟩ := exists_decay s hs
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C := hS
  set t : (τ →₀ ℕ) → (σ →₀ ℕ) → K := fun μ ν =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i) with ht
  have hprod1 : ∀ (ν : σ →₀ ℕ) μ, ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ 1 := fun ν μ =>
    (hθ ν μ).trans (pow_le_one₀ h0 h1.le)
  have hsum : ∀ μ, HasSum (t μ) (MvPowerSeries.coeff μ (csub s S)) := by
    intro μ
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have htend : Filter.Tendsto (t μ) Filter.cofinite (nhds 0) := by
      refine squeeze_zero_norm (a := fun ν => max C 0 * θ ^ (ν.degree - μ.degree))
        (fun ν => ?_) ?_
      · rw [ht, norm_mul]
        exact mul_le_mul ((hC ν).trans (le_max_left _ _)) (hθ ν μ) (norm_nonneg _) hC0
      · have h : Filter.Tendsto (fun ν : σ →₀ ℕ => θ ^ (ν.degree - μ.degree))
            Filter.cofinite (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
            ((Filter.tendsto_sub_atTop_nat μ.degree).comp tendsto_degree)
        simpa using h.const_mul (max C 0)
    have heq : MvPowerSeries.coeff μ (csub s S) = ∑' ν, t μ ν := rfl
    rw [heq]
    exact (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero htend).hasSum
  have hbound : ∀ B : ℝ, 0 ≤ B → (∀ μ ν, ‖t μ ν‖ ≤ B) →
      ∀ μ, ‖MvPowerSeries.coeff μ (csub s S)‖ ≤ B := fun B hB h μ => by
    rw [← (hsum μ).tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB (h μ)
  have hterm : ∀ μ ν, ‖t μ ν‖ ≤ ‖MvPowerSeries.coeff ν S‖ := fun μ ν => by
    rw [ht, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hprod1 ν μ)
  have hintg : Intg S → Intg (csub s S) := fun hI =>
    hbound 1 zero_le_one fun μ ν => (hterm μ ν).trans (hI ν)
  refine ⟨hsum, ?_, hintg, fun hI h00 => ?_⟩
  · exact Exists.intro (max C 0) (hbound _ (le_max_right _ _) fun μ ν =>
      (hterm μ ν).trans ((hC ν).trans (le_max_left _ _)))
  · have hc : ‖MvPowerSeries.coeff 0 (csub s S)‖ ≤ θ := by
      rw [← (hsum 0).tsum_eq]
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg h0 fun ν => ?_
      by_cases hν : ν = 0
      · subst hν
        simp [ht, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h00, h0]
      · rw [ht, norm_mul]
        have hd : 1 ≤ ν.degree - (0 : τ →₀ ℕ).degree := by
          have a := (Finsupp.degree_eq_zero_iff ν).not.2 hν
          rw [map_zero]
          omega
        calc ‖MvPowerSeries.coeff ν S‖ * ‖MvPowerSeries.coeff 0 (∏ i, s i ^ ν i)‖
            ≤ 1 * θ := mul_le_mul (hI ν)
              ((hθ ν 0).trans ((pow_le_pow_of_le_one h0 h1.le hd).trans_eq (pow_one θ)))
              (norm_nonneg _) zero_le_one
          _ = θ := one_mul θ
    exact And.intro (hintg hI)
      (by rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc.trans_lt h1)
end

