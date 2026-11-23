module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageGenerationStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageStepIndependent
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BasisLift

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]

theorem comb_add (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b + c) e = comb b e + comb c e := by
  simp [comb, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem comb_sub (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b - c) e = comb b e - comb c e := by
  simp [comb, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem comb_zero (e : ι → MvPowerSeries σ Q) : comb (0 : ι → B) e = 0 := by
  simp [comb]

theorem comb_mul (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => r * b i) e = algebraMap B Q r • comb b e := by
  simp [comb, map_mul, mul_smul, Finset.smul_sum]

theorem comb_mul_right (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => b i * r) e = algebraMap B Q r • comb b e := by
  simp only [mul_comm _ r]; exact comb_mul r b e

theorem coeff_comb (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ i, algebraMap B Q (b i) * coeff α (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, coeff_smul]

end GlobalTheory.BasisLift


open GlobalTheory.BasisLift in
theorem GlobalTheory.basis_lift : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ (Ideal.span {(p : B)}) → IsBasis μ e := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL C _ _ hC Θ hΘ ι _ e he hB hch
  obtain ⟨u, hu⟩ := hF.unit_p
  have hmapP : algebraMap B Q (p : B) = (p : Q) := map_natCast _ _
  have hconst : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hL.const i]
  have ql0 : ∀ N : Ideal B, QL μ N (0 : MvPowerSeries (Fin d) Q) := by
    intro N
    refine ⟨by simp, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
    have h0 := formalCoboundary_smul hconst (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    simp only [zero_smul] at h0
    simp [h0]
  have hsm : ∀ n : ℕ, (Ideal.span {(p : B)} ^ n • ⊤ : Submodule B B) = Ideal.span {(p : B) ^ n} := by
    intro n; rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have key : ∀ t ∈ Ideal.span {(p : B)}, ∃ t' : B, (↑u⁻¹ : Q) * algebraMap B Q t = algebraMap B Q t' := by
    intro t ht
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    refine ⟨a, ?_⟩
    rw [map_mul, hmapP, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]

  have chainE : ∀ N, Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N →
      ∀ f, QL μ ⊤ f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q),
        In (⊤ : Ideal B) s ∧ QL μ N (f - comb b e - s) := by
    intro N hN
    induction hN with
    | refl => intro f hf; exact ⟨0, 0, fun α => ⟨0, trivial, by simp⟩, by simpa [comb_zero] using hf⟩
    | tail _ hst ih =>
      intro f hf
      obtain ⟨b, s, hs, hq⟩ := ih f hf
      obtain ⟨b', s', -, hs', hq'⟩ := _root_.GlobalTheory.QLog.StepGen.step_generation p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst _ hq
      refine ⟨b + b', s + s', ?_, ?_⟩
      · intro α
        obtain ⟨x, -, hx⟩ := hs α
        obtain ⟨y, -, hy⟩ := hs' α
        exact ⟨x + y, trivial, by rw [map_add (f := _), hx, hy, map_add (f := _)]⟩
      · rw [comb_add]; convert hq' using 1; abel

  have divP : ∀ h : MvPowerSeries (Fin d) Q, QL μ (Ideal.span {(p : B)}) h →
      QL μ ⊤ ((↑u⁻¹ : Q) • h) ∧ h = (p : Q) • ((↑u⁻¹ : Q) • h) := by
    intro h ⟨h0, hl, hc⟩
    refine ⟨⟨?_, fun i => ?_, fun α => ?_⟩, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]
    · obtain ⟨t, ht, he'⟩ := hl i
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      simp only [lin, coeff_smul] at he' ⊢
      rw [he', ht']
    · obtain ⟨t, ht, he'⟩ := hc α
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      rw [formalCoboundary_smul hconst, coeff_smul, he', ht']
    · rw [smul_smul, ← hu, Units.mul_inv, one_smul]
  have E1 : ∀ f : {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f}, ∃ (b : ι → B) (s g : MvPowerSeries (Fin d) Q),
      In (⊤ : Ideal B) s ∧ QL μ ⊤ g ∧ f.1 = comb b e + s + (p : Q) • g := by
    intro ⟨f, hf⟩
    obtain ⟨b, s, hs, hq⟩ := chainE _ hch f hf
    obtain ⟨hg, hgq⟩ := divP _ hq
    exact ⟨b, s, _, hs, hg, by rw [← hgq]; abel⟩
  choose bF sF gF hsF hgF heqF using E1

  have V : ∀ α : Fin d →₀ ℕ, ∃ v : ℕ, ∀ g, QL μ ⊤ g → (p : Q) ^ v * coeff α g ∈ (algebraMap B Q).range := by
    intro α
    by_cases hα : α = 0
    · refine ⟨0, fun g hg => ⟨0, ?_⟩⟩
      rw [hα, coeff_zero_eq_constantCoeff_apply, hg.1]; simp
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h; push_neg at h; exact hα (Finsupp.ext fun i => by simp [h i])
      obtain ⟨v, n, hn, hαi⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Fact.out : p.Prime).one_lt.ne'
      have hcop : Nat.Coprime n p := Nat.Coprime.symm (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hn)
      obtain ⟨w, hw⟩ := hF.unit_coprime n hcop
      refine ⟨v, fun g hg => ?_⟩
      obtain ⟨t, -, ht⟩ := _root_.GlobalTheory.QLogDiff.dIn_of_QL p B O Q θ hF d μ hL ⊤ g hg α i
      refine ⟨↑w⁻¹ * t, ?_⟩
      rw [hαi] at ht
      push_cast at ht
      rw [map_mul, ← ht]
      have hw1 : algebraMap B Q (↑w⁻¹) * (n : Q) = 1 := by
        rw [← map_natCast (algebraMap B Q) n, ← map_mul, ← hw, Units.inv_mul, map_one]
      linear_combination ((p : Q) ^ v * coeff α g) * hw1

  have chainU : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), comb c e = s → ∀ N,
      Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N → In (⊤ : Ideal B) s →
        (∀ i, c i ∈ N) ∧ In N s := by
    intro c s hcs N hN hs
    induction hN with
    | refl => exact ⟨fun _ => trivial, hs⟩
    | tail _ hst ih =>
      exact _root_.GlobalTheory.step_independent p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst c s ih.1 ih.2
        (by rw [hcs, sub_self]; exact ql0 _)
  have U1 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∃ (c' : ι → B) (s' : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s' ∧ comb c' e = s' ∧
        ∀ i, c i = c' i * p := by
    intro c s hs hcs
    obtain ⟨hc, hsp⟩ := chainU c s hcs _ hch hs
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    refine ⟨c', (↑u⁻¹ : Q) • s, ?_, ?_, fun i => (hc' i).symm⟩
    · intro α
      obtain ⟨t, ht, h1⟩ := hsp α
      obtain ⟨t', h2⟩ := key t ht
      exact ⟨t', trivial, by rw [coeff_smul, h1, h2]⟩
    · have hc2 : c = fun i => c' i * p := funext fun i => (hc' i).symm
      rw [← hcs, hc2, comb_mul_right, smul_smul, hmapP, ← hu, Units.inv_mul, one_smul]
  have U2 : ∀ K (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∀ i, c i ∈ Ideal.span {(p : B) ^ K} := by
    intro K
    induction K with
    | zero => intro c s _ _ i; simp
    | succ K ih =>
      intro c s hs hcs i
      obtain ⟨c', s', hs', hcs', hc⟩ := U1 c s hs hcs
      rw [hc i, pow_succ]
      exact Ideal.mem_span_singleton.2 (mul_dvd_mul_right (Ideal.mem_span_singleton.1 (ih c' s' hs' hcs' i)) _)
  have U3 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → c = 0 := by
    intro c s hs hcs; funext i
    refine hF.complete.toIsHausdorff.haus (c i) fun n => ?_
    rw [SModEq.sub_mem, sub_zero, hsm]; exact U2 n c s hs hcs i
  refine ⟨he, fun f hf => ?_⟩

  obtain ⟨Fs, hF0, hFs⟩ : ∃ Fs : ℕ → {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f},
      Fs 0 = ⟨f, hf⟩ ∧ ∀ k, Fs (k + 1) = ⟨gF (Fs k), hgF (Fs k)⟩ :=
    ⟨fun k => Nat.rec ⟨f, hf⟩ (fun _ y => ⟨gF y, hgF y⟩) k, rfl, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ι → B, ∀ K i, x K i = ∑ k ∈ Finset.range K, (p : B) ^ k * bF (Fs k) i :=
    ⟨_, fun _ _ => rfl⟩
  have hrec : ∀ K, ∃ S, In (⊤ : Ideal B) S ∧ f = comb (x K) e + S + (p : Q) ^ K • (Fs K).1 := by
    intro K
    induction K with
    | zero =>
      have hx0 : x 0 = 0 := funext fun i => by simp [hx]
      refine ⟨0, fun α => ⟨0, trivial, by simp⟩, ?_⟩
      rw [hx0, comb_zero, hF0]; simp
    | succ K ih =>
      obtain ⟨S, hS, hfe⟩ := ih
      refine ⟨S + (p : Q) ^ K • sF (Fs K), ?_, ?_⟩
      · intro α
        obtain ⟨a, -, ha⟩ := hS α
        obtain ⟨c, -, hc⟩ := hsF (Fs K) α
        exact ⟨a + p ^ K * c, trivial, by simp [coeff_smul, ha, hc, map_add (f := _), map_mul, map_pow, map_natCast]⟩
      · have h1 : x (K + 1) = x K + fun i => (p : B) ^ K * bF (Fs K) i := by
          funext i; simp [hx, Finset.sum_range_succ]
        have h2 : (Fs (K + 1)).1 = gF (Fs K) := by rw [hFs]
        rw [h1, comb_add, GlobalTheory.BasisLift.comb_mul, h2, map_pow, map_natCast]
        conv_lhs => rw [hfe, heqF (Fs K)]
        simp only [smul_add, smul_smul, ← pow_succ]
        abel
  have hcau : ∀ m n, m ≤ n → ∀ i, x n i - x m i ∈ Ideal.span {(p : B) ^ m} := by
    intro m n hmn i
    rw [hx, hx, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    exact Ideal.mem_span_singleton.2
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _)
  have hlim : ∀ i, ∃ L : B, ∀ n, x n i - L ∈ Ideal.span {(p : B) ^ n} := by
    intro i
    obtain ⟨L, hL'⟩ := hF.complete.toIsPrecomplete.prec (f := fun n => x n i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_sub]; exact neg_mem (hcau m n hmn i))
    exact ⟨L, fun n => by have := hL' n; rwa [SModEq.sub_mem, hsm] at this⟩
  choose L hLx using hlim
  have hIn : In (⊤ : Ideal B) (f - comb L e) := by
    intro α
    obtain ⟨v, hv⟩ := V α
    obtain ⟨S, hS, hfe⟩ := hrec v
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hLx i v)
    have hmem : coeff α (f - comb L e) ∈ (algebraMap B Q).range := by
      rw [hfe]
      have e1 : comb (x v) e + S + (p : Q) ^ v • (Fs v).1 - comb L e =
          (comb (x v) e - comb L e) + S + (p : Q) ^ v • (Fs v).1 := by abel
      rw [e1, ← comb_sub, map_add (f := _), map_add (f := _), coeff_comb, coeff_smul]
      refine add_mem (add_mem (Subring.sum_mem _ fun i _ => ?_) ?_) (hv _ (Fs v).2)
      · rw [show (x v - L) i = c i * (p : B) ^ v from (hc i).symm,
          show algebraMap B Q (c i * (p : B) ^ v) * coeff α (e i) =
            algebraMap B Q (c i) * ((p : Q) ^ v * coeff α (e i)) by
              rw [map_mul, map_pow, map_natCast, mul_assoc]]
        exact Subring.mul_mem _ ⟨c i, rfl⟩ (hv _ (he i))
      · obtain ⟨a, -, ha⟩ := hS α; exact ⟨a, ha.symm⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, trivial, hb.symm⟩
  refine ⟨L, hIn, fun y hy => ?_⟩
  have hs : In (⊤ : Ideal B) (comb (y - L) e) := by
    intro α
    obtain ⟨a, -, ha⟩ := hIn α
    obtain ⟨a', -, ha'⟩ := hy α
    refine ⟨a - a', trivial, ?_⟩
    rw [map_sub, ← ha, ← ha', ← map_sub, comb_sub]
    congr 1; abel
  exact sub_eq_zero.1 (U3 _ _ hs rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinset
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem sections_coords_and_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T G
  obtain ⟨q, hq, hk9⟩ := _root_.GlobalTheory.jets_approx_sections_of_positive n Y ι La A H hH T
  obtain ⟨ε, hε, hk10⟩ := _root_.GlobalTheory.quot_jets_det_ne_zero n
  obtain ⟨k0, hk0⟩ := hk9 0 (fun _ _ => 1) (fun _ => differentiable_const _) ε hε
  have hpj : ∀ j : Fin n, ∀ P : Y,
      Differentiable ℂ (fun v : V n => v j - (A.chart (A.pick P) P) j) := fun j P =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable).sub_const _
  choose kj hkj using fun j : Fin n =>
    hk9 0 (fun P v => v j - (A.chart (A.pick P) P) j) (hpj j) ε hε
  obtain ⟨ka, hka⟩ := hk9 G (fun _ _ => 1) (fun _ => differentiable_const _) (1/2) (by norm_num)
  refine ⟨max k0 (max ka (Finset.univ.sup kj)), fun k hk => ?_⟩
  have hk0' : k ≥ k0 := le_trans (le_max_left _ _) hk
  have hka' : k ≥ ka := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkj' : ∀ j, k ≥ kj j := fun j =>
    le_trans (le_trans (Finset.le_sup (f := kj) (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  obtain ⟨F0, hF0s, hF0⟩ := hk0 k hk0'
  choose Fj hFjs hFj using fun j => hkj j k (hkj' j)
  obtain ⟨Fa, hFas, hFa⟩ := hka k hka'
  rw [zero_add] at hF0s hFjs
  refine ⟨F0, Fj, Fa, hF0s, hFjs, hFas, fun P hP => ?_⟩
  set i := A.pick P with hi
  set p := A.chart i P with hp
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  have hpt : p ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm p = P := (A.chart i).left_inv hPs
  have hdiffF : ∀ F : ι → Y → ℂ, ∀ la, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) p := by
    intro F la hF
    have h1 := hF.1 i
    have h2 : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
    rw [h2] at h1
    exact h1.differentiableAt ((A.chart i).open_target.mem_nhds hpt)
  have hE : DifferentiableAt ℂ (fun v => Complex.exp (-((k : ℂ) * q P v))) p :=
    ((((hq P hP) p).const_mul (k : ℂ)).neg).cexp
  set w0 : V n → ℂ := fun v => F0 i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw0
  set w : Fin n → V n → ℂ := fun j v => Fj j i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw
  have hd0 : DifferentiableAt ℂ w0 p := (hdiffF F0 _ hF0s).mul hE
  have hdj : ∀ j, DifferentiableAt ℂ (w j) p := fun j => (hdiffF (Fj j) _ (hFjs j)).mul hE
  obtain ⟨h0a, h0b⟩ := hF0 P hP
  have e1 : ‖w0 p - 1‖ ≤ ε := by
    simp only [hw0, hsymm]; exact h0a
  have e2 : ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε := h0b
  have e3 : ∀ j, ‖w j p‖ ≤ ε := by
    intro j
    have := (hFj j P hP).1
    simp only [sub_self, sub_zero] at this
    simp only [hw, hsymm]; exact this
  have e4 : ∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε := fun j => (hFj j P hP).2
  obtain ⟨hne, hdet⟩ := hk10 p w0 w hd0 hdj e1 e2 e3 e4
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [hw0, hsymm, h0, zero_mul]
  · unfold WeightedAtlas.IsCoordAt
    have hfun : A.zLoc F0 Fj i = fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) := by
      funext v
      simp only [WeightedAtlas.zLoc, hw, hw0]
      congr 1
      funext j
      rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
    rw [← hi, ← hp, hfun]
    exact hdet
  · intro h0
    have := (hFa P hP).1
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at this
    norm_num at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

def TateIsoO.transport {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z)
    (I : TateIsoO D k Q act e) : TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := Φ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n b x := by rw [I.lin, hact]
  ker n hn hc x := by rw [map_eq_one_iff Φ Φ.injective]; exact I.ker n hn hc x
  onto n hn hc q := by
    obtain ⟨q, rfl⟩ := Φ.surjective q
    rw [← map_pow, map_eq_one_iff Φ Φ.injective, I.onto n hn hc]
    exact exists_congr fun x => Φ.injective.eq_iff.symm
  tower n m hn hm hc x := by rw [← map_pow, I.tower n m hn hm hc]
  isom n hn hc x y := he _ _ _ _ (I.isom n hn hc x y)

@[simp] theorem TateIsoO.transport_ev {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type}
    [Group Q] [Group Q'] {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop}
    {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x))
    (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z) (I : TateIsoO D k Q act e) (n : ℕ) (y : D.La) :
    (I.transport Φ hact he).ev n y = Φ (I.ev n y) := rfl

theorem tateIsoO_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left), IsGrpPullback o'.A o.A f φ → IsSquare φ φ₂ → (∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left) → LBIso o'.P (o.P.pull φ₂) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S'), (∀ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧ (∀ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∃ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  intro p _ D R _ b N N' S S' s s' o o' f φ φ₂ hp hsq hact hpol k _ _ x
  have e : φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · change (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) ≫ (fst o.A o.A).left =
        ((lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂) ≫ (fst o.A o.A).left
      rw [Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, Category.assoc, hsq.1,
        ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
    · change (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) ≫ (snd o.A o.A).left =
        ((lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂) ≫ (snd o.A o.A).left
      rw [Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, Category.assoc, hsq.2,
        ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hL' : (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left).IsLB := pull_isLB o'.isLB _
  have H1 : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    LBIso.chartPull (chartPullPull o'.P _ _ rfl) (chartPullSame o.P _ (fun _ => φ₂) _ _ fun _ => e) hpol
  have hw : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullId _) (chartPullOut o.P (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1) φ
      (fun _ => φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) fun _ => rfl) H1
  let Φ := GlobalTheory.ObjPull.pushEquiv hp (Over.mk x)
  have hW : ∀ (n : ℕ) (g g' : Over.mk x ⟶ o'.A) (z : kˣ),
      Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z) ↔
        Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (Φ g) (Φ g') (unitOn z) :=
    fun n g g' z => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f φ _ _ hL hL' hp hw (Over.mk x) n g g' (Φ g) (Φ g')
      _ rfl rfl
  have hA : ∀ c (g : Over.mk x ⟶ o'.A), Φ (g ≫ o'.act.act c) = Φ g ≫ o.act.act c := fun c g =>
    Over.OverMorphism.ext (by
      show (g ≫ o'.act.act c).left ≫ φ = (Φ g ≫ o.act.act c).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc])
  refine ⟨fun I' => ⟨I'.transport Φ hA fun n g g' z h => (hW n g g' z).1 h, fun n y => rfl⟩,
    fun I => ⟨I.transport Φ.symm (fun c g => Φ.injective ?_) (fun n g g' z h => (hW n _ _ z).2 ?_), fun n y => ?_⟩⟩
  · rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  · rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
  · rw [TateIsoO.transport_ev]
    exact (GlobalTheory.ObjPull.pushEquiv_symm_left hp (Over.mk x) (I.ev n y)).symm

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSequenceGuards
section
noncomputable section

namespace GlobalTheory.Proof.WeightSequenceEntries

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

theorem padZero_eq {a : ℕ} (b : ℕ) (ν : DomWeight a) (j : Fin b) :
    PaddedWittNormSquare.padZero b ν j = PaddedLastEntry.padZero b ν j := rfl

theorem lastEntry_eq {a : ℕ} (ν : DomWeight a) : PaddedWittNormSquare.lastEntry ν = PaddedLastEntry.lastEntry ν := rfl

theorem normSq_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    PaddedWittNormSquare.normSq lam v = PaddedLastEntry.invNormSq lam v := rfl

theorem unitSq_eq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) :
    PaddedWittNormSquare.unitNormSq r z = PaddedLastEntry.unitSq r z := rfl

theorem tmax_eq {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) :
    PaddedWittNormSquare.tmax b ν Om S = PaddedLastEntry.tmax b ν S Om := rfl

theorem opNormSqLe_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' T t ↔ PaddedLastEntry.OpNormSqLe lam lam' T t := by
  unfold PaddedWittNormSquare.OpNormSqLe PaddedLastEntry.OpNormSqLe
  simp only [normSq_eq]

theorem stepWeights_iff {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) :
    (∃ s' s : ℤ, PaddedWittNormSquare.IsStepWeight lam ν lam' s' s) ↔ PaddedLastEntry.StepWeights lam ν lam' := by
  unfold PaddedWittNormSquare.IsStepWeight PaddedLastEntry.StepWeights
  constructor
  · rintro ⟨s', s, hν, hpos, hpad⟩
    exact ⟨hpos, ⟨s', hν⟩, ⟨s, fun j => (hpad j).trans (padZero_eq b ν j)⟩⟩
  · rintro ⟨hpos, ⟨s', hν⟩, ⟨s, hpad⟩⟩
    exact ⟨s', s, hν, hpos, fun j => (hpad j).trans (padZero_eq b ν j).symm⟩

theorem stepWeights_family_iff {ι : Type} {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) :
    (∃ s' s : ι → ℤ, ∀ τ, PaddedWittNormSquare.IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) ↔
      ∀ τ, PaddedLastEntry.StepWeights (lam τ) (ν τ) (lam' τ) := by
  constructor
  · rintro ⟨s', s, h⟩ τ
    exact (stepWeights_iff (lam τ) (ν τ) (lam' τ)).1 ⟨s' τ, s τ, h τ⟩
  · intro h
    choose s' s hs using fun τ => (stepWeights_iff (lam τ) (ν τ) (lam' τ)).2 (h τ)
    exact ⟨s', s, hs⟩

theorem guard_iff {ι : Type} {a b : ℕ} (hab : a ≤ b) (ν : ι → DomWeight a) :
    (∀ τ, a < b ∨ PaddedWittNormSquare.lastEntry (ν τ) = 0) ↔ (a = b → ∀ τ, PaddedLastEntry.lastEntry (ν τ) = 0) := by
  constructor
  · intro h heq τ
    rcases h τ with hlt | h0
    · exact absurd heq (ne_of_lt hlt)
    · exact (lastEntry_eq (ν τ)).symm.trans h0
  · intro h τ
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ((lastEntry_eq (ν τ)).trans (h heq τ))

theorem growth_iff {ι : Type} [Fintype ι] {a b : ℕ} (G : VCx ι a b → ℂ) (S : ℝ) (r : ι → ℝ) :
    (∀ z, ‖G z‖ ≤ S * Real.exp (PaddedWittNormSquare.unitNormSq r z / 2)) ↔
      ∀ z, ‖G z‖ ≤ S * Real.exp (PaddedLastEntry.unitSq r z / 2) := by
  simp only [unitSq_eq]

theorem conclusion_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b)
    (G : VCx ι a b → ℂ) (S : ℝ) (Om : ι → ℝ) (cD : ι → ℂ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedWittNormSquare.lastEntry (ν τ)) (PaddedWittNormSquare.tmax b ν Om S) ↔
      PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedLastEntry.lastEntry (ν τ)) (PaddedLastEntry.tmax b ν S Om) := by
  simp only [opNormSqLe_iff, tmax_eq, lastEntry_eq]

theorem blockBound_iff : PaddedWittNormSquare.BlockBound ↔ PaddedLastEntry.BlockBound := by
  unfold PaddedWittNormSquare.BlockBound PaddedLastEntry.BlockBound
  constructor
  · intro h ι _ a b hab lam ν lam' hstep hguard r Om cD hr hOm hc G S hG hgrowth
    obtain ⟨s', s, hs⟩ := (stepWeights_family_iff lam ν lam').2 hstep
    exact (conclusion_iff lam ν lam' G S Om cD).1
      (h ι a b hab lam ν lam' s' s hs ((guard_iff hab ν).2 hguard) G S r Om cD hG hr
        ((growth_iff G S r).2 hgrowth) hOm hc)
  · intro h ι _ a b hab lam ν lam' s' s hs hguard G S r Om cD hG hr hgrowth hOm hc
    exact (conclusion_iff lam ν lam' G S Om cD).2
      (h ι a b hab lam ν lam' ((stepWeights_family_iff lam ν lam').1 ⟨s', s, hs⟩)
        ((guard_iff hab ν).1 hguard) r Om cD hr hOm hc G S hG ((growth_iff G S r).1 hgrowth))

end GlobalTheory.Proof.WeightSequenceEntries
end
end

