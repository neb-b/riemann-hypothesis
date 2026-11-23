module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliCasimir
open Polynomial

noncomputable def rev {ι : Type} (s : Finset ι) (f : ι → ℂ) : ℂ[X] := ∏ l ∈ s, (1 + C (f l) * X)

theorem rev_coeff {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    (rev s f).coeff 0 = 1 ∧ (rev s f).coeff 1 = ∑ l ∈ s, f l ∧
      2 * (rev s f).coeff 2 = (∑ l ∈ s, f l) ^ 2 - ∑ l ∈ s, f l ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rev, coeff_one]
  | insert a s ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
    have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
    have : rev (insert a s) f = rev s f + C (f a) * (X * rev s f) := by
      simp only [rev, prod_insert ha]; ring
    rw [this, sum_insert ha, sum_insert ha]
    simp only [coeff_add, coeff_C_mul]
    refine ⟨?_, ?_, ?_⟩
    · simp [h0]
    · rw [c1, h0, h1]; ring
    · rw [c2, h1]
      linear_combination h2

theorem rev_eval {ι : Type} (s : Finset ι) (f : ι → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (rev s f).eval t = t ^ s.card * ∏ l ∈ s, (t⁻¹ + f l) := by
  rw [rev, eval_prod, ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  simp; field_simp

theorem scalar_core (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by
  have key : C e * rev univ ρ + X * ∑ i, C (a i) * rev (univ.erase i) ρ
      + X ^ 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (b i j) * rev ((univ.erase i).erase j) ρ
      + X ^ 3 * ∑ d ∈ range (n - 2), C (r d) * X ^ (n - 3 - d) * (1 + C c * X) ^ d
      = C e * rev univ μ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0:ℂ)).infinite_compl
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [Set.mem_setOf_eq, eval_add, eval_mul, eval_C, eval_X, eval_pow, Polynomial.eval_finsetSum,
      eval_one, rev_eval _ _ _ ht, card_univ, Fintype.card_fin]
    have := congrArg (fun z => t ^ n * z) (h t⁻¹)
    simp only [mul_add, mul_sum] at this ⊢
    refine Eq.trans ?_ (this.trans (by ring))
    congr 1
    · congr 1
      · congr 1
        · ring
        · refine sum_congr rfl fun i _ => ?_
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
          obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          have : t ^ n = t * t ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
      · refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
        have hij : j ≠ i := (mem_filter.1 hj).2.ne'
        rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _),
          card_univ, Fintype.card_fin]
        have : t ^ n = t ^ 2 * t ^ (n - 1 - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
    · refine sum_congr rfl fun d hd => ?_
      have hd := mem_range.1 hd
      have h1 : t ^ n = t ^ 3 * t ^ (n - 3 - d) * t ^ d := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : (1 + c * t) = t * (t⁻¹ + c) := by field_simp
      rw [h1, h2, mul_pow]; ring
  have k1 := congrArg (fun p => p.coeff 1) key
  have k2 := congrArg (fun p => p.coeff 2) key
  simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul'] at k1 k2
  have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
  have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
  rw [c1] at k1
  rw [c2] at k2
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul, (rev_coeff _ _).1, (rev_coeff _ _).2.1, le_refl, if_true,
    Nat.sub_self, mul_one] at k1 k2
  norm_num at k1 k2
  constructor
  · linear_combination k1
  · have p1 := (rev_coeff univ ρ).2.2
    have p2 := (rev_coeff univ μ).2.2
    have : ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i = ∑ i, a i * (∑ l, ρ l - ρ i) := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_sub (mem_univ _), mul_comm]
    rw [this]
    linear_combination 2 * k2 - e * p1 + e * p2

theorem sum_sq_split {A : Type} [AddCommGroup A] {n : ℕ} (F : Fin n → Fin n → A) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (F i j + F j i) := by
  have h1 : ∀ i j, F i j = (if i = j then F i j else 0) + (if i < j then F i j else 0)
      + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => h1 i j]
  simp only [sum_add_distrib, sum_filter, sum_ite_eq, mem_univ, if_true]
  rw [add_assoc, sum_comm (f := fun i j => if j < i then F i j else 0)]

theorem sum_diff {A : Type} [AddCommGroup A] [Module ℂ A] {n : ℕ} (x : Fin n → A) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (x i - x j)
      = ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • x i := by
  simp only [sum_sub_distrib]
  have : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), x j
      = ∑ j, ∑ i ∈ univ.filter (fun i => i < j), x j := by
    simp only [sum_filter]; exact sum_comm
  rw [this, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_const, sum_const, filter_lt_eq_Ioi, filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  have := i.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem sq_sub_cas {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) :
    (∑ i, E i i) * (∑ i, E i i) - Formalism.REAL.Cas E
      = (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i := by
  rw [← sum_diff, Formalism.REAL.Cas, sum_mul_sum, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [sum_sq_split]
  simp only [sub_self, sum_const_zero, zero_add, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (mem_filter.1 hj).2.ne
  have h1 := hE i j j i
  have h2 := hE i i j j
  simp only [if_true, hij, hij.symm, if_false, sub_zero] at h1 h2
  rw [two_smul, ← h1, ← sub_eq_zero.1 h2]
  abel

theorem cas_of_capelli : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  intro M _ _ n E mu hn hE h
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders (Module.End ℂ M) n E
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun φ : Module.Dual ℂ (Module.End ℂ M) =>
    scalar_core n hn ρ (fun s => (mu s : ℂ)) (fun i => φ (E i i))
      (fun i j => φ (E i i * E j j - E j i * E i j)) (fun d => φ (Rm d)) (φ 1) (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
            = (∏ s, (Y + (mu s : ℂ))) • (1 : Module.End ℂ M) := by
          ext w; simpa using h Y w
        have h2 := congrArg φ ((hR _).symm.trans h1)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h2
        exact h2)
  have e1 : ∑ i, E i i = (∑ l, (mu l : ℂ)) • (1 : Module.End ℂ M) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := (core φ).1
    rw [hρ0] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, smul_eq_mul]
    linear_combination this
  have e2 : Formalism.REAL.Cas E = (casG mu : ℂ) • (1 : Module.End ℂ M) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have h2 := (core φ).2
    have h3 := congrArg φ (sq_sub_cas E hE)
    rw [e1, smul_mul_smul_comm, mul_one] at h3
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub φ, map_sum, map_smul, smul_eq_mul] at h3 h2 ⊢
    have h4 : (casG mu : ℂ) = ∑ l, (mu l : ℂ) ^ 2 - ∑ l, ρ l ^ 2 := by
      simp [casG, Formalism.QuantumDeterminants.rhoStd, hρ]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * φ (E i i)
        = - (2 * ∑ i, (0 - ρ i) * φ (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h4]
    rw [h5] at h3
    linear_combination -h3 - h2
  intro w
  rw [e2]; simp

end GlobalTheory.CapelliCasimir
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem thresholds_of_gapOK : ∀ (k r : ℕ) (h : ℝ), GapOK k r h →
    JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  intro k r h hg
  obtain ⟨hk, -, -, h4⟩ := hg
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hA : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 2 ≤ aOf r h - 1 := by linarith
  have hN : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold JF.TransportedAlt
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ (by positivity)]
    nlinarith
  · have hAB : B.AB k r = AG k r / 2 + 1 := by unfold B.AB AG; ring
    rw [hAB]
    linarith
  · linarith
  · linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedAction

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem exp_mem {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  refine CCRuleCW.exp_mem_UH (Hpk k r) _ ?_
  have hL : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem : (1 : Mx k r) ∈ UH (Hpk k r) := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem lie_conj {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g⁻¹ * X * g) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
  have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hL : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have A : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hU]
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hU]
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
        = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * Hpk k r)) + (Hpk k r * g⁻¹) * X * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hL]; simp

theorem lie_conj' {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g * X * g⁻¹) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
  have := lie_conj hX (unitary_Hecke_group k r g hg).2.1
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at this

theorem hasDerivAt_local {X g : Mx k r} (hX : InLieHpk k r X) {f F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUH (Hpk k r) h → f h = F h)
    (hg : g ∈ UH (Hpk k r)) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds hgU)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with t ht
  exact hfF _ ht ((unitary_Hecke_group k r g hg).2.2 _ (exp_mem hX t))

theorem exists_lin {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    ∃ L : Mx k r →L[ℝ] H, ∀ X, InLieHpk k r X → dsig (k := k) (r := r) σ X v = L X ∧
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 one_mem
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have h := hasDerivAt_local hX hU h1 hF hfF one_mem
  simp only [Matrix.one_mul] at h
  have e : dsig (k := k) (r := r) σ X v = fderiv ℝ F 1 X := h.deriv
  exact ⟨e, e ▸ h⟩

theorem hasDerivAt_dsig {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 := by
  obtain ⟨L, hL⟩ := exists_lin hv
  exact (hL X hX).2

theorem hasDerivAt_apply {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (T : H →L[ℂ] H) :
    HasDerivAt (fun t : ℝ => T (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (T (dsig (k := k) (r := r) σ X v)) 0 :=
  (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dsig hX hv)

theorem dsig_zero (X : Mx k r) : dsig (k := k) (r := r) σ X (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add {X : Mx k r} (hX : InLieHpk k r X) {v w : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (v + w) = dsig (k := k) (r := r) σ X v + dsig (k := k) (r := r) σ X w := by
  have h := (hasDerivAt_dsig hX hv).add (hasDerivAt_dsig hX hw)
  rw [← h.deriv]
  unfold dsig
  congr 1
  funext t
  simp

theorem dsig_smul {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (a • v) = a • dsig (k := k) (r := r) σ X v := by
  have h := (hasDerivAt_dsig hX hv).const_smul a
  rw [← h.deriv]
  unfold dsig
  congr 1
  funext t
  simp

theorem dsig_smooth (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hv g₀ hg₀
  let L : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hL : ∀ x, L x = x * X := by intro x; simp [L]
  refine ⟨U, fun g => fderiv ℝ F g (L g), hU, hgU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  · intro g hg hgH
    have h1 := hasDerivAt_local hX hU hg hF hfF hgH
    have h2 := hasDerivAt_apply hX hv (σ g)
    have e : (fun u : ℝ => σ (g * NormedSpace.exp ((u : ℂ) • X)) v) =
        fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
      funext t
      rw [Hecke_multiplication k r ε mu H σ hσ g hgH _ (exp_mem hX t)]
      rfl
    rw [e] at h1
    simp only [hL]
    exact h2.unique h1

theorem dsig_conj (hσ : IsDSHpk k r ε mu σ) {X g : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hg : g ∈ UH (Hpk k r)) :
    σ g (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (g * X * g⁻¹) (σ g v) := by
  rw [← (hasDerivAt_apply hX hv (σ g)).deriv]
  unfold dsig
  congr 1
  funext t
  obtain ⟨hu, hi, hm⟩ := unitary_Hecke_group k r g hg
  have hi1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have e1 : σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) = σ (g * NormedSpace.exp ((t : ℂ) • X)) v := by
    rw [Hecke_multiplication k r ε mu H σ hσ g hg _ (exp_mem hX t)]; rfl
  have e2 : σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g v) =
      σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g) v := by
    rw [Hecke_multiplication k r ε mu H σ hσ _ (exp_mem (lie_conj' hX hg) t) g hg]; rfl
  have e3 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, e2, e3, Matrix.exp_conj _ _ hu, Matrix.mul_assoc _ g⁻¹ g, hi1, Matrix.mul_one]

theorem dsig_kfin [CompleteSpace H] (hK : PI.KFinSmooth) (hmu : IsHCParam mu) (hσ : IsDSHpk k r ε mu σ)
    {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : IsKFinHpk (k := k) (r := r) σ v) :
    IsKFinHpk (k := k) (r := r) σ (dsig (k := k) (r := r) σ X v) := by
  obtain ⟨S, hfd, hvS, hS⟩ := hv
  have hsm : ∀ x ∈ S, x ∈ smoothVecs (k := k) (r := r) σ := fun x hx =>
    hK k r ε mu H σ hmu hσ x ⟨S, hfd, hx, hS⟩
  refine ⟨Submodule.span ℂ {y | ∃ Y, InLieHpk k r Y ∧ ∃ s ∈ S, y = dsig (k := k) (r := r) σ Y s}, ?_,
    Submodule.subset_span ⟨X, hX, v, hvS, rfl⟩, ?_⟩
  · obtain ⟨fs, hfs⟩ := (Submodule.fg_iff_finiteDimensional S).2 hfd
    have hfsS : ∀ x : fs, (x : H) ∈ S := fun x => hfs ▸ Submodule.subset_span x.2
    choose L hL using fun x : fs => exists_lin (hsm x (hfsS x))
    let b := Module.finBasis ℝ (Mx k r)
    let T : Submodule ℂ H := Submodule.span ℂ (Set.range fun p : fs × Fin (Module.finrank ℝ (Mx k r)) =>
      L p.1 (b p.2))
    haveI : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
    rintro _ ⟨Y, hY, s, hs, rfl⟩
    rw [← hfs] at hs hsm
    show dsig (k := k) (r := r) σ Y s ∈ T
    induction hs using Submodule.span_induction with
    | mem y hy =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(hL ⟨y, hy⟩ Y hY).1, ← b.sum_repr Y, map_sum]
      refine T.sum_mem fun j _ => ?_
      rw [map_smul]
      exact T.smul_of_tower_mem _ (Submodule.subset_span ⟨(⟨y, hy⟩, j), rfl⟩)
    | zero => rw [dsig_zero]; exact T.zero_mem
    | add x y hx hy ihx ihy => rw [dsig_add hY (hsm x hx) (hsm y hy)]; exact T.add_mem ihx ihy
    | smul a x hx ih => rw [dsig_smul hY a (hsm x hx)]; exact T.smul_mem a ih
  · intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Y, hY, s, hs, rfl⟩ := hy
      rw [dsig_conj hσ hY (hsm s hs) hg.1]
      exact Submodule.subset_span ⟨_, lie_conj' hY hg.1, _, hS g hg s hs, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add (f := _)]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

theorem dsig_skew (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v w : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    ⟪dsig (k := k) (r := r) σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) σ X w⟫_ℂ := by
  obtain ⟨h1, hunit⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ
  have h := (hasDerivAt_dsig hX hv).inner ℂ (hasDerivAt_dsig hX hw)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) v, σ (NormedSpace.exp ((t : ℂ) • X)) w⟫_ℂ) =
      fun _ => ⟪v, w⟫_ℂ := by
    funext t
    exact (LinearMap.norm_map_iff_inner_map_map
      ((σ (NormedSpace.exp ((t : ℂ) • X)) : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 (hunit _ (exp_mem hX t)) v w
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, h1, ContinuousLinearMap.one_apply] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem dsig_TK (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDS ε mu) {X : Mx k r} (hX : InLieHpk k r X) :
    ∀ v ∈ R.TK, v ∈ R.sm ∧ dsig (k := k) (r := r) R.σ X v ∈ R.TK := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hy
    have hs := hK k r ε mu R.H R.σ hR.1 hR.2 v₀ hv₀
    refine ⟨smooth_right_action k r ε mu R.H R.σ hR.2 v₀ hs g hg, ?_⟩
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
    have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have h := dsig_conj hR.2 (lie_conj hX hg) hs hg
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hi1, Matrix.one_mul, Matrix.mul_one]
    rw [e] at h
    rw [← h]
    exact Submodule.subset_span ⟨g, hg, _, dsig_kfin hK hR.1 hR.2 (lie_conj hX hg) hv₀, rfl⟩
  | zero => exact ⟨R.smSub.zero_mem, by rw [dsig_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    exact ⟨R.smSub.add_mem ihx.1 ihy.1, by rw [dsig_add hX ihx.1 ihy.1]; exact Submodule.add_mem _ ihx.2 ihy.2⟩
  | smul a x _ ih =>
    exact ⟨R.smSub.smul_mem a ih.1, by rw [dsig_smul hX a ih.1]; exact Submodule.smul_mem _ a ih.2⟩

theorem derived_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) :=
  fun hK _ _ _ _ R hR _ hX =>
    ⟨fun _ hv => ⟨dsig_smooth hR.2 hX hv, hasDerivAt_dsig hX hv⟩, fun _ hv _ hg => dsig_conj hR.2 hX hv hg,
      fun _ hv => dsig_kfin hK hR.1 hR.2 hX hv, fun v hv => (dsig_TK hK R hR hX v hv).2,
      fun _ hv _ hw => dsig_skew hR.2 hX hv hw⟩

end GlobalTheory.DerivedAction
end
end

