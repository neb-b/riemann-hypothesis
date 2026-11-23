module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.IteratedDerivZeroOfBound
section
noncomputable section

open Metric

namespace PositivityTheory.Rg.Sw.SP

theorem iteratedDeriv_zero_of_bound {f : ℂ → ℂ} {ε C : ℝ} {r : ℕ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (ball 0 ε)) (hb : ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖z‖ ^ r) {j : ℕ} (hj : j < r) :
    iteratedDeriv j f 0 = 0 := by
  have key : ∀ R : ℝ, 0 < R → R < ε → ‖iteratedDeriv j f 0‖ ≤ j.factorial * (C * R ^ r) / R ^ j := by
    intro R hR hRε
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR ?_ ?_
    · exact hf.diffContOnCl_ball (closedBall_subset_ball hRε)
    · intro z hz
      have hz' : z ∈ ball (0 : ℂ) ε := by
        rw [mem_sphere_zero_iff_norm] at hz
        rw [mem_ball_zero_iff, hz]; exact hRε
      have := hb z hz'
      rwa [mem_sphere_zero_iff_norm.1 hz] at this
  have hlim : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * (C * R ^ r) / R ^ j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have e : ∀ R : ℝ, 0 < R → (j.factorial : ℝ) * (C * R ^ r) / R ^ j = j.factorial * C * R ^ (r - j) := by
      intro R hR
      have : R ^ r = R ^ (r - j) * R ^ j := by rw [← pow_add, Nat.sub_add_cancel hj.le]
      rw [this]; field_simp
    have h0 : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhds 0) (nhds ((j.factorial : ℝ) * C * 0 ^ (r - j))) :=
        (continuous_const.mul (continuous_pow _)).tendsto 0
      rw [zero_pow (Nat.sub_ne_zero_of_lt hj), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with R hR using (e R hR).symm
  have hle : ‖iteratedDeriv j f 0‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with R hR using key R hR.1 hR.2
  exact norm_le_zero_iff.1 hle

theorem norm_le_of_circle {q : ℂ → ℂ} (hq : Differentiable ℂ q) {r : ℕ} {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ r * q w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖q z‖ ≤ M := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) 1) isBounded_ball
    hq.diffContOnCl (fun w hw => ?_) ?_
  · rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hw
    have := hM w hw
    rwa [norm_mul, norm_pow, hw, one_pow, one_mul] at this
  · rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff]; exact hz

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorDefs
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R] {ρ : ℕ}

abbrev Pm (R : Type) [CommRing R] (ρ : ℕ) := MvPolynomial (Fin ρ × Fin ρ) R

def Xm (R : Type) [CommRing R] (ρ : ℕ) : Matrix (Fin ρ) (Fin ρ) (Pm R ρ) := fun a d => X (a, d)

def del (p q : Fin ρ) : Derivation R (Pm R ρ) (Pm R ρ) :=
  mkDerivation R fun ad => (X (ad.1, p) * X (q, ad.2) : Pm R ρ)

def opE (α : R) (p q : Fin ρ) : Pm R ρ →ₗ[R] Pm R ρ :=
  LinearMap.mulLeft R (C α * X (q, p)) + (del p q).toLinearMap

def detE (α : R) : Pm R ρ →ₗ[R] Pm R ρ :=
  ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : R) • (List.finRange ρ).foldr (fun k g => opE α k (σ k) ∘ₗ g) LinearMap.id

def ren {r s : ℕ} (I J : Fin r ↪ Fin s) : Pm R r →ₐ[R] Pm R s := rename fun pq => (J pq.1, I pq.2)

def MComm : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (α : R) (p q p' q' : Fin ρ),
  opE α p q ∘ₗ opE α p' q' = opE α p' q' ∘ₗ opE α p q

def DelDet : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (p q : Fin ρ), del p q (Xm R ρ).det = X (q, p) * (Xm R ρ).det

def RenInt : Prop := ∀ (R : Type) [CommRing R] (r s : ℕ) (I J : Fin r ↪ Fin s) (α : R) (p q : Fin r) (f : Pm R r),
  opE α (I p) (J q) (ren I J f) = ren I J (opE α p q f)

def Core : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (α : R),
  detE α (1 : Pm R ρ) = (∏ i ∈ Finset.range ρ, (C α - (i : Pm R ρ))) * (Xm R ρ).det

def Iter : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (α : R) (N : ℕ),
  (detE α)^[N] (1 : Pm R ρ) = (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) * (Xm R ρ).det ^ N

end PositivityTheory.Rg.Sw.SP.Mi
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.WROrdA
section
noncomputable section

open Function

namespace PositivityTheory.Rg.Sw.SP

theorem entire_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℕ)
    (h : ∀ j < r, iteratedDeriv j f 0 = 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = z ^ r * g z := by
  have hdiff : ∀ k : ℕ, Differentiable ℂ ((swap dslope (0 : ℂ))^[k] f) := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (Complex.differentiableOn_dslope (f := (swap dslope (0 : ℂ))^[k] f) (s := Set.univ) (c := 0)
        Filter.univ_mem).2 ih.differentiableOn
      simpa [swap, differentiableOn_univ] using this
  obtain ⟨p, hp⟩ := hf.analyticAt 0
  obtain ⟨R, hR⟩ := hp
  have hcoeff : ∀ k < r, p.coeff k = 0 := by
    intro k hk
    have h1 := hR.factorial_smul (y := (1 : ℂ)) k
    have h2 : iteratedDeriv k f 0 = iteratedFDeriv ℂ k f 0 (fun _ => 1) := by
      rw [iteratedDeriv_eq_iteratedFDeriv]
    rw [← h2, h k hk] at h1
    have h3 : p.coeff k = p k (fun _ => 1) := rfl
    rw [h3]
    rw [nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h4 | h4
    · exact absurd h4 (by exact_mod_cast Nat.factorial_ne_zero k)
    · exact h4
  have hzero : ∀ k < r, (swap dslope (0 : ℂ))^[k] f 0 = 0 := by
    intro k hk
    have := (hR.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1
    rw [← this, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
    exact hcoeff k hk
  refine ⟨(swap dslope (0 : ℂ))^[r] f, hdiff r, fun z => ?_⟩
  have := pow_sub_smul_iterate_dslope_of_zero r hzero z
  simpa [smul_eq_mul] using this.symm

end PositivityTheory.Rg.Sw.SP
end
end

