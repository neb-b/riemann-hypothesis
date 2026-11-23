module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerMemLatticeSubBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0272
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
section
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.TorusSymbol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma isOpen_omegaSet (n : ℕ) : IsOpen (OmegaSet n) := by
  have h : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [h]
  refine isOpen_iInter_of_finite fun i => ?_
  have hc : Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z := by
    have hi : (i : ℕ) + 1 ≤ n := i.2
    simp only [lead, dif_pos hi]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  exact isOpen_ne_fun hc continuous_const

lemma differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : DifferentiableAt ℂ F z :=
  (hF.1.contDiffAt ((isOpen_omegaSet n).mem_nhds hz)).differentiableAt (by simp)

lemma lop_add (Y : Matrix (Fin n) (Fin n) ℂ) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) (hG : G ∈ OmF n) : lop Y (F + G) = lop Y F + lop Y G := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.add_apply, if_pos hz]
    have h : fderiv ℂ (F + G) z = fderiv ℂ F z + fderiv ℂ G z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.add (differentiableAt_of_mem hG hz).hasFDerivAt).fderiv
    rw [h]
    simp only [ContinuousLinearMap.add_apply]
    ring
  · simp [lop, if_neg hz]

lemma lop_smul (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) : lop Y (s • F) = s • lop Y F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.smul_apply, if_pos hz]
    have h : fderiv ℂ (s • F) z = s • fderiv ℂ F z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.const_smul s).fderiv
    rw [h]
    simp
  · simp [lop, if_neg hz]

lemma lop_sum (Y : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hf : ∀ i, f i ∈ OmF n) :
    lop Y (∑ i ∈ s, f i) = ∑ i ∈ s, lop Y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp [lop, if_pos hz]
    · simp [lop, if_neg hz]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, lop_add Y (hf i) (Submodule.sum_mem _ fun j _ => hf j), ih]

def wtL (c : Fin n) (w : List (Fin n × Fin n)) : ℝ :=
  (w.map fun p => (if p.1 = c then (1 : ℝ) else 0) - (if p.2 = c then 1 else 0)).sum

lemma lw_mem (H : HolFacts) (μ : Fin n → ℤ) (w : List (Fin n × Fin n)) : lw w (PhiO μ) ∈ OmF n := by
  induction w with
  | nil => exact (H n μ).2.2.1
  | cons p w ih => exact (H n μ).1 _ _ ih

lemma lop_lw (H : HolFacts) (μ : Fin n → ℤ) (c : Fin n) (w : List (Fin n × Fin n)) :
    lop (Matrix.single c c 1) (lw w (PhiO μ)) =
      ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lw w (PhiO μ) := by
  induction w with
  | nil =>
    have h := (H n μ).2.2.2.1 c
    simpa [wtL, lw] using h
  | cons p w ih =>
    obtain ⟨a, b⟩ := p
    have hF := lw_mem H μ w
    have rel := (H n μ).2.1 (lw w (PhiO μ)) c c a b hF
    have hlw : lw ((a, b) :: w) (PhiO μ) = lop (Matrix.single a b 1) (lw w (PhiO μ)) := rfl
    have hwt : wtL c ((a, b) :: w) =
        ((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0)) + wtL c w := by
      simp [wtL]
    rw [ih, lop_smul _ _ hF] at rel
    have rel' : lop (Matrix.single c c 1) (lop (Matrix.single a b 1) (lw w (PhiO μ))) =
        ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lop (Matrix.single a b 1) (lw w (PhiO μ)) +
        ((((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0) : ℝ)) : ℂ) •
          lop (Matrix.single a b 1) (lw w (PhiO μ)) := by
      rw [sub_eq_iff_eq_add] at rel
      rw [rel, add_comm]
      congr 1
      by_cases h1 : a = c <;> by_cases h2 : b = c
      · subst h1; subst h2; simp
      · subst h1; simp [h2]
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    rw [hlw, rel', hwt, ← add_smul]
    congr 1
    push_cast
    ring

lemma exists_tor (ε : Fin n → Bool) (θ : Fin n → ℝ) : ∃ k : KG ε, toMK k = tor θ := by
  have hH : (tor θ)ᴴ = tor (-θ) := by
    unfold tor
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp [Pi.star_apply, ← Complex.exp_conj]
  have hm : ∀ θ : Fin n → ℝ, tor θ * tor (-θ) = 1 := by
    intro θ
    unfold tor
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← Complex.exp_add]
    simp
  have h1 : tor θ * (tor θ)ᴴ = 1 := by rw [hH, hm]
  have h2 : (tor θ)ᴴ * tor θ = 1 := by
    have := hm (-θ)
    rwa [neg_neg, ← hH] at this
  have hJ : tor θ * Jm ε = Jm ε * tor θ := by
    unfold tor Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  have hUJ : inUJ ε (tor θ) := by
    unfold inUJ
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hK : tor θ ∈ Kset ε := by
    refine ⟨?_, hJ⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact h1
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨tor θ, (tor θ)ᴴ, h1, h2⟩
  let g : UJ ε := ⟨u, hUJ⟩
  exact ⟨⟨g, hK⟩, rfl⟩

lemma inner_op_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (u v : T.V) :
    inner ℂ (T.op k u) (T.op k v) = inner ℂ u v := by
  have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have : star (T.op k) (T.op k v) = v := by
    have h : (star (T.op k) * T.op k) v = v := by rw [hu]; rfl
    exact h
  rw [this]

lemma wt_eq (hR : RhoTorus) (hT : TorW) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {m : ℕ}
    {η : Fin n → ℝ} {a : AS T m}
    (ha : ∀ (θ : Fin n → ℝ) (k : KG ε), toMK k = tor θ →
      rhoA T m k a = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a)
    (x : Wd n m) (hx : inner ℂ T.w (a x) ≠ 0) (c : Fin n) : wtL c (ofW x) = η c - Λ c := by
  by_contra hne
  set v : ℝ := η c - Λ c - wtL c (ofW x) with hv
  have hv0 : v ≠ 0 := fun h => hne (by rw [hv] at h; linarith)
  set t : ℝ := Real.pi / v with ht
  have htv : t * v = Real.pi := by rw [ht]; field_simp
  set θ : Fin n → ℝ := Pi.single c t with hθ
  obtain ⟨k, hk⟩ := exists_tor ε θ
  have h1 : rhoA T m k a x = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a x := by
    rw [ha θ k hk]; rfl
  have h2 := hR n ε Λ T m θ k hk a x
  have h3 := hT n ε Λ T θ k hk
  have hS : (∑ i, (θ (x.2 i).1 - θ (x.2 i).2) : ℝ) = t * wtL c (ofW x) := by
    unfold wtL ofW
    rw [List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hθ, Pi.single_apply, Function.comp_apply]
    split_ifs <;> simp
  have hE : (∑ a, η a * θ a : ℝ) = t * η c := by
    simp [hθ, Pi.single_apply, mul_comm]
  have hL : (∑ a, Λ a * θ a : ℝ) = t * Λ c := by
    simp [hθ, Pi.single_apply, mul_comm]
  rw [hS] at h2
  rw [hE] at h1
  rw [hL] at h3
  set E1 : ℂ := Complex.exp (((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I) with hE1
  set E2 : ℂ := Complex.exp (((t * η c : ℝ) : ℂ) * Complex.I) with hE2
  set E3 : ℂ := Complex.exp (((t * Λ c : ℝ) : ℂ) * Complex.I) with hE3
  have h4 : E1 • T.op k (a x) = E2 • a x := by rw [← h2, h1]
  have h5 : E1 * inner ℂ T.w (a x) = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
    calc E1 * inner ℂ T.w (a x) = E1 * inner ℂ (T.op k T.w) (T.op k (a x)) := by rw [inner_op_op]
      _ = inner ℂ (T.op k T.w) (E1 • T.op k (a x)) := by rw [inner_smul_right]
      _ = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
        rw [h4, h3, inner_smul_right, inner_smul_left]; ring
  have h6 : E1 = (starRingEnd ℂ) E3 * E2 := mul_right_cancel₀ hx h5
  have h7 : (starRingEnd ℂ) E3 * E3 = 1 := by
    rw [hE3, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have h8 : E1 * E3 = E2 := by
    rw [h6]
    calc (starRingEnd ℂ) E3 * E2 * E3 = ((starRingEnd ℂ) E3 * E3) * E2 := by ring
      _ = E2 := by rw [h7, one_mul]
  have h9 : E2 = -(E1 * E3) := by
    have : ((t * η c : ℝ) : ℂ) * Complex.I = ((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I +
        ((t * Λ c : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
      rw [← htv, hv]
      push_cast
      ring
    rw [hE2, this, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h10 : E1 * E3 ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  apply h10
  have h11 : E1 * E3 = -(E1 * E3) := by rw [← h9, h8]
  have h12 : (2 : ℂ) * (E1 * E3) = 0 := by linear_combination h11
  simpa using h12

theorem betaWeight : HolFacts → RhoTorus → TorW → BetaWeight := by
  intro H hR hT n ε Λ T μ m η a ha
  refine ⟨?_, ?_⟩
  · unfold betaF
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ofW x, rfl⟩)
  · intro c
    unfold betaF
    rw [lop_sum _ _ _ fun x => Submodule.smul_mem _ _ (lw_mem H μ (ofW x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lop_smul _ _ (lw_mem H μ (ofW x)), lop_lw H]
    by_cases hx : inner ℂ T.w (a x) = 0
    · simp [hx]
    · rw [wt_eq hR hT T ha x hx c, smul_comm]
      congr 2
      push_cast
      ring

end GlobalTheory.CompanionTheory.TorusSymbol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
section
open Polynomial

namespace GlobalTheory.CompanionTheory.LinRec

noncomputable def shift : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun u := fun i => u (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shift_apply (u : ℕ → ℂ) (i : ℕ) : shift u i = u (i + 1) := rfl

lemma shift_pow (j : ℕ) (u : ℕ → ℂ) (i : ℕ) : (shift ^ j) u i = u (i + j) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shift_apply]
    rfl

lemma aeval_shift (p : ℂ[X]) (u : ℕ → ℂ) (i : ℕ) :
    aeval shift p u i = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shift_pow, smul_eq_mul]

lemma aeval_diff (q : ℂ[X]) (z : ℂ) (u : ℕ → ℂ) (hu : aeval shift ((X - C z) * q) u = 0) :
    aeval shift q (fun i => u (i + 1) - z * u i) = 0 := by
  have h : aeval shift (X - C z : ℂ[X]) u = fun i => u (i + 1) - z * u i := by
    funext i
    simp [aeval_X, aeval_C, shift_apply, Module.algebraMap_end_apply]
  rw [← h, ← Module.End.mul_apply, ← map_mul, mul_comm]
  exact hu

lemma geom_step (z : ℂ) (κ c M : ℝ) (hz : ‖z‖ < Real.exp κ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (u : ℕ → ℂ) (h0 : ‖u 0‖ ≤ M)
    (hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤ c * Real.exp (κ * i) * M) (i : ℕ) :
    ‖u i‖ ≤ (1 + c / (Real.exp κ - ‖z‖)) * Real.exp (κ * i) * M := by
  have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hz
  set D : ℝ := 1 + c / (Real.exp κ - ‖z‖) with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ c / (Real.exp κ - ‖z‖) := div_nonneg hc hpos.le
    linarith
  have hD : ‖z‖ * D + c ≤ D * Real.exp κ := by
    have : D * (Real.exp κ - ‖z‖) = (Real.exp κ - ‖z‖) + c := by
      rw [hDdef]; field_simp
    nlinarith
  induction i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    nlinarith
  | succ i ih =>
    have hE : 0 < Real.exp (κ * i) := Real.exp_pos _
    have h1 : ‖u (i + 1)‖ ≤ ‖z‖ * ‖u i‖ + ‖u (i + 1) - z * u i‖ := by
      have : u (i + 1) = z * u i + (u (i + 1) - z * u i) := by ring
      calc ‖u (i + 1)‖ = ‖z * u i + (u (i + 1) - z * u i)‖ := by rw [← this]
        _ ≤ ‖z * u i‖ + ‖u (i + 1) - z * u i‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    have hexp : Real.exp (κ * ((i + 1 : ℕ) : ℝ)) = Real.exp (κ * i) * Real.exp κ := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc ‖u (i + 1)‖ ≤ ‖z‖ * (D * Real.exp (κ * i) * M) + c * Real.exp (κ * i) * M :=
          h1.trans (add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _)) (hv i))
      _ = (‖z‖ * D + c) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (D * Real.exp κ) * (Real.exp (κ * i) * M) := mul_le_mul_of_nonneg_right hD hEM
      _ = _ := by ring

theorem bound_of_natDegree (n : ℕ) : ∀ (p : ℂ[X]) (κ : ℝ), p.Monic → p.natDegree = n →
    (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < n, ‖u j‖ ≤ M) → 0 ≤ M → ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  induction n with
  | zero =>
    intro p κ hp hd _
    refine ⟨0, le_rfl, fun u M hu _ _ i => ?_⟩
    have hp1 : p = 1 := by
      have h1 : p.coeff 0 = 1 := by
        have h2 := hp.coeff_natDegree
        rwa [hd] at h2
      rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
    subst hp1
    have hu0 : u = 0 := by simpa using hu
    simp [hu0]
  | succ n ih =>
    intro p κ hp hd hr
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      have : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
      omega)
    have hzlt := hr z hz
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : q.natDegree = n := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C] at hd
      omega
    obtain ⟨C', hC', hB⟩ := ih q κ hq hqd fun w hw => hr w (by
      have hw' : eval w q = 0 := hw
      simp [IsRoot, hw'])
    have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hzlt
    have hc : 0 ≤ C' * (1 + ‖z‖) := by positivity
    refine ⟨1 + C' * (1 + ‖z‖) / (Real.exp κ - ‖z‖), by positivity, fun u M hu hM hM0 i => ?_⟩
    refine geom_step z κ _ M hzlt hc hM0 u (hM 0 (Nat.succ_pos n)) (fun i => ?_) i
    have hb := hB (fun i => u (i + 1) - z * u i) ((1 + ‖z‖) * M) (aeval_diff q z u hu)
      (fun j hj => ?_) (by positivity) i
    · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + ‖z‖) * M) := hb
        _ = _ := by ring
    · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
        _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
        _ ≤ M + ‖z‖ * M := add_le_add (hM _ (by omega))
            (mul_le_mul_of_nonneg_left (hM _ (by omega)) (norm_nonneg _))
        _ = _ := by ring

theorem recBound : PositivityTheory.Rg.Rs.An.RecBound := by
  intro p κ hp hr
  obtain ⟨C, hC, h⟩ := bound_of_natDegree _ p κ hp rfl hr
  refine ⟨C, hC, fun u M hu hM hM0 i => h u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CKContinuous
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cont_triple {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Group B]
    [IsTopologicalGroup B] (F : A × B → ℝ) (c : B → ℝ) (hF : Continuous F) (hc : Continuous c) :
    Continuous fun z : A × (B × B) => F (z.1, z.2.1) * F (z.1, z.2.2) * c (z.2.1⁻¹ * z.2.2) ^ 2 := by
  have h1 : Continuous fun z : A × (B × B) => F (z.1, z.2.1) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun z : A × (B × B) => F (z.1, z.2.2) :=
    hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun z : A × (B × B) => c (z.2.1⁻¹ * z.2.2) :=
    hc.comp (((continuous_fst.comp continuous_snd).inv).mul (continuous_snd.comp continuous_snd))
  exact (h1.mul h2).mul (h3.pow 2)

theorem cont_slice {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A × B → ℝ)
    (hf : Continuous f) (a : A) : Continuous fun b : B => f (a, b) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous (cK T) := by
  have h : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have h2 : Continuous fun k : KG ε => ‖⟪T.w, T.op k T.w⟫_ℂ‖ := (continuous_const.inner h).norm
  exact h2

theorem hI_continuous (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Continuous fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  cont_triple (fun z : UJ ε × KG ε => phiK μ (pP (toM z.1)) z.2) (cK T) (hC n ε μ) (cK_continuous T)

theorem hI_measurable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Measurable fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  (hI_continuous hC T μ).measurable

theorem hI_nonneg (hMul : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    0 ≤ hI T μ x p := by
  have a := (hMul n ε μ 0 x hx p.1).1
  have b := (hMul n ε μ 0 x hx p.2).1
  exact mul_nonneg (mul_pos a b).le (sq_nonneg _)

theorem hI_integrable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) (g : UJ ε) :
    Integrable (fun p : KG ε × KG ε => hI T μ (pP (toM g)) p) ((dk ε).prod (dk ε)) := by
  haveI : IsProbabilityMeasure (dk ε) := (dk_props ε).1
  have hc : Continuous fun p : KG ε × KG ε => hI T μ (pP (toM g)) p :=
    cont_slice (fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2)
      (hI_continuous hC T μ) g
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem hsInt : HsPs → HsPol → PhiMul → PhiCont → HsInt := by
  intro hPs hPol hMul hC n ε Λ T μ
  refine ⟨hI_measurable hC T μ, fun g => ?_⟩
  obtain ⟨⟨X, hX, hE⟩, hN⟩ := hPol n ε (toM g) g.2
  have hpd : (pP (toM g)).PosDef := by
    rw [hE]
    exact exp_noncompactPart_posDef hX
  rw [hN Λ T μ, hPs n ε Λ T μ _ hpd, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (hI_integrable hC T μ g)
      (Filter.Eventually.of_forall (hI_nonneg hMul T μ hpd))]

end GlobalTheory.CompanionTheory.RgFd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegers
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCOK

theorem exists_uniform_mem_sub : ∀ (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K),
      Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K
  choose c hc using _root_.GlobalTheory.CompanionTheory.LatOKElem.ok_mem_sub l K
  refine ⟨2 * s.sup c, fun k a => ?_⟩
  obtain ⟨d, hd⟩ := hs a
  have h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) *
      Lat.kP l K i := by
    have h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l)) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, hd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [map_mul]
  exact Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i))
    (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))

end GlobalTheory.CompanionTheory.LatCOK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphismStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g, IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  first | exact @GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | exact GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism <;> assumption)
end

