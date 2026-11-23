module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.SpecSum
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem specSum_op {d : ℕ} (a Y : Eu d →L[ℂ] Eu d) (y : ℝ → ℂ) (sp : Finset ℝ) (ha : 0 ≤ a) (hc : Commute a Y)
    (hsp : ∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ) ≠ ⊥)
    (hY : ∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ), Y v = y x • v) (w : Eu d) :
    a (Y w) = ∑ x ∈ sp, ((x : ℂ) * y x) • eigP a x w := by
  have hpos : a.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).1 ha
  have hsym : (a : Eu d →ₗ[ℂ] Eu d).IsSymmetric := hpos.isSymmetric
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hsym.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hw : w ∈ (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) := htop ▸ Submodule.mem_top
  induction hw using Submodule.iSup_induction' with
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add (f := _), hu, hv, smul_add, Finset.sum_add_distrib]
  | mem μ v hv =>
    by_cases h0 : v = 0
    · subst h0; simp
    have hav : a v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    have hev : Module.End.HasEigenvalue (a : Eu d →ₗ[ℂ] Eu d) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, h0⟩
    have hre : (starRingEnd ℂ) μ = μ := hsym.conj_eigenvalue_eq_self hev
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, μ = r := ⟨μ.re, (Complex.conj_eq_iff_re.1 hre).symm⟩
    have hr : 0 ≤ r := by
      have h1 := hpos.re_inner_nonneg_right v
      rw [hav, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
      have h2 : 0 < ‖v‖ ^ 2 := by positivity
      have h3 : RCLike.re ((r : ℂ) * ((‖v‖ : ℂ)) ^ 2) = r * ‖v‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; simp only [RCLike.re_to_complex, Complex.ofReal_re]
      have h4 : 0 ≤ r * ‖v‖ ^ 2 := by rw [← h3]; exact h1
      exact nonneg_of_mul_nonneg_left h4 h2
    have hne : ∀ x : ℝ, x ≠ r → eigP a x v = 0 := by
      intro x hx
      unfold eigP
      rw [Submodule.starProjection_apply_eq_zero_iff]
      intro u hu
      have hx' : (x : ℂ) ≠ r := by exact_mod_cast hx
      exact hsym.orthogonalFamily_eigenspaces hx' ⟨u, hu⟩ ⟨v, hv⟩
    have heq : eigP a r v = v := Submodule.starProjection_eq_self_iff.2 hv
    rcases hr.eq_or_lt with h | h
    · have h1 : a (Y v) = Y (a v) := congrArg (fun T : Eu d →L[ℂ] Eu d => T v) hc.eq
      rw [h1, hav, ← h]
      simp only [Complex.ofReal_zero, zero_smul, map_zero]
      refine (Finset.sum_eq_zero fun x hx => ?_).symm
      rw [hne x (h ▸ ((hsp x).1 hx).1.ne'), smul_zero]
    · have hm : r ∈ sp := (hsp r).2 ⟨h, hev⟩
      rw [Finset.sum_eq_single_of_mem r hm fun x _ hx => by rw [hne x hx, smul_zero], heq, hY r h v hv, map_smul, hav,
        smul_smul, mul_comm]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.specSum :
    ∀ {d d' : ℕ} (a Y Z : Eu d' →L[ℂ] Eu d') (N : Eu d' →ₗ[ℂ] Eu d) (s : Eu d →ₗ[ℂ] Eu d') (y : ℝ → ℂ) (sp : Finset ℝ), 0 ≤ a → Commute a Y →
      (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ) ≠ ⊥) →
      (∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ), Y v = y x • v) →
      LinearMap.trace ℂ (Eu d) (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
        ∑ x ∈ sp, x * y x * LinearMap.trace ℂ (Eu d) (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
  intro d d' a Y Z N s y sp ha hc hsp hY
  have key : (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
      ∑ x ∈ sp, ((x : ℂ) * y x) • (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply]
    change N (a (Y (Z (s w)))) = ∑ x ∈ sp, ((x : ℂ) * y x) • N (eigP a x (Z (s w)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [specSum_op a Y y sp ha hc hsp hY, map_sum]
    simp only [map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [map_smul, smul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.TruncSB
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d p = ∑ α ∈ p.support,
      monomial (Finsupp.single none (d - α.degree) + α.mapDomain some) (p.coeff α) := by
  unfold homog
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

private theorem deg_le {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : α.degree ≤ d := by
  have := (le_totalDegree hα).trans h
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

private theorem deg_exp {ι : Type} {d : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ d) :
    (Finsupp.single none (d - α.degree) + α.mapDomain some : Option ι →₀ ℕ).degree = d := by
  rw [map_add (f := _), Finsupp.degree_single, Finsupp.degree_mapDomain]
  omega

private theorem trunc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (d : ℕ)
    (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) (s : Finset ((Pl K × Fin n) →₀ ℕ))
    (h : ∀ k, (G k).support ⊆ s) :
    trunc d G = ∑ β ∈ s, monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)) := by
  unfold trunc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_subset (h k) fun β _ hβ => ?_
  rw [notMem_support_iff.mp hβ]
  simp [homog]

private theorem mon_norm {σ : Type} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial σ ℂ →+* (H →L[ℂ] H)) {D : ℝ} (hD : 1 ≤ D) (hX : ∀ i, ‖ψ (X i)‖ ≤ D) (m : σ →₀ ℕ) :
    ‖ψ (monomial m 1)‖ ≤ D ^ m.degree := by
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  induction m using Finsupp.induction_linear with
  | zero => simpa using h1
  | add a b ha hb =>
    have : (monomial (a + b) 1 : MvPolynomial σ ℂ) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, map_add (f := _), pow_add]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  | single i e =>
    rw [← X_pow_eq_monomial, map_pow, Finsupp.degree_single]
    induction e with
    | zero => simpa using h1
    | succ e ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih (hX i) (norm_nonneg _) (by positivity))

private theorem homog_norm {ι : Type} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial (Option ι) ℂ →+* (H →L[ℂ] H)) (hψ : ∀ c : ℂ, ψ (C c) = c • 1) {D : ℝ} (hD : 1 ≤ D)
    (hX : ∀ i, ‖ψ (X i)‖ ≤ D) (d : ℕ) (p : MvPolynomial ι ℂ) (hp : p.totalDegree ≤ d) :
    ‖ψ (homog d p)‖ ≤ l1 p * D ^ d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homog_eq, map_sum, l1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
  rw [← mul_one (p.coeff α), ← C_mul_monomial, map_mul, hψ, smul_mul_assoc, one_mul, norm_smul, mul_one]
  refine mul_le_mul_of_nonneg_left ((mon_norm ψ hD hX _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [deg_exp (deg_le hp hα)]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncSB :
    ∀ {K : Type} [Field K] [NumberField K] {n d : ℕ} (evz : ℂ → PR K n →+* (Eu d →L[ℂ] Eu d)), (∀ z (c : ℂ), evz z (C (C c)) = c • 1) → ∀ (S : Set (Pl K)), (∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ S) → ∃ M, SB (fun z => evz z R) M) →
      ∀ (Φ : KF (Ix K n) (Pl K × Fin n)) G, admitted S Φ → IsGen Φ G → ∃ M : ℝ, ∀ k, SB (fun z => evz z (trunc k G)) (M ^ (k + 1)) := by
  intro K _ _ n d₀ evz hev S hS Φ G hΦ hG
  classical
  obtain ⟨K₀, G₀, hG₀⟩ := UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (Pl K × Fin n) n Φ (by
    intro w
    convert hΦ.1 w)
  have hGG : G = G₀ := by
    funext k
    refine map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_
    exact (hG k).trans (hG₀ k).1.symm
  subst hGG
  have hs : ∀ k, (G k).support ⊆ Φ.support := fun k => (hG₀ k).2.1
  have hdeg : ∀ d β, ∀ k ∈ Finset.range (d + 1), ((G k).coeff β).totalDegree ≤ d := fun d β k hk =>
    ((hG₀ k).2.2 β).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hT := fun d => trunc_eq d G Φ.support hs
  choose MX hMX using fun o : Option (Ix K n) => hS (C (X o)) (by simp)
  have hmon : ∀ β : (Pl K × Fin n) →₀ ℕ, ∃ M, β ∈ Φ.support → SB (fun z => evz z (monomial β 1)) M := by
    intro β
    by_cases hβ : β ∈ Φ.support
    · obtain ⟨M, hM⟩ := hS (monomial β 1) (by
        intro y hy
        rw [vars_monomial one_ne_zero] at hy
        exact hΦ.2 y ((mem_vars_iff_mem_support y).mpr ⟨β, hβ, hy⟩))
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose Mβ hMβ using hmon
  set D : ℝ := 1 + ∑ o, |MX o| with hDdef
  have h0 : 0 ≤ ∑ o, |MX o| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : 1 ≤ D := by linarith
  set A : ℝ := ∑ β ∈ Φ.support, |Mβ β| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set E : ℝ := |K₀| + 1 with hE
  have hE1 : 1 ≤ E := by have := abs_nonneg K₀; linarith
  refine ⟨(A + 1) * 2 * E * D, fun d z hz => ?_⟩
  have hb := homog_norm ((evz z).comp C) (hev z) hD (fun o => by
    have h1 := hMX o z hz
    have h2 := Finset.single_le_sum (f := fun o => |MX o|) (fun _ _ => abs_nonneg _) (Finset.mem_univ o)
    have h3 := le_abs_self (MX o)
    exact h1.trans (by linarith))
  have hm : ∀ β ∈ Φ.support, ‖evz z (monomial β 1)‖ ≤ |Mβ β| := fun β hβ =>
    (hMβ β hβ z hz).trans (le_abs_self _)
  show ‖evz z (trunc d G)‖ ≤ _
  generalize evz z = ev at hb hm ⊢
  have h1 : ∀ β, ‖ev (C (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
      ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) := by
    intro β
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ k ∈ Finset.range (d + 1), ‖ev (C (homog d ((G k).coeff β)))‖ ≤ E ^ (d + 1) * D ^ (d + 1) := by
      intro k hk
      refine (hb d _ (hdeg d β k hk)).trans (mul_le_mul ?_ (pow_le_pow_right₀ hD (Nat.le_succ d))
        (by positivity) (by positivity))
      refine ((hG₀ k).2.2 β).2.trans ?_
      have h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1) :=
        (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
      have h4 : E ^ (k + 1) ≤ E ^ (d + 1) :=
        pow_le_pow_right₀ hE1 (by have := Finset.mem_range.mp hk; omega)
      have h5 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
      calc K₀ ^ (k + 1) / k.factorial ≤ E ^ (d + 1) / k.factorial := by gcongr; linarith
        _ ≤ E ^ (d + 1) := div_le_self (by positivity) h5
    refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
    rw [Finset.card_range, nsmul_eq_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (Nat.lt_two_pow_self (n := d + 1)).le
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have h6 : ∀ β ∈ Φ.support, ‖ev (monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
      ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * |Mβ β| := by
    intro β hβ
    rw [← mul_one (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)), ← C_mul_monomial, map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (h1 β) (hm β hβ) (norm_nonneg _) (by positivity))
  refine (Finset.sum_le_sum h6).trans ?_
  rw [← Finset.mul_sum, ← hA, mul_pow, mul_pow, mul_pow]
  have h7 : A ≤ (A + 1) ^ (d + 1) :=
    (by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
  calc 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * A ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * (A + 1) ^ (d + 1) := by
        gcongr
    _ = _ := by ring
end

