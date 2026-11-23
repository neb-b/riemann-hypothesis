module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCubeIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoostLowerBounds

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientQuantitative
section
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cusp_coefficient_bound_of_unipotent_lattice_lift (hL2 : UnipotentLatticeLift (E := E)) : CuspCoefficientBound (E := E) := by
  intro r X u hu huΛ la P hP hchi ν
  have hiso : X.IsIso (u 0) := ⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩
  refine ⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩
  · intro x hx b hb
    have hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) =
        rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b := fun s => by
      funext τ
      show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) =
        (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ
      rw [Matrix.mul_assoc]
    have hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) =
        bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl]
      exact hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb
    unfold Data.fj
    split_ifs with h1 h2
    · simp_rw [hPb, mul_assoc]
      rw [integral_const_mul]
      ring
    · simp
    · simp
  · intro b hb x hx
    let a0 : X.Ψ → Fin 2 → ℂ := fun _ => ![1, 0]
    have hemb : X.embV (u 0) = X.uvec u a0 := by
      funext τ
      simp [Data.uvec, a0, Fin.sum_univ_two, Data.embV]
    have hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y := fun s y => by
      rw [show X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]
    have hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) =
        X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]
    have hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) =
        P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hZ]
      exact (hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _
        (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1
    unfold Data.fj
    simp_rw [hPZ]

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory FourierCoefficientMatrices FourierCubeVolume FourierCubeIntegral

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem fourier_coefficients_of_vector_group (hL1 : UnipotentVectorGroup (E := E)) : FourierCoefficientProperties (E := E) := by
  intro r X u g hiso hg la G hGd hB hper χ
  classical
  obtain ⟨hadd, hH⟩ := hL1 r X u hiso
  have hunit : ∀ b, IsHermFam b → X.IsUnitaryC (X.zmat u b) := fun b hb => (hH b hb).1
  have hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := fun b hb => (hH b hb).2.2.2.1
  have hex : ∃ ω, X.IsLZBasis g ω := FixedPointImaginarySpan.exists_basis X g hg
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = hex.choose := ⟨_, rfl⟩
  have hω : X.IsLZBasis g ω := hωdef ▸ hex.choose_spec
  have hfz : ∀ ψ x, X.fz u g ψ G x =
      if IsHermFam ψ ∧ X.IsFreqZ g ψ then Ich X u ω G ψ x else 0 := by
    intro ψ x
    unfold Data.fz
    rw [dite_eq_left hex, ← hωdef]
    rfl
  have hsum : ∀ x ∈ X.dom, Summable (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g ψ G x‖) →
      HasSum (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) (G x) := by
    intro x hx hs
    have hωh := herm_ω hω
    have hli := hω.2.2
    obtain ⟨c, hc⟩ : ∃ c : (Fin (4 * Fintype.card X.Ψ) → ℤ) → X.Ψ → Fin 2 → Fin 2 → ℂ,
        c = fun m => chiOf ω hωh hli rfl fun j => (m j : ℝ) := ⟨_, rfl⟩
    have hcm : ∀ m, c m = chiOf ω hωh hli rfl fun j => (m j : ℝ) := fun m => by rw [hc]
    have hc_inj : Function.Injective c := by
      intro m m' h
      rw [hcm, hcm] at h
      have h' := chiOf_inj ω hωh hli rfl h
      funext j
      exact_mod_cast congrFun h' j
    have hcfreq : ∀ m, IsHermFam (c m) ∧ X.IsFreqZ g (c m) := by
      intro m
      refine ⟨by rw [hcm]; exact chiOf_herm ω hωh hli rfl _, ?_⟩
      intro b hb
      obtain ⟨n, hn, -⟩ := hω.2.1 b hb
      refine ⟨∑ j, n j * m j, ?_⟩
      have hb' : b = ∑ j, ((n j : ℝ) : ℂ) • ω j := by
        rw [hn]
        simp only [Complex.ofReal_intCast]
      show 2 * pr (c m) b = _
      rw [hb', pr_sum, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      have hp : 2 * pr (c m) (ω j) = (m j : ℝ) := by
        rw [hcm]
        exact chiOf_pair ω hωh hli rfl _ j
      calc 2 * ((n j : ℝ) * pr (c m) (ω j)) = (n j : ℝ) * (2 * pr (c m) (ω j)) := by ring
        _ = (n j : ℝ) * (m j : ℝ) := by rw [hp]
    obtain ⟨D, hD⟩ := I2.DimB.descend (fun t => G (X.Zb u (Bv ω t) x))
      (psi_cont hω hdomH hGd hx) (fun n t => psi_per hω hadd hdomH hper hx n t)
    have hcoef : ∀ m, X.fz u g (c m) G x = UnitAddTorus.mFourierCoeff D m := by
      intro m
      rw [hfz, if_pos (hcfreq m)]
      refine Ich_coeff (fun j => ?_) D hD
      show 2 * pr (c m) (ω j) = (m j : ℝ)
      rw [hcm]
      exact chiOf_pair ω hωh hli rfl _ j
    have hsupp : ∀ ψ ∉ Set.range c, X.fz u g ψ G x = 0 := by
      intro ψ hψ
      rw [hfz]
      split_ifs with h
      · exfalso
        apply hψ
        choose k hk using fun j => h.2 (ω j) (hω.1 j)
        refine ⟨k, ?_⟩
        rw [hcm]
        exact (chiOf_eq ω hωh hli rfl h.1 (m := fun j => (k j : ℝ)) hk).symm
      · rfl
    have hsm : Summable (UnitAddTorus.mFourierCoeff D) := by
      refine Summable.of_norm ((hs.comp_injective hc_inj).congr fun m => ?_)
      simp only [Function.comp, hcoef]
    have hG0 : D (I2.DimB.tproj 0) = G x := by
      rw [hD, Bv_zero, Zb_zero]
    have hF := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsm (I2.DimB.tproj 0)
    rw [hG0] at hF
    have hF' : HasSum (UnitAddTorus.mFourierCoeff D) (G x) := by
      simpa [I2.DimB.mF_tproj] using hF
    rw [← hc_inj.hasSum_iff hsupp]
    have hcomp : (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) ∘ c =
        UnitAddTorus.mFourierCoeff D := funext fun m => hcoef m
    rw [hcomp]
    exact hF'
  by_cases hχ : IsHermFam χ ∧ X.IsFreqZ g χ
  · have hfe : X.fz u g χ G = Ich X u ω G χ := funext fun x => by rw [hfz, if_pos hχ]
    have hfreq : ∀ j, ∃ k : ℤ, 2 * X.pairR χ (ω j) = k := fun j => hχ.2 (ω j) (hω.1 j)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact Ich_diff hω hdomH hGd χ
    · intro x hx b hb
      rw [hfe]
      exact Ich_rmul la hB hω hdomH χ hx hb
    · intro b hb x hx
      rw [hfe]
      exact Ich_Zb hω hadd hdomH hGd hper hfreq hb hx
    · intro x hx M hM
      rw [pnorm_eq, hfe]
      exact Ich_bound hω hunit la χ x hM
  · have hfe : X.fz u g χ G = fun _ => 0 := funext fun x => by rw [hfz, if_neg hχ]
    have hh0 : IsHermFam (0 : X.Ψ → Fin 2 → Fin 2 → ℂ) := by
      have h := th_herm (0 : X.Ψ → Fin 2 → Fin 2 → ℝ)
      rwa [th_zero] at h
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact differentiableOn_const 0
    · intro x hx b hb
      rw [hfe]
      simp
    · intro b hb x hx
      rw [hfe]
      simp
    · intro x hx M hM
      have h0 := hM 0 hh0
      rw [Zb_zero, pnorm_eq] at h0
      rw [pnorm_eq, hfe]
      simp only [norm_zero, zero_mul]
      exact (mul_nonneg (norm_nonneg _) (fac_nonneg X la x)).trans h0

theorem fourier_coefficients_holds : FourierCoefficientProperties (E := E) :=
  fourier_coefficients_of_vector_group unipotent_vector_group

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ImaginaryMajorants
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ImaginaryMajorants

open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds

variable {r : ℕ} (X : Data E r)

theorem jp_col {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.jp z τ (X.colP z τ d) = X.colP z τ d := by
  have hP : X.ppos z τ (X.colP z τ d) = X.colP z τ d := by
    have h := X.ppos_eq_of z τ (X.gramPos_det_ne hz τ) (X.colP z τ d)
      (fun a => if a = d then 1 else 0) (fun b => by
        rw [show (∑ a, (if a = d then (1 : ℂ) else 0) • col (mat z τ) (Fin.castLE X.p0_le a)) =
          X.colP z τ d by simp [Data.colP]]
        rw [sub_self, hermC_zero_left])
    rw [h]
    simp [Data.colP]
  simp only [Data.jp, hP]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem maj_imag_eq {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w = X.maj z τ (Matrix.mulVec
      (boost X τ (Data.emb τ.1 ξ) (X.jp z τ (Data.emb τ.1 ξ)) (X.maj z τ (Data.emb τ.1 ξ))
        (Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)))⁻¹) w) := by
  set e := Data.emb τ.1 ξ with he_def
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  set f := X.jp z τ e with hf_def
  set m := X.maj z τ e with hm_def
  set q := 1 + X.c τ * b τ * m with hq_def
  set σ := Real.sqrt q with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.mpr hq
  have hσ2 : σ ^ 2 = q := Real.sq_sqrt hq.le
  set T := X.flowMat ξ τ (I * (b τ : ℂ))
  have hT : ∀ v, Matrix.mulVec T v = v + (((X.c τ * b τ : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • e := by
    intro v
    rw [Data.flowMat_mulVec]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcb : X.c τ * b τ = (σ ^ 2 - 1) / m := by
    rw [hσ2, hq_def]; field_simp; ring
  set B := boost X τ e f m σ
  set B' := boost X τ e f m σ⁻¹
  set P := X.ppos z τ e with hP_def
  set γ : Fin X.p0 → ℂ := fun j => ∑ b, hermC τ.1 X.Gm e (X.colP z τ b) * (X.gramPos z τ)⁻¹ b j
  have hPsum : P = ∑ j, γ j • X.colP z τ j := rfl
  have hPef : P = (1 / 2 : ℂ) • (e + f) := by
    funext k
    simp only [hf_def, Data.jp, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, ← hP_def]
    ring
  have hPe : hermC τ.1 X.Gm P e = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hee, hfe]; push_cast; ring
  have hPf : hermC τ.1 X.Gm P f = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hef, hff]; push_cast; ring
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hcol : ∀ d, Matrix.mulVec T (X.colP z τ d) = X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d := by
    intro d
    rw [show X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d = col (mat (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ) (Fin.castLE X.p0_le d) from rfl, Data.col_flow]
    rfl
  have hzf : ∀ d, hermC τ.1 X.Gm (X.colP z τ d) f = hermC τ.1 X.Gm (X.colP z τ d) e := by
    intro d; rw [hf_def, ← X.hermC_jp_left hz, jp_col X hz τ d]

  have hi : ∀ d, Matrix.mulVec T (X.colP z τ d) = Matrix.mulVec B (X.colP z τ d) +
      (((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec B P := by
    intro d
    rw [hT, boost_mulVec, boost_mulVec, hzf, hPe, hPf, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hii : ∀ d, Matrix.mulVec B (X.colP z τ d) = Matrix.mulVec T (X.colP z τ d) -
      (((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec T P := by
    intro d
    rw [hT, hT, boost_mulVec, hzf, hPe, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a = ∑ c, L c • Matrix.mulVec B (X.colP z τ c) := by
    intro a
    refine ⟨fun j => (if j = a then 1 else 0) +
      ((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ a) e / m) * γ j, ?_⟩
    rw [← hcol, hi, hPsum, Data.mulVec_lin]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum]
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec B (X.colP z τ c) = ∑ a, K a • X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a := by
    intro c
    refine ⟨fun j => (if j = c then 1 else 0) -
      ((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ c) e / m) * γ j, ?_⟩
    rw [hii, hPsum, Data.mulVec_lin]
    simp only [hcol, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum]
  have hmt := maj_transfer X hz hy τ B B' (boost_comp X τ hm hee hff hef hfe hσ)
    (boost_isom X τ hm hee hff hef hfe hσ) H1 H2 w
  exact hmt

theorem maj_imag_flow {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    min (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ))⁻¹ *
      X.maj z τ w ≤ X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w := by
  rw [maj_imag_eq X hz ξ b hy τ hee he0 hq w]
  have hσ : 0 < Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq
  have h := boost_lower (X := X) (z := z) (τ := τ) (e := Data.emb τ.1 ξ) hz hee he0 hσ w
  rwa [Real.sq_sqrt hq.le] at h

end ImaginaryMajorants

end ReciprocityTheory.ChartRestriction.G.FD
end

