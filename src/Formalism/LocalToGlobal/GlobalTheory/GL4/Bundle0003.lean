module

public import Formalism.LocalToGlobal.Columns.Bundle0022
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.FockNExtCNu
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.L2.DIV

section Mono

variable {ι : Type} [Fintype ι] {n : ℕ}

private theorem map_algebraMap_rat_complex_hw {N : ℕ} (ν : Fin N → ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) ν) = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν := by
  unfold Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]

theorem fockN_ext_cNu (lam : DomWeight n) :
    fockN (extremal ℂ n lam) = cNu lam.natW * ∏ s, ((lam.natW s).factorial : ℝ) := by
  have hprod : (∏ s, ((lam.natW s).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold extremal cNu
  rw [← map_algebraMap_rat_complex_hw, Formalism.L2.Col.fock_norm_rational_eq, div_mul_cancel₀ _ hprod]

theorem cNu_natW_pos (lam : DomWeight n) : 0 < cNu lam.natW := by
  have hnn : (0 : ℚ) ≤ Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) := by
    unfold Formalism.GradedWeylDivisibility.fockQ
    exact Finset.sum_nonneg fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)
  have hpos : (0 : ℚ) < Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) :=
    lt_of_le_of_ne hnn (Formalism.L2.DIV.we_hw_norm_ne le_rfl lam.natW).symm
  unfold cNu
  apply div_pos
  · exact_mod_cast hpos
  · exact Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _

def monCnu (lam : ι → DomWeight n) : ℝ := ((n : ℝ) ^ (∑ τ, dW (lam τ)) * ∏ τ, cNu (lam τ).natW)⁻¹

private theorem sub_one_mul_padicValNat_factorial_le' {n : ℕ} (g : Fin n → ℕ) :
    (∑ a, g a).factorial ≤ n ^ (∑ a, g a) * ∏ a, (g a).factorial := by
  classical
  have hmul := Nat.multinomial_spec Finset.univ g
  have hle : Nat.multinomial Finset.univ g ≤ n ^ (∑ a, g a) := by
    have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℕ)) (∑ a, g a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow,
      Finset.prod_const_one, Nat.cast_id] at h
    rw [h]
    apply Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)
    rw [Finset.mem_piAntidiag]
    exact ⟨rfl, fun i _ => Finset.mem_univ i⟩
  calc (∑ a, g a).factorial = (∏ a, (g a).factorial) * Nat.multinomial Finset.univ g := hmul.symm
    _ ≤ (∏ a, (g a).factorial) * n ^ (∑ a, g a) := Nat.mul_le_mul_left _ hle
    _ = _ := mul_comm _ _

theorem monW_ge_cNu (lam : ι → DomWeight n) (m : MonI lam) : monCnu lam ≤ monW lam m := by
  classical
  have hC : 0 < ∏ τ, cNu (lam τ).natW := Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)
  have hF : (0 : ℝ) < ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _
  have hND : (0 : ℝ) < (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  have hext : extremalFockNormProduct lam = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := by
    unfold extremalFockNormProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => fockN_ext_cNu (lam τ)
  have hcombN : ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ Formalism.L2.DIV.mfact m.1 * n ^ (∑ τ, dW (lam τ)) := by
    have hmf : Formalism.L2.DIV.mfact m.1 = ∏ τ, ∏ s, ∏ a, (m.1 (τ, a, s)).factorial := by
      unfold Formalism.L2.DIV.mfact
      rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
        rw [show m.1 k = 0 from by simpa using hk, Nat.factorial_zero])]
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Fintype.prod_prod_type, Finset.prod_comm]
    have hpow : n ^ (∑ τ, dW (lam τ)) = ∏ τ, ∏ s, n ^ ((lam τ).natW s) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      unfold dW
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [hmf, hpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
    intro τ _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
    intro s _
    have h := sub_one_mul_padicValNat_factorial_le' (fun a => m.1 (τ, a, s))
    rw [m.2 τ s] at h
    exact h.trans (le_of_eq (mul_comm _ _))
  have hcomb : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤
      (Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    exact_mod_cast hcombN
  unfold monCnu monW
  rw [hext, inv_eq_one_div, div_le_div_iff₀ (mul_pos hND hC) (mul_pos hC hF)]
  calc 1 * ((∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ))
      = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := one_mul _
    _ ≤ (∏ τ, cNu (lam τ).natW) * ((Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ))) :=
      mul_le_mul_of_nonneg_left hcomb hC.le
    _ = _ := by ring

theorem monCnu_pos (lam : ι → DomWeight n) : 0 < monCnu lam := by
  unfold monCnu
  apply inv_pos.mpr
  apply mul_pos
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  · exact Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)

theorem log_monCnu (lam : ι → DomWeight n) (hn : 0 < n) :
    -Real.log (monCnu lam) = ∑ τ, ((dW (lam τ) : ℝ) * Real.log n + Real.log (cNu (lam τ).natW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ∀ τ, cNu (lam τ).natW ≠ 0 := fun τ => (cNu_natW_pos (lam τ)).ne'
  unfold monCnu
  rw [Real.log_inv, neg_neg, Real.log_mul (pow_ne_zero _ hn'.ne') (Finset.prod_ne_zero_iff.mpr fun τ _ => hc τ),
    Real.log_pow, Real.log_prod (fun τ _ => hc τ), Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]

end Mono

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.MuMaxLeMon
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms Formalism.L2.Col

section Gen

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem muMax_le_mon {V κ : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype κ] [DecidableEq κ]
    (b : Basis κ K V) (X : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (N : Submodule (𝓞 K) V) (hN : N.FG) (φ : V →ₗ[K] (MonI lam → K)) (hinj : Set.InjOn φ N)
    (hne : N.map (φ.restrictScalars (𝓞 K)) ≠ ⊥)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0)
    (hint : ∀ x ∈ N, ∀ m, φ x m ∈ (I : Submodule (𝓞 K) K))
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v)
    (hnorm : ∀ v x, normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (φ x) ^ 2 ≤ B v * normAt b X v x ^ 2)
    (c0 : ℝ) (hc0 : 0 < c0) (hc : ∀ m, c0 ≤ monW lam m) :
    muMaxDef b X N ≤ -Real.log c0 - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
      + (1 / (nPl K : ℝ)) * ∑ v, Real.log (B v) := by
  have hX' : ∀ v : InfinitePlace K, IsUnit ((fun _ : InfinitePlace K => (monD lam)⁻¹) v).det :=
    fun v => (Matrix.isUnit_nonsing_inv_det_iff).mpr (monD_det lam)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hne
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    simp
  obtain ⟨L0, hL0⟩ : ∃ L0 : Submodule (𝓞 K) (MonI lam → K),
      L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) := ⟨_, rfl⟩
  have hmemL0 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) ∈ L0 := fun m => by
    rw [hL0]
    exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem (Finset.mem_univ m)
      (Submodule.mem_span_singleton_self _))
  have hmapT : N.map (φ.restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have hdec : φ x = ∑ m, (φ x m) • (Pi.single m (1 : K) : MonI lam → K) := by
      ext m'
      simp [Finset.sum_apply, Pi.single_apply]
    show φ x ∈ _
    rw [hdec]
    exact Submodule.sum_mem _ fun m _ => Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul (hint x hx m) (hmemL0 m)
  have horth : ∀ s t : MonI lam, s ≠ t → Formalism.BranchingDeterminantCap.OrthAt (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) (𝓞 K ∙ (Pi.single s (1 : K) : MonI lam → K))
      (𝓞 K ∙ (Pi.single t (1 : K) : MonI lam → K)) := by
    intro s t hst v x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨r', rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [majAt, monH_fcoord]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m = s
    · subst hm
      simp [Pi.single_apply, hst]
    · simp [Pi.single_apply, hm]
  have hline : ∀ m, muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹)
      (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) ≤ -Real.log c0 := by
    intro m
    refine max_slope_line_neg_log _ _ hX' _ ?_ c0 hc0 fun v => ?_
    · simp
    · rw [monH_norm, Finset.sum_eq_single m (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simpa using hc m
  have hmain := Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX'
    (fun m => 𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) (fun m => Submodule.fg_span_singleton _) horth
    Finset.univ
  rw [← hL0] at hmain
  have hL0ne : L0 ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    have h1 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) = 0 := fun m => by
      have := hmemL0 m
      rwa [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    funext m
    exact absurd (h1 m) (by simp)
  have hL0mu : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) L0 ≤ -Real.log c0 := by
    have h2 := hmain.2.2.2 ((-Real.log c0 - slopeNormalisingConstant K) / 2) (fun m _ _ => by
      have := hline m
      rw [frameB_muMaxDef] at this
      linarith) hL0ne
    rw [frameB_muMaxDef]
    linarith
  have hT := Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_fractional_le (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX' hmain.1 hL0ne hI0
  have hS := ((Formalism.HN.slopeIneqMean K V κ (MonI lam → K) (MonI lam) b X (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' φ N hN hne).2 (idealSmul (I : Submodule (𝓞 K) K) L0)
    (Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_fg I hmain.1) hmapT).2 hinj
  have hht : htMap b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) φ ≤
      1 / (nPl K : ℝ) * ∑ v, Real.log (B v) := by
    unfold htMap
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro v _
    have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' v φ hφ0
    have hle : opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ≤ √(B v) := by
      apply Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X _ _ hX φ v _ (Real.sqrt_nonneg _)
      intro f
      have h0 : 0 ≤ normAt (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v (φ f) :=
        Real.sqrt_nonneg _
      have h1 : 0 ≤ normAt b X v f := Real.sqrt_nonneg _
      have := Real.sqrt_le_sqrt (hnorm v f)
      rwa [Real.sqrt_sq h0, Real.sqrt_mul (hB v).le, Real.sqrt_sq h1] at this
    apply Real.log_le_log (by positivity)
    calc opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ^ 2
        ≤ √(B v) ^ 2 := pow_le_pow_left₀ hpos.le hle 2
      _ = B v := Real.sq_sqrt (hB v).le
  linarith [hS, hT, hL0mu, hht]

end Gen

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

