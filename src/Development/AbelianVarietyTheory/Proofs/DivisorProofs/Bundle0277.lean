module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLintegralSobolevPointwise
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem weighted_lintegral_sobolev_pointwise : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
  intro E _ _ _ _ _ μ _ m hdim
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set B : Set E := Metric.closedBall (0:E) 1 with hB
  set β : ℝ≥0∞ := μ B with hβ
  have hβ0 : β ≠ 0 := (Metric.measure_closedBall_pos μ (0:E) one_pos).ne'
  have hβtop : β ≠ ∞ := (measure_closedBall_lt_top).ne
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (m.factorial : ℝ)) * ENNReal.ofReal (1 / ((m : ℝ) + 1)) with hc
  refine ⟨2 * c / β, ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hβ0, ?_⟩
  intro F _ _ _ G hG hdec k x
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector'' ℝ x
  set S : Set E := B ∩ {v | 0 ≤ φ v} with hS
  have hSmeas : MeasurableSet S :=
    Metric.isClosed_closedBall.measurableSet.inter (measurableSet_le measurable_const φ.continuous.measurable)
  open scoped Pointwise in
  have hβS : β ≤ 2 * μ S := by
    have hsub : B ⊆ S ∪ -S := by
      intro v hv
      by_cases h : 0 ≤ φ v
      · exact Or.inl ⟨hv, h⟩
      · right
        refine ⟨?_, ?_⟩
        · simpa [hB, Metric.mem_closedBall, norm_neg] using hv
        · show 0 ≤ φ (-v)
          rw [map_neg]
          linarith [not_le.mp h]
    calc β ≤ μ (S ∪ -S) := measure_mono hsub
      _ ≤ μ S + μ (-S) := measure_union_le _ _
      _ = 2 * μ S := by rw [Measure.measure_neg, two_mul]
  have hDc : Continuous (fun z => ‖iteratedFDeriv ℝ (m + 1) G z‖) :=
    (hG.continuous_iteratedFDeriv (by exact_mod_cast (le_top : ((m+1 : ℕ) : ℕ∞) ≤ ⊤))).norm
  set Ψ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (‖x + y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + y)‖) with hΨ
  have hΨm : Measurable Ψ := by
    apply ENNReal.measurable_ofReal.comp
    exact (((continuous_const.add continuous_id).norm.pow k).mul
      (hDc.comp (continuous_const.add continuous_id))).measurable
  set a : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) with ha
  set H : E → ℝ≥0∞ := fun v => ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) with hH
  have hpt : ∀ v ∈ S, v ≠ 0 → a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    intro v hvS hv0
    have hray : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0) := by
      intro j hj
      refine (hdec j hj).comp ?_
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have h1 : Tendsto (fun t : ℝ => t * ‖v‖ + -‖x‖) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hvpos)
      refine tendsto_atTop_mono (fun t => ?_) h1
      have e1 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
        simpa using norm_sub_le (x + t • v) x
      have e2 : t * ‖v‖ ≤ ‖t • v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg v)
      show t * ‖v‖ + -‖x‖ ≤ ‖x + t • v‖
      linarith
    have hR := GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' G m x v hG hray
    have hxk : (0:ℝ) ≤ ‖x‖ ^ k := by positivity
    calc a = ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal ‖G x‖ := by rw [ha, ENNReal.ofReal_mul hxk]
      _ ≤ ENNReal.ofReal (‖x‖ ^ k) * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by gcongr
      _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (m.factorial : ℝ)) *
            (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v)) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
          have ht0 : (0:ℝ) ≤ t := le_of_lt ht
          have hmono : ‖x‖ ≤ ‖x + t • v‖ := by
            have h1 : φ x ≤ φ (x + t • v) := by
              rw [map_add (f := _), map_smul, smul_eq_mul]
              have : 0 ≤ φ v := hvS.2
              nlinarith
            have h2 : φ (x + t • v) ≤ ‖x + t • v‖ := by
              calc φ (x + t • v) ≤ |φ (x + t • v)| := le_abs_self _
                _ = ‖φ (x + t • v)‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖φ‖ * ‖x + t • v‖ := φ.le_opNorm _
                _ ≤ 1 * ‖x + t • v‖ := mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
                _ = ‖x + t • v‖ := one_mul _
            have h0 : φ x = ‖x‖ := by simpa using hφx
            linarith
          have hpow : ‖x‖ ^ k ≤ ‖x + t • v‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) hmono k
          have hfac : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
          have hP : 0 ≤ t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖) := by positivity
          have hA : 0 ≤ t ^ m * ‖v‖ ^ (m + 1) := by positivity
          have hf : 0 ≤ 1 / (m.factorial : ℝ) := by positivity
          show ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) ≤
            ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) *
              ENNReal.ofReal (‖x + t • v‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖))
          rw [← ENNReal.ofReal_mul hxk, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hf]
          apply ENNReal.ofReal_le_ofReal
          have e : 1 / (m.factorial : ℝ) * (t ^ m * ‖v‖ ^ (m + 1) * (‖x + t • v‖ ^ k *
              ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) = ‖x + t • v‖ ^ k * (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right hpow hP
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hae : ∀ᵐ v ∂(μ.restrict S), a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    rw [ae_restrict_iff' hSmeas]
    have h0 : ∀ᵐ v ∂μ, v ≠ (0:E) := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [h0] with v hv0 hvS
    exact hpt v hvS hv0
  have hI : ∫⁻ y, Ψ y ∂μ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ :=
    lintegral_add_left_eq_self (μ := μ) (fun z => ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖)) x
  have hmain : μ S * a ≤ c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
    calc μ S * a = ∫⁻ _ in S, a ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ v in S, ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v ∂μ := lintegral_mono_ae hae
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in S, H v ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in B, H v ∂μ := by
          gcongr
          exact inter_subset_left
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ) := by
          gcongr
          exact _root_.GlobalTheory.rayAvg_bound μ Ψ m hΨm hdim
      _ = c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
          rw [hI, hc, mul_assoc]
  have h2 : a * β ≤ 2 * (c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ) := by
    calc a * β ≤ a * (2 * μ S) := by gcongr
      _ = 2 * (μ S * a) := by ring
      _ ≤ _ := by gcongr
  have h3 := (ENNReal.le_div_iff_mul_le (Or.inl hβ0) (Or.inl hβtop)).mpr h2
  calc a ≤ _ := h3
    _ = 2 * c / β * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorFieldEqProdGalois
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut.TorsorField

theorem exists_point_pi {K G A Ω : Type} [CommRing K] [Fintype G] [DecidableEq G] [CommRing A]
    [Algebra K A] [Field Ω] [Algebra K Ω] (z : (G → A) →ₐ[K] Ω) :
    ∃ g : G, ∀ f : G → A, z f = z (fun _ => f g) := by
  have hs : ∑ g, (Pi.single g (1 : A) : G → A) = 1 := by
    simpa using Finset.univ_sum_single (1 : G → A)
  have hsum : ∑ g, z (Pi.single g 1) = 1 := by rw [← map_sum, hs, map_one]
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun g => z (Pi.single g 1)) (by rw [hsum]; exact one_ne_zero)
  have hidem : z (Pi.single g 1) = 1 := by
    have h2 : z (Pi.single g 1) * z (Pi.single g 1) = z (Pi.single g 1) * 1 := by
      rw [← map_mul, mul_one]; congr 1; funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
    exact mul_left_cancel₀ hg h2
  refine ⟨g, fun f => ?_⟩
  have hf : f * Pi.single g 1 = (fun _ => f g) * Pi.single g 1 := by
    funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
  calc z f = z f * z (Pi.single g 1) := by rw [hidem, mul_one]
    _ = z (fun _ => f g) * z (Pi.single g 1) := by rw [← map_mul, ← map_mul, hf]
    _ = z (fun _ => f g) := by rw [hidem, mul_one]

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

abbrev galMap (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) :
    M ⊗[K] M →ₐ[K] (Multiplicative (ZMod q) → M) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun _ => AlgHom.id K M))
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun g => (act g).toAlgHom))

theorem galMap_tmul (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (a b : M) :
    galMap act (a ⊗ₜ b) = fun g => a * act g b := by
  funext g; simp [galMap, Algebra.TensorProduct.productMap_apply_tmul]

theorem exists_eq_comp [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x y : M →ₐ[K] Ω) : ∃ g, y = x.comp (act g).toAlgHom := by
  classical
  let Φ := AlgEquiv.ofBijective (galMap act) hbij
  let z := (Algebra.TensorProduct.productMap x y).comp Φ.symm.toAlgHom
  obtain ⟨g, hg⟩ := exists_point_pi z
  have key : ∀ a b : M, x a * y b = z (fun _ => a * act g b) := by
    intro a b
    have hΦ : Φ.symm (galMap act (a ⊗ₜ b)) = a ⊗ₜ b := by
      show Φ.symm (Φ (a ⊗ₜ b)) = _
      exact Φ.symm_apply_apply _
    have h1 : z (galMap act (a ⊗ₜ b)) = x a * y b := by
      show Algebra.TensorProduct.productMap x y (Φ.symm (galMap act (a ⊗ₜ b))) = _
      rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    rw [← h1, hg, galMap_tmul]
  have hx : ∀ a, x a = z (fun _ => a) := fun a => by simpa using key a 1
  refine ⟨g, AlgHom.ext fun b => ?_⟩
  have h := key 1 b
  rw [map_one, one_mul, one_mul] at h
  rw [h, ← hx]; rfl

theorem eq_of_comp_eq [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x : M →ₐ[K] Ω) {g g' : Multiplicative (ZMod q)}
    (h : x.comp (act g).toAlgHom = x.comp (act g').toAlgHom) : g = g' := by
  classical
  by_contra hne
  obtain ⟨w, hw⟩ := hbij.2 (Pi.single g 1)
  have hZ : ∀ k, Algebra.TensorProduct.productMap x (x.comp (act k).toAlgHom) =
      (x.comp (Pi.evalAlgHom K (fun _ => M) k)).comp (galMap act) := by
    intro k; apply Algebra.TensorProduct.ext'; intro a b
    rw [AlgHom.comp_apply, galMap_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    simp
  have e1 := congrArg (fun F => F w) (hZ g)
  have e2 := congrArg (fun F => F w) (hZ g')
  simp only [AlgHom.comp_apply, hw, Pi.evalAlgHom_apply] at e1 e2
  rw [h] at e1
  rw [Pi.single_eq_same] at e1
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at e2
  have := e1.symm.trans e2
  simp at this

end GlobalTheory.KeyOriginCut.TorsorField

namespace GlobalTheory.KeyOriginCut.TorsorField

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

theorem factor_isGalois_dvd [NeZero q] {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M))
    (hbij : Function.Bijective (galMap act)) (π : M →ₐ[K] L) (hπ : Function.Surjective π) :
    IsGalois K L ∧ Module.finrank K L ∣ q := by
  classical
  let Ω := AlgebraicClosure K
  let σ0 : L →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ0inj : Function.Injective σ0 := σ0.toRingHom.injective
  let P : Multiplicative (ZMod q) → Prop := fun g => ∀ a, π a = 0 → π (act g a) = 0
  have hPmul : ∀ g h, P g → P h → P (g * h) := by
    intro g h hg hh a ha; rw [map_mul, AlgEquiv.mul_apply]; exact hg _ (hh a ha)
  have hPone : P 1 := by intro a ha; rw [map_one, AlgEquiv.one_apply]; exact ha
  have hPpow : ∀ g (n : ℕ), P g → P (g ^ n) := by
    intro g n hg; induction n with
    | zero => rw [pow_zero]; exact hPone
    | succ n ih => rw [pow_succ]; exact hPmul _ _ ih hg
  let H : Subgroup (Multiplicative (ZMod q)) :=
    { carrier := {g | P g}
      mul_mem' := fun {g h} hg hh => hPmul g h hg hh
      one_mem' := hPone
      inv_mem' := fun {g} hg => by
        show P g⁻¹
        have hc : g ^ (Fintype.card (Multiplicative (ZMod q)) - 1) * g = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos, pow_card_eq_one]
        rw [← eq_inv_of_mul_eq_one_left hc]
        exact hPpow g _ hg }
  have hτ : ∀ g, P g → ∃ τ : L →ₐ[K] L, τ.comp π = π.comp (act g).toAlgHom := by
    intro g hg
    let E := Ideal.quotientKerAlgEquivOfSurjective hπ
    let f := Ideal.Quotient.liftₐ (RingHom.ker π) (π.comp (act g).toAlgHom)
      (fun a ha => hg a (RingHom.mem_ker.1 ha))
    refine ⟨f.comp E.symm.toAlgHom, AlgHom.ext fun a => ?_⟩
    have hE : E.symm (π a) = Ideal.Quotient.mk _ a := E.symm_apply_eq.2 rfl
    show f (E.symm (π a)) = π (act g a)
    rw [hE]; rfl
  choose! τ hτc using hτ
  have hΨ : ∀ g, P g → (σ0.comp (τ g)).comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro g hg; rw [AlgHom.comp_assoc, hτc g hg, ← AlgHom.comp_assoc]
  have hB : ∀ σ : L →ₐ[K] Ω, ∃ g, P g ∧ σ.comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro σ
    obtain ⟨g, hg⟩ := exists_eq_comp act hbij (σ0.comp π) (σ.comp π)
    refine ⟨g, fun a ha => hσ0inj ?_, hg⟩
    have h := congrArg (fun F => F a) hg
    simp only [AlgHom.comp_apply] at h
    rw [map_zero]; exact h.symm.trans (by rw [ha, map_zero])
  have hcancel : ∀ σ σ' : L →ₐ[K] Ω, σ.comp π = σ'.comp π → σ = σ' := by
    intro σ σ' h; ext l; obtain ⟨a, rfl⟩ := hπ l
    exact congrArg (fun F => F a) h

  let Ψ : H → (L →ₐ[K] Ω) := fun g => σ0.comp (τ g)
  have hΨbij : Function.Bijective Ψ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun σ => ?_⟩
    · have h2 : (σ0.comp π).comp (act g.1).toAlgHom = (σ0.comp π).comp (act g'.1).toAlgHom := by
        rw [← hΨ _ g.2, ← hΨ _ g'.2]; exact congrArg (fun F => F.comp π) h
      exact eq_of_comp_eq act hbij _ h2
    · obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨⟨g, hg⟩, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
  have hcardΩ : Nat.card (L →ₐ[K] Ω) = Module.finrank K L := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  have hcardH : Nat.card H = Module.finrank K L := (Nat.card_eq_of_bijective Ψ hΨbij).trans hcardΩ
  refine ⟨?_, ?_⟩
  ·
    have hsurj : Function.Surjective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro σ
      obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨τ g, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
    have hinj : Function.Injective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro a b h; ext l; exact hσ0inj (congrArg (fun F => F l) h)
    have hLL : Nat.card (L →ₐ[K] L) = Module.finrank K L :=
      (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).trans hcardΩ
    apply IsGalois.of_card_aut_eq_finrank
    rw [← hLL]
    exact Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).toEquiv
  · rw [← hcardH]
    have := Subgroup.card_subgroup_dvd_card H
    simpa [Nat.card_eq_fintype_card] using this

end GlobalTheory.KeyOriginCut.TorsorField


open GlobalTheory.KeyOriginCut.TorsorField in
theorem GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois :
    ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  intro K M _ _ _ q act hq htor
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.Etale K M := GlobalTheory.KeyOriginCut.etale_of_isZTorsor K M q act htor
  obtain ⟨I, hI, L, hF, hA, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K M).1 inferInstance
  have hbij : Function.Bijective (galMap act) := htor.2.2.2
  have key : ∀ i, IsGalois K (L i) ∧ Module.finrank K (L i) ∣ q := by
    intro i
    haveI := (hL i).1
    haveI := (hL i).2
    exact factor_isGalois_dvd act hbij ((Pi.evalAlgHom K L i).comp e.toAlgHom)
      ((Function.surjective_eval i).comp e.surjective)
  exact ⟨I, Fintype.ofFinite I, L, hF, hA, fun i => (hL i).1, fun i => (key i).1,
    fun i => (key i).2, ⟨e⟩⟩
end
end

