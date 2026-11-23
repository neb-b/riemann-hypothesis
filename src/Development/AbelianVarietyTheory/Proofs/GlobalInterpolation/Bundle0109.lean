module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsOrthogonalComplementUnitaryFrameOfMatrix
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.PerpFrameOfMatrix

theorem herm_eq_dot {P Q : ℕ} (u v : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm u v = star v ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ u := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    mul_comm, neg_mulVec]

theorem isPerpFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  intro P Q P' Q' hc x hx C h1 h2 ι hι
  have hx' : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0 := by
    rw [← herm_eq_dot, ActionCoordinates.herm_self]; exact_mod_cast hx
  have hperp : ∀ v, star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (C *ᵥ v) = 0 := fun v => by
    have h3 : star x ᵥ* (Formalism.UG.Jpq P Q * C) = 0 := by
      have := congrArg star h2
      rwa [star_mulVec, conjTranspose_mul, conjTranspose_conjTranspose,
        GlobalTheory.UnfoldingCompare.Jpq_conjTranspose, star_zero] at this
    rw [mulVec_mulVec, dotProduct_mulVec, h3, zero_dotProduct]
  refine ⟨fun v w => ?_, fun y => ⟨fun hy => ?_, ?_⟩, fun g => ⟨(hι g).2, fun v => ?_⟩⟩
  · rw [herm_eq_dot, herm_eq_dot, toLin'_apply, toLin'_apply, star_mulVec, mulVec_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h1]
  · obtain ⟨N, B, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx' h1 h2
    have e : y = C *ᵥ ((N *ᵥ y) ∘ Sum.inl) + (N *ᵥ y) (Sum.inr ()) • x := by
      conv_lhs => rw [← one_mulVec y, ← hN, ← mulVec_mulVec, fromCols_mulVec]
      congr 1
      funext i
      simp [mulVec, dotProduct, mul_comm]
    have ha : (N *ᵥ y) (Sum.inr ()) = 0 := by
      rw [herm_eq_dot, e, mulVec_add, mulVec_smul, dotProduct_add, hperp, zero_add,
        dotProduct_smul, smul_eq_mul] at hy
      exact (mul_eq_zero.1 hy).resolve_right hx'
    refine ⟨(N *ᵥ y) ∘ Sum.inl, ?_⟩
    rw [ha, zero_smul, add_zero] at e
    rw [toLin'_apply, ← e]
  · rintro ⟨v, rfl⟩
    rw [herm_eq_dot, toLin'_apply, hperp]
  · simp only [ActionCoordinates.act, toLin'_apply, mulVec_mulVec, (hι g).1]

end GlobalTheory.PerpFrameOfMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem kit_of_points : ∀ (Q : PtProp) (C : FC) (cD ch : ℝ) (s : Scale) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool), (∀ u0 : ℕ, u0 < R.n → ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q) → ∃ k : Kit C cD ch s, ∀ i, (∃ u0, (k.pt i).From H a b c u0) ∧ CanonInst (k.pt i).ta.Gx ∧ (k.pt i).Has Q := by
  intro Q C cD ch s R H a b M c hObj
  have hn : 0 < R.n := by unfold Ranks.n; exact R.ord_pos
  choose pt hsc hval har hfrom hcan hhas using fun i : Fin R.n => hObj i.1 i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ⟨⟨i.1, hfrom i⟩, hcan i, hhas i⟩⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩

end GlobalTheory.EX.DC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LitThin
section
namespace GlobalTheory.ThinScaleLiterature

theorem litThin : Formalism.MainNotions.LitThin :=
  ⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩

end GlobalTheory.ThinScaleLiterature
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.LocCharComp

private theorem eventually_abs_le_half_add_of_doubling_bounds {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ x ∈ P.asIdeal, ∃ x₂ : 𝓞 E, x * s = x₂ * π := by
  have hle : Ideal.span {π} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hπ2
    have hsub : Ideal.span {π} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact hsub (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨s, hsP, fun x hx => ?_⟩
  have hmem : x * s ∈ Ideal.span {π} := hJ ▸ Ideal.mul_mem_mul hx hsJ
  obtain ⟨x₂, hx₂⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨x₂, hx₂.symm⟩

private theorem exists_unit_mul_eq_mul_uniformizer_pow {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) :
    ∀ n : ℕ, ∀ x : 𝓞 E, x ∉ P.asIdeal ^ (n + 1) →
      ∃ (m : ℕ) (s x' : 𝓞 E), s ∉ P.asIdeal ∧ x' ∉ P.asIdeal ∧ s * x = x' * π ^ m := by
  obtain ⟨s₀, hs₀, hstep⟩ := eventually_abs_le_half_add_of_doubling_bounds P π hπ hπ2
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  intro n
  induction n with
  | zero =>
    intro x hx
    exact ⟨0, 1, x, h1, by simpa using hx, by simp⟩
  | succ n ih =>
    intro x hx
    by_cases hxP : x ∈ P.asIdeal
    · obtain ⟨x₂, hx₂⟩ := hstep x hxP
      have hx₂n : x₂ ∉ P.asIdeal ^ (n + 1) := by
        intro h
        apply hx
        have hmem : x * s₀ ∈ P.asIdeal ^ (n + 1 + 1) := by
          rw [hx₂, pow_succ]
          exact Ideal.mul_mem_mul h hπ
        have hv := (P.intValuation_le_pow_iff_mem _ _).2 hmem
        rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.2 hs₀, mul_one] at hv
        exact (P.intValuation_le_pow_iff_mem _ _).1 hv
      obtain ⟨m, s, x', hs, hx', he⟩ := ih x₂ hx₂n
      refine ⟨m + 1, s * s₀, x', fun h => (P.isPrime.mem_or_mem h).elim hs hs₀, hx', ?_⟩
      calc s * s₀ * x = s * (x * s₀) := by ring
        _ = s * x₂ * π := by rw [hx₂]; ring
        _ = x' * π ^ (m + 1) := by rw [he]; ring
    · exact ⟨0, 1, x, h1, hxP, by simp⟩

private theorem exists_notMem_pow_succ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E)
    (hx : x ≠ 0) : ∃ n : ℕ, x ∉ P.asIdeal ^ (n + 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation x = WithZero.exp (-(n : ℤ)) := ⟨_, P.intValuation_if_neg hx⟩
  refine ⟨n, fun h => ?_⟩
  have hv := (P.intValuation_le_pow_iff_mem _ _).2 h
  rw [hn, WithZero.exp_le_exp] at hv
  push_cast at hv
  omega

private theorem exists_zpow_uniformizer_factorization {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) (a : E) (ha : a ≠ 0) :
    ∃ (z : ℤ) (r s : 𝓞 E), r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E π ^ z := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨n₁, hn₁⟩ := exists_notMem_pow_succ P x hx0
  obtain ⟨n₂, hn₂⟩ := exists_notMem_pow_succ P y hy0
  obtain ⟨m₁, s₁, x₁, hs₁, hx₁, e₁⟩ := exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₁ x hn₁
  obtain ⟨m₂, s₂, y₁, hs₂, hy₁, e₂⟩ := exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₂ y hn₂
  refine ⟨(m₁ : ℤ) - m₂, x₁ * s₂, y₁ * s₁, fun h => (P.isPrime.mem_or_mem h).elim hx₁ hs₂,
    fun h => (P.isPrime.mem_or_mem h).elim hy₁ hs₁, ?_⟩
  have e₁' := congrArg (algebraMap (𝓞 E) E) e₁
  have e₂' := congrArg (algebraMap (𝓞 E) E) e₂
  simp only [map_mul, map_pow] at e₁' e₂'
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Submodule.zero_mem _)
  have hY : algebraMap (𝓞 E) E y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
  have hpi : algebraMap (𝓞 E) E π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ0
  rw [zpow_sub₀ hpi, zpow_natCast, zpow_natCast, map_mul, map_mul]
  field_simp
  linear_combination (algebraMap (𝓞 E) E y₁ * algebraMap (𝓞 E) E π ^ m₂) * e₁' -
    (algebraMap (𝓞 E) E x₁ * algebraMap (𝓞 E) E π ^ m₁) * e₂'

private theorem exists_integer_ratio_of_isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : IsUnit (redP P b)) :
    ∃ r s : 𝓞 E, r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P b = Ideal.Quotient.mk P.asIdeal r := by
  have := P.isPrime
  unfold redP at hb ⊢
  split_ifs at hb ⊢ with h
  · obtain ⟨r, s, hs, hsb, hc⟩ := h.choose_spec
    refine ⟨r, s, fun hr => ?_, hs, hsb, hc⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, hb.mul_left_eq_zero] at hc
    exact hs (Ideal.Quotient.eq_zero_iff_mem.1 hc)
  · exact absurd hb not_isUnit_zero

private theorem isUnit_redP_of_integer_ratio {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (r s : 𝓞 E) (hr : r ∉ P.asIdeal) (hs : s ∉ P.asIdeal)
    (hsb : algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r) : IsUnit (redP P b) := by
  let := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hsb,
      by rw [mul_comm (Ideal.Quotient.mk P.asIdeal r), ← mul_assoc, mul_inv_cancel₀ hs', one_mul]⟩
  unfold redP
  rw [dite_eq_left hex]
  obtain ⟨r₂, s₂, hs₂, hsb₂, hc₂⟩ := hex.choose_spec
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc₂
  have he : s * r₂ = s₂ * r := IsFractionRing.injective (𝓞 E) E (by
    simp only [map_mul]
    rw [← hsb₂, ← hsb]
    ring)
  have hmem : s₂ * r ∈ P.asIdeal := he ▸ Ideal.mul_mem_left _ s hc₂
  exact (P.isPrime.mem_or_mem hmem).elim hs₂ hr

theorem locChar_eq_locK : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  intro E K _ _ _ σ P ψ cq t hq2 h1 h2 a
  have := P.isPrime
  let := Ideal.Quotient.field P.asIdeal
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hπ : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hπE : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) := by
    rw [map_natCast]
    rfl
  have hπne : ((qOf P : ℕ) : E) ≠ 0 := by
    rw [hπE]
    refine (map_ne_zero_iff _ hinj).2 fun h0 => hq2 ?_
    rw [h0]
    exact Submodule.zero_mem _
  have hex : ∃ z : ℤ, IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ z)) := by
    obtain ⟨z, r, s, hr, hs, hsa⟩ := exists_zpow_uniformizer_factorization P _ hπ hq2 (a : E) a.ne_zero
    refine ⟨z, isUnit_redP_of_integer_ratio P _ r s hr hs ?_⟩
    rw [hπE, mul_div_assoc', hsa, mul_div_assoc, div_self (zpow_ne_zero _ (hπE ▸ hπne)), mul_one]
  have hU : IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ LocE.vP P (qOf P) (a : E))) :=
    Classical.epsilon_spec hex
  obtain ⟨r, s, hr, hs, hsb, hc⟩ := exists_integer_ratio_of_isUnit_redP P _ hU
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hr (h0 ▸ Submodule.zero_mem _)
  have hs0 : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hs (h0 ▸ Submodule.zero_mem _)
  have hmr : Ideal.Quotient.mk P.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hms : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  set w := LocE.vP P (qOf P) (a : E)
  let Q : Eˣ := Units.mk0 _ hπne
  let xr : Eˣ := Units.mk0 _ hr0
  let xs : Eˣ := Units.mk0 _ hs0
  let cr : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hmr
  let cs : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hms
  have hA : a = Q ^ w * xr * xs⁻¹ := by
    ext
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0, Q, xr, xs]
    rw [← hsb]
    field_simp
  have hB : hU.unit = cr * cs⁻¹ := by
    ext
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, cr, cs]
    rw [← hc]
    field_simp
  have eQ := h1 Q rfl
  have er := h2 xr r cr rfl rfl
  have es := h2 xs s cs rfl rfl
  show σ (cq ^ w * LocE.unitV t ((a : E) / ((qOf P : ℕ) : E) ^ w)) = _
  unfold LocE.unitV
  rw [dite_eq_left hU, hB]
  conv_rhs => rw [hA]
  simp only [map_mul, map_inv, map_zpow, map_zpow₀, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, map_inv₀, eQ, er, es]
  ring

end GlobalTheory.LocCharComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegOneZpowRound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Move

theorem finsum_eq_sum_reps {G V : Type} [AddCommGroup G] [AddCommGroup V] (φ : G →+ V) (M M' : AddSubgroup G)
    (Λ₁ Λ₂ : AddSubgroup V) (h₁ : ∀ y, φ y ∈ Λ₁ ↔ y ∈ M) (h₂ : ∀ v, v ∈ Λ₂ ↔ ∃ y ∈ M', φ y = v) (R : Finset G)
    (hR : IsReps M M' R) (F : V → ℂ) (hF : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → F (x + l) = F x) :
    (Λ₁.addSubgroupOf Λ₂).index = R.card ∧
      ∑ᶠ q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, F ((Quotient.out q : Λ₂) : V) = ∑ y ∈ R, F (φ y) := by
  classical
  let f : R → Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ := fun y => QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have := QuotientAddGroup.eq.1 hxy
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have h3 : φ (y.1 - x.1) ∈ Λ₁ := by simpa [map_sub, neg_add_eq_sub] using this
      exact Subtype.ext (hR.2.1 _ y.2 _ x.2 ((h₁ _).1 h3)).symm
    · intro q
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨y, hy, hv⟩ := (h₂ _).1 v.2
      obtain ⟨x, hx, hxy⟩ := hR.2.2 y hy
      refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.2 ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have := (h₁ _).2 hxy
      simpa [map_sub, neg_add_eq_sub, hv] using this
  let e := Equiv.ofBijective f hf
  refine ⟨?_, ?_⟩
  · rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  · rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq : (QuotientAddGroup.mk ⟨φ y, (h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) =
        QuotientAddGroup.mk (Quotient.out (e y)) := (QuotientAddGroup.out_eq' (e y)).symm
    have h3 := QuotientAddGroup.eq.1 hq
    rw [AddSubgroup.mem_addSubgroupOf] at h3
    have := hF _ ((h₂ _).2 ⟨y, hR.1 y y.2, rfl⟩) _ (Subtype.property _) h3
    rw [← this]
    congr 1
    simp

theorem op_add {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (Λ : AddSubgroup V)
    (hs : IsSelfDual H Λ) (hα : IsSemiChar H Λ α) (F : V → ℂ) (x l : V) (hx : x ∈ Λ) (hl : l ∈ Λ)
    (hF : ∀ z, α l * opU H l F z = F z) (z : V) : α (x + l) * opU H (x + l) F z = α x * opU H x F z := by
  have hx' : x ∈ dualLat H Λ := by rw [hs]; exact hx
  obtain ⟨m, hm⟩ := hx' l hl
  have h1 := hF (z + x)
  have h2 : H l x = H x l - 2 * Complex.I * m := by
    rw [hH x l]
    apply Complex.ext
    · simp
    · simp only [altE] at hm
      simp [hm]; ring
  rw [hα.2 x hx l hl, hm]
  simp only [opU] at h1 ⊢
  rw [← h1, ← add_assoc]
  have h3 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * H z (x + l) - (Real.pi : ℂ) * H (x + l) (x + l) / 2) =
      Complex.exp (-(Real.pi : ℂ) * H (z + x) l - (Real.pi : ℂ) * H l l / 2) *
        Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [map_add (f := _), LinearMap.add_apply, h2]
    push_cast
    ring
  linear_combination (α x * α l * F (z + x + l)) * h3

theorem neg_one_zpow_round (q : ℝ)
    (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = 1 ∨ Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = -1) :
    (-1 : ℂ) ^ (round q) = Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) := by
  have h2 : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I * (q : ℂ))) = 1 := by
    rw [two_mul, Complex.exp_add]
    rcases h with h | h <;> simp [h]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  have hq : (q : ℂ) = n := by
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h0
    linear_combination hn
  have hq' : q = n := by exact_mod_cast hq
  rw [hq, hq', round_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

theorem embH_inj {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine (Pi.basisFun E (Fin a)).ext fun j => funext fun i => ?_
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem move : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → s.Ok → B.EqP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ → IsSdLat N → IsSdLat N' → IsSdLat N'' → ∀ R : Finset (HomE X.E a b), IsReps (per (ambOf s B χ cD) N N').toAddSubgroup (per (ambOf s B χ cD) N N'').toAddSubgroup R → ∀ z, (ambOf s B χ cD).e a b N N'' z = χ (TaylorLogMetric.detId D (s.lat N') (s.lat N'')) ^ (-((a / 2 : ℕ) : ℤ)) * (((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ y ∈ R, Wx (ambOf s B χ cD) y ((ambOf s B χ cD).e a b N N') z) := by
  intro D X s cc δ B χ cD a b N N' N'' _ hs hE ha hb hL hN hN' hN'' R hR z
  obtain ⟨hδ, hτ, -, -, -, hL⟩ := hL
  obtain ⟨t1, t2, t3, -⟩ := _root_.GlobalTheory.SeamTransport.transport D X s cc δ B χ cD a b hs
  set A := ambOf s B χ cD with hA
  letI := D.host.cmStar
  have key := congrFun (hE.2.1 a b ⟨s.lat N, (t2 N N' ha hb hN hN').2.2.1⟩ ⟨s.lat N', (t2 N N' ha hb hN hN').2.2.2⟩
    ⟨s.lat N'', (t2 N N'' ha hb hN hN'').2.2.2⟩ ha hb) fun τ => z (s.iT.symm τ)
  refine key.trans (congrArg₂ (· * ·) rfl ?_)
  let φ : HomE X.E a b →+ TaylorLogMetric.VC D a b :=
    { toFun := fun y τ => emb A y (s.iT.symm τ)
      map_zero' := by funext τ; simp [emb]
      map_add' := fun x y => by funext τ; simp [emb] }
  have hφ : ∀ y, (fun τ => φ y (s.iT τ)) = emb A y := fun y => by funext τ; simp [φ]
  have hmem : ∀ (M : Submodule (𝓞 X.E) (Sp X.E b)) v, v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat M) ↔
      ∃ y ∈ (per A N M).toAddSubgroup, φ y = v := by
    intro M v
    rw [t1]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · funext τ
      have := congrFun h (s.iT.symm τ)
      simp only [Equiv.apply_symm_apply] at this
      exact this
    · rw [← h, hφ]; rfl
  have h₁ : ∀ y, φ y ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ y ∈ (per A N N').toAddSubgroup := by
    intro y
    rw [hmem]
    refine ⟨fun ⟨x, hx, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
    have h' : emb A x = emb A y := by rw [← hφ, ← hφ, h]
    exact embH_inj _ hδ h' ▸ hx
  have hW : ∀ v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N''),
      TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ)) =
      alV A.d A.sc (fun τ => v (s.iT τ)) * opU (HV A.sc) (fun τ => v (s.iT τ)) (A.e a b N N') z := by
    intro v hv
    refine congrArg₂ (· * ·) ?_ ?_
    · have h := (hL N N'' hN hN'').2.2.1 _ ((t1 N N'' v).1 hv)
      unfold TaylorLogMetric.al
      rw [t3]
      exact neg_one_zpow_round _ h
    · unfold TaylorLogMetric.U opU
      rw [t3, t3]
      simp only [Equiv.symm_apply_apply]
      refine congrArg₂ (· * ·) ?_ rfl
      refine congrArg (B.eNat χ a b (s.lat N) (s.lat N')) ?_
      funext τ
      simp
  obtain ⟨e1, e2⟩ := finsum_eq_sum_reps φ _ _ _ _ h₁ (hmem N'') R hR
    (fun v => TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) v * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) v (B.eNat χ a b (s.lat N) (s.lat N'))
        (fun τ => z (s.iT.symm τ))) (by
      intro x hx l hl hl'
      rw [hW _ (add_mem hx hl), hW _ hx]
      exact op_add _ (isHerm_HV _) _ _ (hL N N'' hN hN'').2.1 (hL N N'' hN hN'').2.2 _ _ _ ((t1 N N'' x).1 hx)
        ((t1 N N'' l).1 hl) ((hL N N' hN hN').1 _ ((t1 N N' l).1 hl')) z)
  unfold TaylorLogMetric.Iop
  refine congrArg₂ (· * ·) ?_ (e2.trans (Finset.sum_congr rfl fun y hy => ?_))
  · rw [← e1]
  · rw [hW _ ((hmem N'' _).2 ⟨y, hR.1 y hy, rfl⟩), hφ]
    rfl

end GlobalTheory.MomT.Move
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLattice
section
namespace GlobalTheory.OverObj

theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
end

