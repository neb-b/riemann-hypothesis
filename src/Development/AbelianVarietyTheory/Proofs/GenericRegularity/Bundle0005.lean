module

public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AlgebraicIndependentResidueIffGauss
section
namespace GlobalTheory

open MvPolynomial

theorem residue_valuationSubring_ne_zero_iff {U Γ : Type*} [Field U]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x ≠ 0 ↔ v (x : U) = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring v).symm.eq_one_iff_eq_one

private theorem residue_eval₂_comap {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    IsLocalRing.residue v.valuationSubring
        (MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => ⟨t s, ht s⟩) p) =
      @MvPolynomial.aeval _ _ _ _ _
        (ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f)
        (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)
        (MvPolynomial.map (IsLocalRing.residue (v.valuationSubring.comap f)) p) := by
  let := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  congr 1

private theorem coe_eval₂_comapInclusion_eq_eval₂_map {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    ((MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => (⟨t s, ht s⟩ : v.valuationSubring)) p : v.valuationSubring) : U) =
      MvPolynomial.eval₂ f t (MvPolynomial.map (v.valuationSubring.comap f).subtype p) := by
  rw [MvPolynomial.eval₂_map]
  exact MvPolynomial.eval₂_comp_left v.valuationSubring.subtype _ _ p

private theorem residue_comap_ne_zero_iff_valuation_eq_one {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (c : v.valuationSubring.comap f) :
    IsLocalRing.residue (v.valuationSubring.comap f) c ≠ 0 ↔ v (f c) = 1 := by
  have h := residue_valuationSubring_ne_zero_iff v (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f c)
  rw [← IsLocalRing.ResidueField.map_residue, map_ne_zero] at h
  exact h

theorem algebraicIndependent_residue_iff_gauss (F U : Type) [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) :
    (letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
     AlgebraicIndependent (IsLocalRing.ResidueField (v.valuationSubring.comap f))
      (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)) ↔
    ∀ p : MvPolynomial σ F, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (MvPolynomial.eval₂ f t p) = 1 := by
  let := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [algebraicIndependent_iff]
  constructor
  · intro hind p hle hone
    obtain ⟨q, rfl⟩ : p ∈ Set.range (MvPolynomial.map (v.valuationSubring.comap f).subtype) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨α, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      exact ⟨⟨p.coeff α, ValuationSubring.mem_comap.mpr ((v.mem_valuationSubring_iff _).mpr (hle α))⟩, rfl⟩
    obtain ⟨α, hα⟩ := hone
    rw [MvPolynomial.coeff_map] at hα
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap]
    intro h0
    have hq := congrArg (AddMonoidAlgebra.coeff · α) (hind _ h0)
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at hq
    exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mpr hα hq
  · intro hg r hr
    by_contra hne
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective r
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    rw [MvPolynomial.coeff_map] at hα
    have hle : ∀ β, v (f ((MvPolynomial.map (v.valuationSubring.comap f).subtype q).coeff β)) ≤ 1 := by
      intro β
      rw [MvPolynomial.coeff_map]
      exact (v.mem_valuationSubring_iff _).mp (ValuationSubring.mem_comap.mp (q.coeff β).2)
    have h1 := hg _ hle ⟨α, by
      rw [MvPolynomial.coeff_map]
      exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mp hα⟩
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap] at h1
    exact h1 hr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes
section
namespace GlobalTheory

theorem exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime {S : Type*} [CommRing S]
    {q : Ideal S} (hq : q ∈ minimalPrimes S) (m : Ideal S) [m.IsPrime] (hqm : q ≤ m)
    [IsDomain (Localization.AtPrime m)] {x : S} (hx : x ∈ q) :
    ∃ s : m.primeCompl, (s : S) * x = 0 := by
  have hPq : (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) ≤ q := by
    intro y hy
    have hy0 : algebraMap S (Localization.AtPrime m) y = 0 := hy
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ y).1 hy0
    have hsy : (s : S) * y ∈ q := by
      rw [hs]
      exact q.zero_mem
    have hsq : (s : S) ∉ q := fun h => s.2 (hqm h)
    exact (hq.1.1.mem_or_mem hsy).resolve_left hsq
  have hqP : q ≤ (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) :=
    hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hPq
  have hx0 : algebraMap S (Localization.AtPrime m) x = 0 := hqP hx
  exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 hx0

theorem isIntegrallyClosed_quotient_of_mem_minimalPrimes {S : Type*} [CommRing S]
    (hS : ∀ (m : Ideal S) [m.IsPrime],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m))
    {q : Ideal S} (hq : q ∈ minimalPrimes S) : IsIntegrallyClosed (S ⧸ q) := by
  have : q.IsPrime := hq.1.1
  refine IsIntegrallyClosed.of_localization_maximal (fun M _ _ => ?_)
  let m : Ideal S := M.comap (Ideal.Quotient.mk q)
  have : m.IsPrime := Ideal.comap_isPrime _ _
  have hqm : q ≤ m := by
    intro x hx
    show Ideal.Quotient.mk q x ∈ M
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact M.zero_mem
  obtain ⟨hdom, hic⟩ := hS m
  have hker : ∀ x ∈ q, algebraMap S (Localization.AtPrime m) x = 0 := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime hq m hqm hx
    exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).2 ⟨s, hs⟩
  let : Algebra (S ⧸ q) (Localization.AtPrime m) :=
    (Ideal.Quotient.lift q (algebraMap S (Localization.AtPrime m)) hker).toAlgebra
  have hmk : ∀ a : S, algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q a) =
      algebraMap S (Localization.AtPrime m) a := fun a => Ideal.Quotient.lift_mk _ _ _
  have : IsLocalization M.primeCompl (Localization.AtPrime m) := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      show IsUnit (algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q s))
      rw [hmk]
      exact IsLocalization.map_units (Localization.AtPrime m) (⟨s, hy⟩ : m.primeCompl)
    · intro z
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl z
      refine ⟨⟨Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q s, s.2⟩⟩, ?_⟩
      show z * algebraMap (S ⧸ q) _ (Ideal.Quotient.mk q s) =
        algebraMap (S ⧸ q) _ (Ideal.Quotient.mk q a)
      rw [hmk, hmk]
      exact h
    · intro a b hab
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [hmk, hmk] at hab
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl _).1 hab
      refine ⟨⟨Ideal.Quotient.mk q c, c.2⟩, ?_⟩
      show Ideal.Quotient.mk q c * Ideal.Quotient.mk q a =
        Ideal.Quotient.mk q c * Ideal.Quotient.mk q b
      rw [← map_mul, ← map_mul, hc]
  exact hic.of_equiv (IsLocalization.algEquiv M.primeCompl (Localization.AtPrime M)
    (Localization.AtPrime m)).toRingEquiv.symm

theorem isIntegrallyClosed_quotient_minimalPrime_of_smooth :
    ∀ (F S : Type) [Field F] [CommRing S] [Algebra F S] [Algebra.Smooth F S] (q : Ideal S),
      q ∈ minimalPrimes S → IsIntegrallyClosed (S ⧸ q) := by
  intro F S _ _ _ _ q hq
  refine isIntegrallyClosed_quotient_of_mem_minimalPrimes (fun m _ => ?_) hq
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth F m (Localization.AtPrime m)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto
section
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.PeriodLift

theorem exists_matrix_lift {r : ℕ} {ι : Type} {𝓕 : Filter ι} (p : Fin r → Prop) [DecidablePred p]
    (A₀ : Matrix (Fin r) (Fin r) ℂ) (A : ι → Matrix (Fin r) (Fin r) ℂ)
    (h0 : A₀.det ≠ 0) (hA : ∀ᶠ n in 𝓕, (A n).det ≠ 0)
    (hc : ∀ a, p a → ∀ k, Tendsto (fun n => A n k a) 𝓕 (𝓝 (A₀ k a)))
    (hr : ∀ a, ¬ p a → ∀ k, Tendsto (fun n => (A n)⁻¹ a k) 𝓕 (𝓝 (A₀⁻¹ a k))) :
    ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 A₀) ∧ ∀ᶠ n in 𝓕,
      (∀ a, p a → ∀ k, B n k a = A n k a) ∧ (∀ a, ¬ p a → ∀ k, (B n)⁻¹ a k = (A n)⁻¹ a k) := by
  set Q : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun k a => if p a then A n k a else A₀ k a with hQdef
  set D : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun a j =>
      if p a then (1 : Matrix (Fin r) (Fin r) ℂ) a j else ((A n)⁻¹ * Q n) a j with hDdef
  have hQe : ∀ k a, Tendsto (fun n => Q n k a) 𝓕 (𝓝 (A₀ k a)) := by
    intro k a
    by_cases h : p a
    · simpa [hQdef, h] using hc a h k
    · simpa [hQdef, h] using tendsto_const_nhds
  have hQ : Tendsto Q 𝓕 (𝓝 A₀) :=
    tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => hQe k a
  have hD : Tendsto D 𝓕 (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun j => ?_
    by_cases h : p a
    · simpa [hDdef, h] using tendsto_const_nhds
    · have e : (1 : Matrix (Fin r) (Fin r) ℂ) a j = ∑ k, A₀⁻¹ a k * A₀ k j := by
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Ne.isUnit h0)]
      rw [e]
      simp only [hDdef, Matrix.of_apply, h, if_false, Matrix.mul_apply]
      exact tendsto_finsetSum _ fun k _ => (hr a h k).mul (hQe k j)
  have hdet : Continuous fun M : Matrix (Fin r) (Fin r) ℂ => M.det := continuous_id.matrix_det
  have hDi : Tendsto (fun n => (D n)⁻¹) 𝓕 (𝓝 1) := by
    have hc1 : ContinuousAt Inv.inv (1 : Matrix (Fin r) (Fin r) ℂ) := by
      apply continuousAt_matrix_inv
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have := hc1.tendsto.comp hD
    simpa [Function.comp_def] using this
  have hQd : ∀ᶠ n in 𝓕, (Q n).det ≠ 0 := ((hdet.tendsto _).comp hQ).eventually_ne h0
  have hDd : ∀ᶠ n in 𝓕, (D n).det ≠ 0 :=
    ((hdet.tendsto _).comp hD).eventually_ne (by simp)
  refine ⟨fun n => Q n * (D n)⁻¹, by simpa using hQ.mul hDi, ?_⟩
  filter_upwards [hA, hQd, hDd] with n hAn hQn hDn
  constructor
  · intro j hj k
    have hDj : ∀ i, D n i j = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
      intro i
      by_cases h : p i
      · simp [hDdef, h]
      · rw [← Matrix.nonsing_inv_mul _ (Ne.isUnit hAn)]
        simp [hDdef, hQdef, h, hj, Matrix.mul_apply]
    have e : (Q n * (D n)⁻¹ * D n) k j = (Q n * (D n)⁻¹ * (1 : Matrix (Fin r) (Fin r) ℂ)) k j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [hDj]
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ (Ne.isUnit hDn)] at e
    rw [← e]
    simp [hQdef, hj]
  · intro a ha k
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit hDn)]
    have e : ((A n)⁻¹ * Q n * (Q n)⁻¹) a k = (A n)⁻¹ a k := by
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit hQn)]
    rw [← e, Matrix.mul_apply, Matrix.mul_apply]
    simp [hDdef, ha]

theorem tendsto_of_span {E : Type} [Field E] {r : ℕ} {ι : Type} {𝓕 : Filter ι}
    (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ : ι → (Fin r → E) → ℂ) (Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ n v w, Φ n (v + w) = Φ n v + Φ n w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ n (c : E) v, Φ n (c • v) = σ c * Φ n v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0)
    (h : ∀ v ∈ S, Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v))) (v : Fin r → E) :
    Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v)) := by
  have hv : v ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e : (0 : Fin r → E) = (0 : E) • (0 : Fin r → E) := by simp
    rw [e]
    simp only [hs, hs₀, hσ, zero_mul]
    exact tendsto_const_nhds
  | add x y _ _ hx hy => simpa only [ha, ha₀] using hx.add hy
  | smul c x _ hx => simpa only [hs, hs₀] using hx.const_mul (σ c)

theorem hermC_emb_inv_col {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (u : Fin r → ℂ) (k : Fin r) :
    hermC τ G u (Data.emb τ fun b => cc (G⁻¹ b k)) = u k := by
  have e : ∀ a, ∑ b, u a * τ (G a b) * (starRingEnd ℂ) (τ (cc (G⁻¹ b k))) =
      u a * τ ((G * G⁻¹) a k) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.conj_conj, map_mul, mul_assoc]
  simp only [hermC, Data.emb, e]
  rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hG)]
  simp [Matrix.one_apply, apply_ite τ]

theorem period_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ι : Type) (𝓕 : Filter ι) (x₀ : Frame X.Ψ r) (x₁ : ι → Frame X.Ψ r), x₀ ∈ X.dom → (∀ᶠ n in 𝓕, x₁ n ∈ X.dom) → (∀ v ∈ X.Λ, ∀ (τ : X.Ψ) (a : Fin r), Tendsto (fun n => (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)) 𝓕 (𝓝 (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v) else ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a))) → ∀ V ∈ 𝓝 x₀, ∀ᶠ n in 𝓕, ∃ x ∈ V, ∀ (v : Fin r → E) (τ : X.Ψ) (a : Fin r), (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a) = (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a) := by
  intro E _ _ _ r X ι 𝓕 x₀ x₁ h0 h1 h V hV
  have key : ∀ τ : X.Ψ, ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 (mat x₀ τ)) ∧
      ∀ᶠ n in 𝓕, (∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k, B n k a = mat (x₁ n) τ k a) ∧
        (∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k, (B n)⁻¹ a k = (mat (x₁ n) τ)⁻¹ a k) := by
    intro τ
    refine exists_matrix_lift (fun a : Fin r => (a : ℕ) < X.p0) (mat x₀ τ)
      (fun n => mat (x₁ n) τ) (h0 τ).1 (h1.mono fun n hn => (hn τ).1) ?_ ?_
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun n v => hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun n v => ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  choose B hB hB' using key
  have hx : Tendsto (fun n => (fun τ => B τ n : Frame X.Ψ r)) 𝓕 (𝓝 x₀) :=
    tendsto_pi_nhds.2 fun τ => hB τ
  filter_upwards [hx.eventually_mem hV, eventually_all.2 hB'] with n hn hn'
  refine ⟨_, hn, fun v τ a => ?_⟩
  have hm : mat (fun τ => B τ n : Frame X.Ψ r) τ = B τ n := rfl
  rw [hm]
  by_cases ha : (a : ℕ) < X.p0
  · have : col (B τ n) a = col (mat (x₁ n) τ) a := funext fun k => (hn' τ).1 a ha k
    simp only [ha, if_true, this]
  · simp only [ha, if_false, Matrix.mulVec, dotProduct, (hn' τ).2 a ha]

end GlobalTheory.PeriodLift
end

