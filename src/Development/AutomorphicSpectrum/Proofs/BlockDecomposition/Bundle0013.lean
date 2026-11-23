module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadical
section
namespace GlobalTheory.CompanionTheory.HermitianForm

theorem re_pairing_eq_zero_of_psd {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by
  have hb : 0 ≤ (B u u).re := hpos u
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re := by
    intro t
    have h := hpos (v + (t : ℂ) • u)
    have e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u)
        = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u := by
      simp only [map_add (f := _), LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Complex.conj_ofReal]
      ring
    rw [e, hv, hB v u] at h
    simp only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h
    nlinarith [h]
  set a := (B v u).re with ha
  set b := (B u u).re with hb'
  have hb1 : 0 < b + 1 := by linarith
  have h := key (-a / (b + 1))
  have e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [e2] at h
  have h3 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    by_contra hc
    push Not at hc
    have : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  have h4 : a ^ 2 * (b + 2) ≤ 0 := by linarith
  have h5 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < a ^ 2 * (b + 2) := mul_pos hc (by linarith)
    linarith
  have h6 : a ^ 2 = 0 := le_antisymm h5 (sq_nonneg a)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h6

theorem pairing_eq_zero_of_psd : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  intro V _ _ B hB hpos v hv w
  have hre := re_pairing_eq_zero_of_psd B hB hpos v hv w
  have him := re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)
  have e : B v (Complex.I • w) = -Complex.I * B v w := by
    simp only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]
  rw [e] at him
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end GlobalTheory.CompanionTheory.HermitianForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
section
open Matrix

namespace GlobalTheory.CompanionTheory.Herm

theorem apply_eq_zero_of_isotropic {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hs : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = B x w := ⟨_, rfl⟩
  have hwx : B w x = starRingEnd ℂ c := by rw [hc]; exact hs x w
  have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq c
      + t ^ 2 * Complex.normSq c * (B w w).re := by
    intro t
    have h := hp (x - ((t : ℂ) * c) • w)
    have e : B (x - ((t : ℂ) * c) • w) (x - ((t : ℂ) * c) • w)
        = B x x - starRingEnd ℂ ((t : ℂ) * c) * c - ((t : ℂ) * c) * starRingEnd ℂ c
          + ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) * B w w := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.map_smulₛₗ, smul_eq_mul, ← hc, hwx]
      ring
    have e1 : starRingEnd ℂ ((t : ℂ) * c) * c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, mul_comm (starRingEnd ℂ c) c,
        Complex.mul_conj]
      push_cast; ring
    have e2 : ((t : ℂ) * c) * starRingEnd ℂ c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj]
      push_cast; ring
    have e3 : ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c)
        = ((t ^ 2 * Complex.normSq c : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal]
      push_cast; ring
    rw [e, e1, e2, e3] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hx] at h
    linarith
  by_contra hne
  have hc0 : c ≠ 0 := by rw [hc]; exact hne
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc0
  have hr : 0 ≤ (B w w).re := hp w
  obtain ⟨r, hrdef⟩ : ∃ r, r = (B w w).re := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hk := key (1 / (r + 1))
  rw [← hrdef] at hk
  have hr1 : 0 < r + 1 := by linarith
  have hid : -2 * (1 / (r + 1)) * Complex.normSq c
      + (1 / (r + 1)) ^ 2 * Complex.normSq c * r
      = -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 := by
    field_simp
    ring
  rw [hid] at hk
  have : -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

end GlobalTheory.CompanionTheory.Herm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFinite
section
namespace GlobalTheory.CompanionTheory.CosetSum

theorem mem_of_translated_bumps : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  intro Γ J _ _ _ Q K K₁ π M Gf hle hidx hconj hdec htr hlawM hlaw hinv hb
  classical
  let H : Subgroup K := K₁.subgroupOf K
  haveI hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : Γ) ∈ K₁ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa using hconj g g.2 n hn'⟩
  haveI : H.FiniteIndex := ⟨hidx⟩
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let P : Γ → Prop := fun x => ∃ q : Q, ∃ b ∈ K₁, x = (q : Γ) * b
  have hPmul : ∀ x, ∀ b ∈ K₁, P x → P (x * b) := by
    rintro x b hb' ⟨q, c, hc, rfl⟩
    exact ⟨q, c * b, K₁.mul_mem hc hb', by simp [mul_assoc]⟩
  have hb2 : ∀ κ : K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧
      ∀ g : Γ, (¬ P g) → φ g = 0 := fun κ => hb κ κ.2
  choose φ hφM hφ1 hφ0 using hb2
  have key : ∀ κ' κ : K, φ κ ((κ' : Γ) * (κ : Γ)⁻¹) =
      if P ((κ' : Γ) * (κ : Γ)⁻¹) then Gf κ' else 0 := by
    intro κ' κ
    split_ifs with h
    · obtain ⟨q, b, hbm, e⟩ := h
      rw [e, hφ1 κ q b hbm, ← hlaw]
      have hκ' : (κ' : Γ) = q * b * κ := by rw [← e]; group
      have e2 : (q : Γ) * κ = κ' * ((κ : Γ)⁻¹ * b⁻¹ * κ) := by rw [hκ']; group
      have hm : (κ : Γ)⁻¹ * b⁻¹ * κ ∈ K₁ := by
        simpa using hconj _ (K.inv_mem κ.2) _ (K₁.inv_mem hbm)
      rw [e2, hinv _ _ hm]
    · exact hφ0 κ _ h
  let r : K ⧸ H → K := Quotient.out
  have hr : ∀ δ : K ⧸ H, ((r δ : K) : K ⧸ H) = δ := fun δ => QuotientGroup.out_eq' δ
  have hPcl : ∀ x y : K, (x : K ⧸ H) = y → P x → P y := by
    intro x y hxy hx
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    have hm' : (x : Γ)⁻¹ * y ∈ K₁ := by simpa using Subgroup.mem_subgroupOf.1 hm
    have := hPmul _ _ hm' hx
    simpa using this
  let Pd : K ⧸ H → Prop := fun ε => P (r ε)
  have hPd : ∀ x : K, P x ↔ Pd (x : K ⧸ H) := fun x =>
    ⟨hPcl _ _ (hr _).symm, hPcl _ _ (hr _)⟩
  let Φ : Γ → J := ∑ δ : K ⧸ H, (fun g => φ (r δ) (g * ((r δ : K) : Γ)⁻¹))
  have hΦM : Φ ∈ M := M.sum_mem fun δ _ => htr _ (hφM _) _
  let n : ℕ := (Finset.univ.filter Pd).card
  have hΦ : ∀ κ' : K, Φ κ' = n • Gf κ' := by
    intro κ'
    have h1 : Φ κ' = ∑ δ : K ⧸ H, if Pd ((κ' : K ⧸ H) * δ⁻¹) then Gf κ' else 0 := by
      simp only [Φ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [key]
      have hcl : (((κ' * (r δ)⁻¹ : K)) : K ⧸ H) = (κ' : K ⧸ H) * δ⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr]
      have := hPd (κ' * (r δ)⁻¹)
      rw [hcl] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      simp only [this]
    rw [h1]
    have h2 := Equiv.sum_comp ((Equiv.inv (K ⧸ H)).trans (Equiv.mulLeft (κ' : K ⧸ H)))
      (fun ε => if Pd ε then Gf κ' else 0)
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at h2
    rw [h2, ← Finset.sum_filter, Finset.sum_const]
  have hn : n ≠ 0 := by
    have h1 : Pd 1 := by
      have : (r 1 : Γ) ∈ K₁ := by
        have : r 1 ∈ H := (QuotientGroup.eq_one_iff _).1 (hr 1)
        exact Subgroup.mem_subgroupOf.1 this
      exact ⟨1, _, this, by simp⟩
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hΨM : (n : ℂ)⁻¹ • Φ ∈ M := M.smul_mem _ hΦM
  have hEq : (n : ℂ)⁻¹ • Φ = Gf := by
    funext g
    obtain ⟨q, κ, hκ, rfl⟩ := hdec g
    have hK : ((n : ℂ)⁻¹ • Φ) κ = Gf κ := by
      have := hΦ ⟨κ, hκ⟩
      simp only at this
      rw [Pi.smul_apply, this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [hlawM _ hΨM, hK, hlaw]
  exact hEq ▸ hΨM

end GlobalTheory.CompanionTheory.CosetSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerCoordinatesBound
section
open NumberField

namespace GlobalTheory.CompanionTheory.NumberFieldCoord

theorem abs_repr_le_of_forall_norm_embedding_le :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  intro E _ _ I _ τ hτ
  classical
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap
    with hLc
  refine ⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩
  have hR0 : 0 ≤ R := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    obtain ⟨i, -⟩ := hτ w
    exact (norm_nonneg _).trans (hR i)
  have hw : ∀ w : InfinitePlace E, w (e : E) ≤ R := by
    intro w
    obtain ⟨i, rfl⟩ := hτ w
    simpa only [InfinitePlace.apply] using hR i
  have hn : ‖mixedEmbedding E (e : E)‖ ≤ R := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_of_isReal w.2] at h
      simpa [mixedEmbedding] using h
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_eq] at h
      simpa [mixedEmbedding] using h
  have hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply E e k
    rw [show (e : E) = algebraMap (𝓞 E) E e from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  calc ‖Lc (mixedEmbedding E (e : E)) k‖ ≤ ‖Lc (mixedEmbedding E (e : E))‖ := norm_le_pi_norm _ k
    _ ≤ ‖Lc‖ * ‖mixedEmbedding E (e : E)‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * R := by gcongr
    _ ≤ (‖Lc‖ + 1) * R := by nlinarith

end GlobalTheory.CompanionTheory.NumberFieldCoord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
section
open scoped Matrix
open MeasureTheory

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

def PosOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, w ≠ 0 → 0 < ε * (star w ⬝ᵥ Z.mulVec w).re

def NonnegOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, 0 ≤ ε * (star w ⬝ᵥ Z.mulVec w).re

theorem integrable_of_mul_unimodular {α : Type} [MeasurableSpace α] (μ : Measure α) (a b : α → ℂ)
    (hi : Integrable (fun x => a x * b x) μ) (hb : AEStronglyMeasurable b μ) (hb1 : ∀ x, ‖b x‖ = 1) :
    Integrable a μ := by
  have hfun : a = fun x => (a x * b x) * star (b x) := by
    funext x
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    simp
  have hmeas : AEStronglyMeasurable a μ := by
    rw [hfun]
    exact hi.1.mul hb.star
  refine hi.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hb1, mul_one]

theorem vanish_abs {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] (e : X → X → ℂ)
    (he : ∀ z, Continuous fun v => e v z) (he' : ∀ v, Continuous fun z => e v z)
    (hen : ∀ a b, ‖e a b‖ = 1) (J : X → ℂ) (hJ : Integrable J μ) (N : Set X) (hN : IsOpen N)
    (hb : ∀ N' : Set X, IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : X → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, J v * e v z ∂μ) * Φ z ∂μ = 0) (z₀ : X) (hz : z₀ ∈ closure N) :
    ∫ v, J v * e v z₀ ∂μ = 0 := by
  have hbd : ∀ z, ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v‖ ∂μ := by
    intro z
    calc ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v * e v z‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ v, ‖J v‖ ∂μ := by
        congr 1
        ext v
        rw [norm_mul, hen, mul_one]
  have hFc : Continuous fun z => ∫ v, J v * e v z ∂μ := by
    refine continuous_of_dominated (F := fun z v => J v * e v z) (bound := fun v => ‖J v‖)
      (fun z => hJ.1.mul (he z).aestronglyMeasurable) (fun z => Filter.Eventually.of_forall
        fun v => by rw [norm_mul, hen, mul_one]) hJ.norm
      (Filter.Eventually.of_forall fun v => continuous_const.mul (he' v))
  set F : X → ℂ := fun z => ∫ v, J v * e v z ∂μ with hFdef
  have hzero : ∀ z₁ ∈ N, F z₁ = 0 := by
    intro z₁ hz₁
    by_contra hc
    set c := F z₁ with hcdef
    let G : X → ℝ := fun z => (starRingEnd ℂ c * F z).re
    have hGc : Continuous G := Complex.continuous_re.comp (continuous_const.mul hFc)
    have hG1 : 0 < G z₁ := by
      show 0 < (starRingEnd ℂ c * c).re
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hc
    have hN'o : IsOpen (N ∩ {z | 0 < G z}) := hN.inter (isOpen_lt continuous_const hGc)
    obtain ⟨Φ, hΦc, hΦi, hΦpos, hΦsupp, hΦ1, hint⟩ :=
      hb _ hN'o Set.inter_subset_left z₁ ⟨hz₁, hG1⟩
    have hint' : ∫ z, F z * Φ z ∂μ = 0 := hint
    have hFΦi : Integrable (fun z => F z * Φ z) μ := by
      refine Integrable.mono (hΦi.norm.const_mul (∫ v, ‖J v‖ ∂μ))
        (hFc.aestronglyMeasurable.mul hΦi.1) (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_norm,
        abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hbd z) (norm_nonneg _)
    let H : X → ℝ := fun z => (starRingEnd ℂ c * (F z * Φ z)).re
    have hHeq : ∀ z, H z = G z * (Φ z).re := by
      intro z
      simp only [H, G]
      rw [← mul_assoc, Complex.mul_re, (hΦpos z).2, mul_zero, sub_zero]
    have hHnn : ∀ z, 0 ≤ H z := by
      intro z
      rw [hHeq]
      by_cases hz : z ∈ N ∩ {z | 0 < G z}
      · exact mul_nonneg hz.2.le (hΦpos z).1
      · rw [hΦsupp z hz]
        simp
    have hHc : Continuous H := Complex.continuous_re.comp (continuous_const.mul (hFc.mul hΦc))
    have hHi : Integrable H μ := (hFΦi.const_mul (starRingEnd ℂ c)).re
    have hHpos : 0 < ∫ z, H z ∂μ := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hHnn z) hHi]
      apply hHc.isOpen_support.measure_pos μ
      refine ⟨z₁, ?_⟩
      rw [Function.mem_support, hHeq]
      exact (mul_pos hG1 hΦ1).ne'
    have hHzero : ∫ z, H z ∂μ = 0 := by
      have h : ∫ z, H z ∂μ = (∫ z, starRingEnd ℂ c * (F z * Φ z) ∂μ).re :=
        integral_re (hFΦi.const_mul _)
      rw [h, integral_const_mul, hint', mul_zero, Complex.zero_re]
    linarith
  exact closure_minimal (s := N) (t := {z | F z = 0})
    (fun z hz => hzero z hz) (isClosed_eq hFc continuous_const) hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorOfScaledIsometricIntertwiner
section
open Topology

namespace GlobalTheory.CompanionTheory.CompactOperators

theorem isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)

end GlobalTheory.CompanionTheory.CompactOperators
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
section
open MeasureTheory Topology Filter
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

variable {A : Type} [CommRing A]

structure IsFieldIdem (f : A) : Prop where
  idem : f * f = f
  ne : f ≠ 0
  inv : ∀ x, f * x ≠ 0 → ∃ y, f * x * y = f

structure IsFieldDec {ι : Type} [Fintype ι] (e : A) (f : ι → A) : Prop where
  field : ∀ i, IsFieldIdem (f i)
  orth : ∀ i j, i ≠ j → f i * f j = 0
  sum : ∑ i, f i = e

def NonDiscreteAt [TopologicalSpace A] (f : A) : Prop := ∀ V ∈ 𝓝 (0 : A), ∃ x ∈ V, x ≠ 0 ∧ f * x = x

def IsHaarMod [TopologicalSpace A] [MeasurableSpace A] (md : Aˣ →* ℝ≥0) : Prop :=
  ∀ h : Measure A, h.IsAddHaarMeasure → ∀ u : Aˣ, h.map (fun x => (u : A) * x) = ((md u : ℝ≥0∞))⁻¹ • h

abbrev Fx (A : Type) (m n : ℕ) : Type := Matrix (Fin m) (Fin n) A

variable {a r t : ℕ}

def yc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A r t := P z.1 * z.2

def vc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A a t := z.2 - z.1 * yc P z

def admitted (e : A) (P : Fx A a r → Fx A r a) : Set (Fx A a r × Fx A a t) :=
  {z | e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ P z.1 * z.1 = e • (1 : Fx A r r)}

def Piece (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A) : Set (Fx A a r × Fx A a t) :=
  {z | z ∈ admitted e P ∧ (∀ p q, z.1 p q ∈ C) ∧ (∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C) ∧
    (∀ p k, k ≠ i → vc P z p k ∈ C) ∧ (∀ p, (1 - f) * vc P z p i ∈ C) ∧
    ∃ c : Fin t → A, c i = 0 ∧ (∀ k, f * c k = c k ∧ c k ∈ C) ∧ ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k}

def gU (i : Fin t) (c₀ : Fin t → A) : Fx A t t := 1 + Matrix.of fun k j => if j = i then c₀ k else 0

def gD (i : Fin t) (u : A) : Fx A t t := Matrix.diagonal (Function.update 1 i u)

def yU (i : Fin t) (y₀ : Fin r → A) : Fx A r t := Matrix.of fun l j => if j = i then y₀ l else 0

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegment
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.ComplexAnalysis

theorem iteratedDeriv_zero_eq_of_eq_on_real_points (f g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ)) (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (h : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 := by

  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hreal : ∀ᶠ s : ℝ in 𝓝[≠] 0, f s = g s := by
    have hs : {s : ℝ | |s| < ρ} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hρ)
    exact Filter.mem_of_superset (nhdsWithin_le_nhds hs) fun s hs' => h s hs'
  have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := Complex.continuous_ofReal.tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := htend.frequently hreal.frequently
  have heq : Set.EqOn f g (Metric.ball 0 ρ) :=
    (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
      (convex_ball (0 : ℂ) ρ).isPreconnected h0 hfreq
  have hev : f =ᶠ[𝓝 0] g := Filter.mem_of_superset (hU.mem_nhds h0) heq
  exact hev.iteratedDeriv_eq r

end GlobalTheory.CompanionTheory.ComplexAnalysis
end

