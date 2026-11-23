module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

private theorem sum_eq_sum_comp_of_eq_zero_of_forall_ne {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [AddCommMonoid M] (v : κ → ι) (hv : Function.Injective v) (f : ι → M)
    (hf : ∀ i, (∀ a, i ≠ v a) → f i = 0) :
    ∑ i, f i = ∑ a, f (v a) := by
  rw [← Finset.sum_image (f := f) (s := Finset.univ) (g := v) (fun a _ b _ h => hv h)]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hf i (fun a hia =>
    hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hia.symm⟩)))).symm

theorem gramOf_mul {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ) :
    gramOf hd (u * g) = gᴴ * gramOf hd u * g := by
  simp only [GlobalTheory.CompanionTheory.Ar.PB.gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem head_conj_mul {N : ℕ} {P : Type*} [Fintype P] (v : P → Fin N)
    (hv : Function.Injective v) (hdown : ∀ (i : Fin N) (c : P), (∀ a, i ≠ v a) → v c < i)
    (G b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) :
    (bᴴ * G * b).submatrix v v = (b.submatrix v v)ᴴ * G.submatrix v v * b.submatrix v v := by
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
    intro i hi
    rw [hb (hdown i p hi), star_zero, zero_mul]
  · intro j hj
    rw [hb (hdown j q hj), mul_zero]

theorem gramLog_inv (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧
    (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 →
      gramLog hd k (g * b) = gramLog hd k g +
        ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  constructor
  · intro h
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog, GlobalTheory.CompanionTheory.Ar.PB.gramHead]
    rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul, h, GlobalTheory.CompanionTheory.Ar.PB.gramOf]
  · intro hb hdet hM
    have hdown : ∀ (i : Fin N) (c : {a : Fin N // (a : ℕ) < k}),
        (∀ a : {a : Fin N // (a : ℕ) < k}, i ≠ a.val) → c.val < i := by
      intro i c hi
      have hik : ¬ (i : ℕ) < k := fun h => hi ⟨i, h⟩ rfl
      rw [Fin.lt_def]
      exact lt_of_lt_of_le c.2 (not_lt.mp hik)
    have hbk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).IsUpperTriangular :=
      fun i j hij => hb (Subtype.coe_lt_coe.mpr hij)
    have hdiag : ∀ i, b i i ≠ 0 := by
      intro i hi
      have h0 : b.det = 0 := by
        rw [Matrix.det_of_upperTriangular hb]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [h0] at hdet
      exact not_isUnit_zero hdet
    have hdetk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).det = ∏ a : {a : Fin N // (a : ℕ) < k}, b a a :=
      Matrix.det_of_upperTriangular hbk
    have hminor : GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b) =
        (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val)ᴴ *
          GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g *
            b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val := by
      simp only [GlobalTheory.CompanionTheory.Ar.PB.gramHead]
      rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul]
      exact GlobalTheory.CompanionTheory.Ar.PB.head_conj_mul Subtype.val
        Subtype.val_injective hdown _ b hb
    have hB0 : ∏ a : {a : Fin N // (a : ℕ) < k}, b a a ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun a _ => hdiag a)
    have hnorm : ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b)).det‖ =
        ‖∏ a : {a : Fin N // (a : ℕ) < k}, b a a‖ ^ 2 *
          ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g).det‖ := by
      rw [hminor, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetk, norm_mul,
        norm_mul, norm_star]
      ring
    have hsum : (∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) =
        ∑ a : {a : Fin N // (a : ℕ) < k}, Real.log ‖b a a‖ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun a => by simp) _
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog]
    rw [hnorm, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hB0)) (norm_ne_zero_iff.mpr hM),
      Real.log_pow, norm_prod, Real.log_prod (s := Finset.univ)
        (f := fun a : {a : Fin N // (a : ℕ) < k} => ‖b a a‖) (fun a _ => norm_ne_zero_iff.mpr (hdiag a)),
      hsum]
    push_cast
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfInverse
section
open Matrix

namespace GlobalTheory.CompanionTheory.Metric.UnitMinor

theorem det_mul_expand {K : Type*} [CommRing K] {a n : ℕ}
    (P : Matrix (Fin a) (Fin n) K) (Q : Matrix (Fin n) (Fin a) K) :
    (P * Q).det = ∑ J : Fin a → Fin n, (∏ l, P l (J l)) * (Q.submatrix J id).det :=
  _root_.Bl.general_b_fact.goal1 P Q

theorem mul_submatrix_castLE {Φ : Type*} [CommRing Φ] {n r a : ℕ} (ha : a ≤ r)
    (Fm : Matrix (Fin n) (Fin r) Φ) (U : Matrix (Fin r) (Fin r) Φ)
    (hU : U.BlockTriangular id) {m : Type*} (J : m → Fin n) :
    (Fm * U).submatrix J (Fin.castLE ha) =
      Fm.submatrix J (Fin.castLE ha) * U.submatrix (Fin.castLE ha) (Fin.castLE ha) := by
  ext x y
  have hinj : Function.Injective (Fin.castLE ha) := Fin.castLE_injective ha
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  have e : ∑ j, Fm.submatrix J (Fin.castLE ha) x j *
        U.submatrix (Fin.castLE ha) (Fin.castLE ha) j y =
      ∑ k ∈ Finset.univ.map ⟨Fin.castLE ha, hinj⟩,
        Fm (J x) k * U k (Fin.castLE ha y) := by
    rw [Finset.sum_map]
    rfl
  rw [e]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro k _ hk
  have hka : a ≤ k.val := by
    by_contra hlt
    push_neg at hlt
    exact hk (Finset.mem_map.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, by ext; simp⟩)
  have : U k (Fin.castLE ha y) = 0 := by
    apply hU
    show Fin.castLE ha y < k
    rw [Fin.lt_def]
    simp only [Fin.val_castLE]
    exact lt_of_lt_of_le y.isLt hka
  rw [this, mul_zero]

theorem det_castLE_triangular {Φ : Type*} [CommRing Φ] {r a : ℕ} (ha : a ≤ r)
    (U : Matrix (Fin r) (Fin r) Φ) (hU : U.BlockTriangular id) :
    (U.submatrix (Fin.castLE ha) (Fin.castLE ha)).det =
      ∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l) := by
  have : (U.submatrix (Fin.castLE ha) (Fin.castLE ha)).BlockTriangular id := by
    intro x y hxy
    apply hU
    show Fin.castLE ha y < Fin.castLE ha x
    show y.val < x.val
    exact hxy
  rw [Matrix.det_of_upperTriangular this]
  rfl

theorem det_mem_subring {Φ : Type*} [CommRing Φ] (R : Subring Φ) {a : ℕ}
    (M : Matrix (Fin a) (Fin a) Φ) (hM : ∀ i j, M i j ∈ R) : M.det ∈ R := by
  rw [Matrix.det_apply']
  refine R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hM _ _)

theorem unit_minor : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (n r : ℕ) (Fm : Matrix (Fin n) (Fin r) Φ) (U : Matrix (Fin r) (Fin r) Φ) (C : Matrix (Fin r) (Fin n) Φ) (X : Φ), U.BlockTriangular id → (∀ a b, (Fm * U) a b / X ∈ R) → (∀ a b, C a b ∈ R) → (∀ a b, ∑ k, C a k * ((Fm * U) k b / X) = if a = b then 1 else 0) → ∀ (a : ℕ) (ha : a ≤ r) (J₀ : Fin a → Fin n), (Fm.submatrix J₀ (Fin.castLE ha)).det ≠ 0 → (∀ J : Fin a → Fin n, (Fm.submatrix J (Fin.castLE ha)).det / (Fm.submatrix J₀ (Fin.castLE ha)).det ∈ R) → (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ∈ R ∧ ((∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a)⁻¹ ∈ R ∧ (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ≠ 0 := by
  intro Φ _ R n r Fm U C X hU hB hC hCB a ha J₀ hD0 hratio
  set u : Φ := ∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l) with hu
  set D : (Fin a → Fin n) → Φ := fun J => (Fm.submatrix J (Fin.castLE ha)).det with hD
  set w : Φ := u * D J₀ / X ^ a with hw

  let B : Matrix (Fin n) (Fin r) Φ := X⁻¹ • (Fm * U)
  have hBent : ∀ k b, B k b = (Fm * U) k b / X := by
    intro k b
    simp [B, div_eq_inv_mul]
  have hminor : ∀ J : Fin a → Fin n,
      ((B.submatrix id (Fin.castLE ha)).submatrix J id).det = u * D J / X ^ a := by
    intro J
    have e : (B.submatrix id (Fin.castLE ha)).submatrix J id
        = X⁻¹ • (Fm.submatrix J (Fin.castLE ha) *
            U.submatrix (Fin.castLE ha) (Fin.castLE ha)) := by
      rw [← mul_submatrix_castLE ha Fm U hU J]
      ext x y
      simp [B]
    rw [e, Matrix.det_smul, Matrix.det_mul, det_castLE_triangular ha U hU]
    simp only [Fintype.card_fin, inv_pow, hD]
    rw [div_eq_inv_mul, mul_comm u]
  have hwR : w ∈ R := by
    have : w = ((B.submatrix id (Fin.castLE ha)).submatrix J₀ id).det := (hminor J₀).symm
    rw [this]
    refine det_mem_subring R _ fun i j => ?_
    simp only [Matrix.submatrix_apply, id]
    rw [hBent]
    exact hB _ _
  have hprod : (C.submatrix (Fin.castLE ha) id) * (B.submatrix id (Fin.castLE ha)) = 1 := by
    ext x y
    have e : ∀ j, (C.submatrix (Fin.castLE ha) id) x j * (B.submatrix id (Fin.castLE ha)) j y
        = C (Fin.castLE ha x) j * ((Fm * U) j (Fin.castLE ha y) / X) := fun j => by
      rw [← hBent]
      rfl
    rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_congr rfl (fun j _ => e j), hCB]
    simp only [(Fin.castLE_injective ha).eq_iff]
  set ρ : Φ := ∑ J : Fin a → Fin n, (∏ l, C (Fin.castLE ha l) (J l)) * (D J / D J₀) with hρ
  have hρR : ρ ∈ R :=
    R.sum_mem fun J _ => R.mul_mem (R.prod_mem fun l _ => hC _ _) (hratio J)
  have hone : w * ρ = 1 := by
    have h1 := det_mul_expand (C.submatrix (Fin.castLE ha) id) (B.submatrix id (Fin.castLE ha))
    rw [hprod, Matrix.det_one] at h1
    rw [h1, hρ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hminor J]
    simp only [Matrix.submatrix_apply, id]
    have hne : D J₀ ≠ 0 := hD0
    rw [hw]
    field_simp
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hone
  refine ⟨hwR, ?_, hw0⟩
  have : w⁻¹ = ρ := by
    rw [← mul_one w⁻¹, ← hone, inv_mul_cancel_left₀ hw0]
  rw [this]
  exact hρR

end GlobalTheory.CompanionTheory.Metric.UnitMinor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmooth
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth

theorem contDiffOn_pker {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℝ => pker ρ q.1 q.2)
      (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ)) := by
  have hc : ContDiff ℝ ∞ (fun q : ℂ × ℝ => circleMap 0 ρ q.2) := (contDiff_circleMap 0 ρ).comp contDiff_snd
  have e : (fun q : ℂ × ℝ => pker ρ q.1 q.2) =
      (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0‖ ^ 2 - ‖q.1 - 0‖ ^ 2) /
        (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0 - (q.1 - 0)‖ ^ 2) := by
    funext q
    simp only [pker, poissonKernel_def, Pi.div_apply]
  rw [e]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (((contDiff_norm_sq ℝ).comp (hc.sub contDiff_const)).sub
      ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const))).contDiffOn
  · exact ((contDiff_norm_sq ℝ).comp ((hc.sub contDiff_const).sub (contDiff_fst.sub contDiff_const))).contDiffOn
  · rintro ⟨w, t⟩ ⟨hw, -⟩
    have hw' : ‖w‖ < ρ := mem_ball_zero_iff.mp hw
    have hne : circleMap 0 ρ t - 0 - (w - 0) ≠ 0 := by
      intro h0
      have h1 : circleMap 0 ρ t = w := by simpa [sub_eq_zero] using h0
      have hn := norm_circleMap_zero ρ t
      rw [h1, abs_of_pos hρ] at hn
      linarith
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

theorem contDiffOn_prod_pker {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i))
      (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
  have hmaps : ∀ i : Fin n, Set.MapsTo (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))
      (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ)) := by
    rintro i ⟨z, θ⟩ ⟨hz, -⟩
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    rw [mem_ball_zero_iff] at hz ⊢
    exact lt_of_le_of_lt (norm_le_pi_norm z i) hz
  have hlin : ∀ i : Fin n, ContDiff ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i)) := fun i =>
    ((contDiff_apply ℝ (fun _ => ℂ) i).comp contDiff_fst).prodMk ((contDiff_apply ℝ (fun _ => ℝ) i).comp contDiff_snd)
  have hcomp : ∀ i : Fin n, ContDiffOn ℝ ∞
      ((fun q : ℂ × ℝ => pker ρ q.1 q.2) ∘ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
    fun i => (contDiffOn_pker hρ).comp (hlin i).contDiffOn (hmaps i)
  have hi : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => pker ρ (q.1 i) (q.2 i)) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
    hcomp
  exact contDiffOn_prod (fun i _ => hi i)

theorem ae_mem_box (n : ℕ) :
    ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), ∀ i, θ i ∈ Set.Ioc 0 (2 * Real.pi) := by
  have h1 : ∀ᵐ t ∂angMeas, t ∈ Set.Ioc 0 (2 * Real.pi) :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Ioc)
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually h1

private theorem contDiffOn_integral_angMeas {n : ℕ} {ρ : ℝ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    ∀ (k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (G : (Fin n → ℂ) × (Fin n → ℝ) → E),
      ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) →
      ContDiffOn ℝ k (fun z => ∫ θ, g θ • G (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas)) (Metric.ball (0 : Fin n → ℂ) ρ) := by
  have hopen : IsOpen (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := Metric.isOpen_ball.prod isOpen_univ
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hbox : ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), θ ∈ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi) := by
    filter_upwards [ae_mem_box n] with θ hθ
    exact fun i _ => Set.Ioc_subset_Icc_self (hθ i)
  obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (G : (Fin n → ℂ) × (Fin n → ℝ) → E), ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) →
      ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ,
        HasFDerivAt (fun z => ∫ θ, g θ • G (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas))
          (∫ θ, g θ • (fderiv ℝ G (z₀, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ)) ∂(Measure.pi fun _ : Fin n => angMeas)) z₀ := by
    intro E _ _ _ G hG z₀ hz₀
    have hGd := (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG
    have hz₀' : ‖z₀‖ < ρ := mem_ball_zero_iff.mp hz₀
    obtain ⟨r, hr, hrdef⟩ : ∃ r : ℝ, 0 < r ∧ r = (ρ - ‖z₀‖) / 2 := ⟨_, by linarith, rfl⟩
    have hsub : Metric.closedBall z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball_zero_iff]
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ < ρ := by linarith
    have hSK : IsCompact (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      (isCompact_closedBall z₀ r).prod hK
    have hSsub : (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) ⊆ Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)) :=
      Set.prod_mono hsub (Set.subset_univ _)
    have hGc : ContinuousOn G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := hG.continuousOn
    have hG'c : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
      hGd.2.continuousOn.clm_comp continuousOn_const
    obtain ⟨C, hC⟩ := hSK.exists_bound_of_continuousOn (hG'c.mono hSsub)
    obtain ⟨C0, hC0⟩ := hSK.exists_bound_of_continuousOn (hGc.mono hSsub)
    have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, Continuous fun θ => g θ • G (z, θ) := fun z hz =>
      hg.smul (hGc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))
    have hslice' : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ,
        Continuous fun θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ)) := fun z hz =>
      hg.smul (hG'c.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))
    have hball : Metric.ball z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ := Metric.ball_subset_closedBall.trans hsub
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z θ => g θ • G (z, θ))
      (F' := fun z θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (bound := fun _ => Cg * C)
      (Metric.ball_mem_nhds z₀ hr) ?_ ?_ ?_ ?_ (integrable_const _) ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
      exact (hslice z hz).aestronglyMeasurable
    · refine Integrable.mono' (integrable_const (Cg * C0)) (hslice z₀ hz₀).aestronglyMeasurable ?_
      filter_upwards [hbox] with θ hθ
      show ‖g θ • G (z₀, θ)‖ ≤ Cg * C0
      rw [norm_smul]
      exact mul_le_mul (hCg θ hθ) (hC0 (z₀, θ) (Set.mk_mem_prod (Metric.mem_closedBall_self hr.le) hθ))
        (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))
    · exact (hslice' z₀ hz₀).aestronglyMeasurable
    · filter_upwards [hbox] with θ hθ z hz
      show ‖g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))‖ ≤ Cg * C
      rw [norm_smul]
      exact mul_le_mul (hCg θ hθ) (hC (z, θ) (Set.mk_mem_prod (Metric.ball_subset_closedBall hz) hθ))
        (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))
    · filter_upwards with θ z hz
      have hz' : z ∈ Metric.ball (0 : Fin n → ℂ) ρ := hball hz
      have hd : DifferentiableAt ℝ G (z, θ) :=
        hGd.1.differentiableAt (hopen.mem_nhds (Set.mk_mem_prod hz' (Set.mem_univ θ)))
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left z θ)).const_smul (g θ)
  intro k
  induction k with
  | zero =>
    intro E _ _ _ G hG
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun z hz => (key E G hG z hz).continuousAt.continuousWithinAt
  | succ k ih =>
    intro E _ _ _ G hG
    have hGd := (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG
    have hG' : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
      hGd.2.clm_comp contDiffOn_const
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
      ⟨fun z hz => (key E G hG z hz).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    exact (ih _ _ hG').congr fun z hz => (key E G hG z hz).fderiv

theorem contDiffOn_polyPoisson :
    ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ →
      Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) →
      ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  intro n ρ h hρ hh
  have e : polyPoisson ρ h = fun z => ∫ θ, h (torusPt ρ θ) •
      (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i)) (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas) := by
    funext z
    show (∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)) = _
    congr 1
    funext θ
    rw [smul_eq_mul, mul_comm]
  rw [e, contDiffOn_infty]
  intro k
  exact contDiffOn_integral_angMeas _ hh k ℝ _ (contDiffOn_prod_pker hρ)

end GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionTensorPullbackRingHomBijective
section
open Set Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_const_of_section_mem_range : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → IsPreconnected B → B.Nonempty → ∀ (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) (s : (Fin n → ℂ) → (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → DifferentiableOn ℂ s B → (∀ b ∈ B, s b ∈ (P b).range) → ∃ x : Λ, ∀ b ∈ B, s b = P b x := by
  intro n g Λ _ _ B hB hpc hne P s hP hs hrange
  haveI : Nonempty B := hne.to_subtype
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  haveI : BaireSpace B := BaireSpace.of_t2Space_locallyCompactSpace
  have hclosed : ∀ x : Λ, IsClosed {b : B | s b = P b x} := fun x =>
    isClosed_eq hs.continuousOn.restrict (hP x).continuousOn.restrict
  have hunion : (⋃ x : Λ, {b : B | s b = P b x}) = univ := by
    refine eq_univ_of_forall fun b => ?_
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (hrange b b.2)
    exact mem_iUnion.mpr ⟨x, hx.symm⟩
  obtain ⟨x, b₀, hb₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hunion
  refine ⟨x, ?_⟩
  have hopen : IsOpen ((Subtype.val : B → Fin n → ℂ) '' interior {b : B | s b = P b x}) :=
    hB.isOpenMap_subtype_val _ isOpen_interior
  have hev : (fun b => s b - P b x) =ᶠ[𝓝 (b₀ : Fin n → ℂ)] 0 := by
    filter_upwards [hopen.mem_nhds ⟨b₀, hb₀, rfl⟩]
    rintro _ ⟨c, hc, rfl⟩
    have hmem : c ∈ {b : B | s b = P b x} := interior_subset hc
    have hc' : s c = P c x := hmem
    show s c - P c x = 0
    exact sub_eq_zero.mpr hc'
  have han : AnalyticOnNhd ℂ (fun b => s b - P b x) B :=
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hB (hs.sub (hP x))
  intro b hb
  have h0 : s b - P b x = 0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc b₀.2 hev hb
  exact sub_eq_zero.mp h0

end GlobalTheory.CompanionTheory.Ar.Flat
end

