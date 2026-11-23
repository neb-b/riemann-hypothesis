module

public import Formalism.HermitianCurvature.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits
section
open Filter Topology Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.MeanBoundsLimits

open Classical

open Formalism.FourierDecayAlt.crystallineComparison

section Mean

variable {Λ : Type} [AddCommGroup Λ] {LIM : (Λ → ℂ) → ℂ}

theorem bdd_const (c : ℂ) : Bdd (fun _ : Λ => c) := ⟨‖c‖, fun _ => le_rfl⟩

theorem lim_const (hM : IsMean LIM) (c : ℂ) : LIM (fun _ : Λ => c) = c := by
  have e : (fun _ : Λ => c) = c • (fun _ : Λ => (1 : ℂ)) := by funext; simp
  rw [e, hM.2.1 c _ (bdd_const 1), hM.2.2.2.1, mul_one]

theorem lim_real (hM : IsMean LIM) (q : Λ → ℂ) (B : ℝ) (hq : ∀ x, ‖q x‖ ≤ B)
    (hr : ∀ x, (q x).im = 0) : (LIM q).im = 0 ∧ (LIM q).re ≤ B := by
  have hqb : Bdd q := ⟨B, hq⟩
  have hre : ∀ x, |(q x).re| ≤ B := fun x => (Complex.abs_re_le_norm _).trans (hq x)
  have h1 := hM.2.2.1 (q + fun _ => (B : ℂ)) (Bdd_add hqb) (fun x => by
    simp only [Pi.add_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
      hr x, add_zero]
    exact ⟨by linarith [(abs_le.mp (hre x)).1], trivial⟩)
  rw [hM.1 _ _ hqb (bdd_const _), lim_const hM] at h1
  have hneg : Bdd ((-1 : ℂ) • q) := ⟨B, fun x => by simpa using hq x⟩
  have h2 := hM.2.2.1 ((fun _ => (B : ℂ)) + (-1 : ℂ) • q) (bdd_const_add hneg) (fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.ofReal_re,
      Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, hr x]
    norm_num
    linarith [(abs_le.mp (hre x)).2])
  rw [hM.1 _ _ (bdd_const _) hneg, lim_const hM, hM.2.1 _ _ hqb] at h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.add_re, Complex.ofReal_re] at h1 h2
  constructor
  · linarith [h1.2]
  · simp at h2; linarith [h2.1]
where
  Bdd_add {g : Λ → ℂ} (hg : Bdd g) : Bdd (g + fun _ => (B : ℂ)) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' hg (bdd_const _)
  bdd_const_add {g : Λ → ℂ} (hg : Bdd g) : Bdd ((fun _ => (B : ℂ)) + g) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_const _) hg

theorem meanBound_ok : MeanBound := by
  intro Λ _ LIM g B hM hg
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  set z := LIM g with hz
  by_cases z0 : z = 0
  · rw [z0, norm_zero]; exact hB
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z0
  set u : ℂ := starRingEnd ℂ z / ‖z‖ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self]
    exact norm_ne_zero_iff.mpr z0
  have hgb : Bdd g := ⟨B, hg⟩
  set h := u • g with hh
  have hhb : ∀ x, ‖h x‖ ≤ B := fun x => by
    simp only [hh, Pi.smul_apply, smul_eq_mul, norm_mul, hu1, one_mul]; exact hg x
  have hLh : LIM h = ‖z‖ := by
    rw [hh, hM.2.1 u g hgb, ← hz, hu, div_mul_eq_mul_div, Complex.conj_mul', pow_two,
      mul_div_assoc, div_self hn, mul_one]
  set hr : Λ → ℂ := fun x => ((h x).re : ℂ)
  set hi : Λ → ℂ := fun x => ((h x).im : ℂ)
  have hrb : ∀ x, ‖hr x‖ ≤ B := fun x => by
    simp only [hr, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hhb x)
  have hib : ∀ x, ‖hi x‖ ≤ B := fun x => by
    simp only [hi, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hhb x)
  have hsplit : h = hr + Complex.I • hi := by
    funext x; simp only [hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im (h x)).symm
  have hL := congrArg LIM hsplit
  rw [hM.1 _ _ ⟨B, hrb⟩ (Formalism.FourierDecayAlt.P.E2.bdd_smul' _ ⟨B, hib⟩), hM.2.1 _ _ ⟨B, hib⟩, hLh] at hL
  have R := lim_real hM hr B hrb (fun x => by simp [hr])
  have I := lim_real hM hi B hib (fun x => by simp [hi])
  have := congrArg Complex.re hL
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, I.1, zero_sub, neg_zero, add_zero] at this
  linarith [R.2]

end Mean

theorem bdd_inner {f : ℕ} {Λ : AddSubgroup (V f)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (p q : V f → H) (B : ℝ) (hp : ∀ x, ‖p x‖ ≤ B) (hq : ∀ x, ‖q x‖ ≤ B)
    (σ : V f) : Bdd (fun x : Λ => inner ℂ (p x) (q ((x : V f) + σ))) :=
  ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hp _) (hq _) (norm_nonneg _) ((norm_nonneg _).trans (hp x)))⟩

theorem lim_of_tendsto {f : ℕ} {Λ : AddSubgroup (V f)} {LIM : (Λ → ℂ) → ℂ}
    (hM : IsMeanInf Λ LIM) (F : V f → ℂ) (L : ℂ) (hF : Bdd (fun x : Λ => F x))
    (ht : Tendsto F (atInfAll f) (𝓝 L)) : LIM (fun x : Λ => F x) = L := by
  have hD : Bdd (fun x : Λ => F x - L) := by
    obtain ⟨b, hb⟩ := hF
    exact ⟨b + ‖L‖, fun x => (norm_sub_le _ _).trans (by linarith [hb x])⟩
  have h0 : LIM (fun x : Λ => F x - L) = 0 := by
    apply hM.2 _ hD
    have := (ht.comp (tendsto_comap (f := fun x : Λ => (x : V f)))).sub_const L
    simpa [Function.comp_def] using this
  have e : (fun x : Λ => F x) = (fun x : Λ => F x - L) + (fun _ => L) := by funext; simp
  rw [e, hM.1.1 _ _ hD (bdd_const L), h0, lim_const hM.1, zero_add]

theorem meanSplit_ok : MeanSplit := by
  intro f Λ LIM H _ _ a r Nh B hM hb haa har hra
  have hpa : ∀ x, ‖a x‖ ≤ B := fun x => (hb x).1
  have hpr : ∀ x, ‖r x‖ ≤ B := fun x => (hb x).2
  constructor
  · intro σ hσ
    have e : (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        (fun x : Λ => inner ℂ (a x) (a ((x : V f) + σ))) +
        (fun x : Λ => inner ℂ (a x) (r ((x : V f) + σ))) +
        ((fun x : Λ => inner ℂ (r x) (a ((x : V f) + σ))) +
         (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) := by
      funext x; simp only [Pi.add_apply, inner_add_left, inner_add_right]; ring
    rw [e, hM.1.1 _ _ (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ))
        (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ)),
      hM.1.1 _ _ (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ),
      hM.1.1 _ _ (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (a (x + σ))) (Nh σ) (bdd_inner a a B hpa hpa σ)
        (haa σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (r (x + σ))) 0 (bdd_inner a r B hpa hpr σ)
        (har σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (r x) (a (x + σ))) 0 (bdd_inner r a B hpr hpa σ)
        (hra σ hσ)]
    ring
  · intro S c hS
    have hS' : ∀ σ ∈ S, σ ∈ Λ := hS
    have hpd := Formalism.FourierDecayAlt.P.mean_matrix_posDef Λ H LIM hM.1.1 hM.1.2.1
      (fun g hg hpos => (hM.1.2.2.1 g hg hpos).1) hM.1.2.2.2.2 (fun x => r x) B (fun x => hpr x)
      (S.subtype (fun x => x ∈ Λ)) (fun σ => c σ)
    have eq : (∑ σ ∈ S, ∑ σ' ∈ S, (LIM fun x : Λ => inner ℂ (r x) (r ((x : V f) + (σ - σ')))) *
        c σ * starRingEnd ℂ (c σ')) =
        ∑ σ ∈ S.subtype (fun x => x ∈ Λ), ∑ σ' ∈ S.subtype (fun x => x ∈ Λ),
          (LIM fun x : Λ => inner ℂ (r x) (r ((x + (σ - σ') : Λ) : V f))) * c σ *
            starRingEnd ℂ (c σ') := by
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub]
    beta_reduce
    rw [eq]
    exact hpd

end Formalism.FourierDecayAlt.P.MeanBoundsLimits

theorem Formalism.FourierDecayAlt.P.mean_bound_estimate : Formalism.FourierDecayAlt.crystallineComparison.MeanBound := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanBound_ok
theorem Formalism.FourierDecayAlt.P.mean_split_identity : Formalism.FourierDecayAlt.crystallineComparison.MeanSplit := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanSplit_ok
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
section
namespace Formalism.FourierDecayAlt.P.S6x1

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem conj_real (E : Type) [Field E] [NumberField E] [IsCMField E]
    (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)

theorem smul_mem_FI (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this

end Formalism.FourierDecayAlt.P.S6x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem unramRelative : Formalism.FourierDecayAlt.S6.UnramRelative := by
  intro E _ _ _ hU
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (maximalRealSubfield E)) (𝓞 E)
  unfold Unram at hU
  have h0 : (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
    rw [← hU]; exact differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    rw [hU] at h
    have h2 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) *
        (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
        1 * (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by rw [one_mul]; exact h.symm
    simpa using mul_right_cancel₀ h0 h2
  refine ⟨h1, fun g => ?_⟩
  unfold UnramAbove
  rw [h1, Ideal.isCoprime_iff_sup_eq]; simp

theorem degreeFacts_statement : Formalism.FourierDecayAlt.S6.DegreeFacts := by
  intro E _ _ _
  have h2 : finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h4 : 0 < finrank ℚ (maximalRealSubfield E) := finrank_pos
  rw [h2] at h3
  refine ⟨by unfold deg; omega, ?_, h4⟩
  have h5 := IsTotallyComplex.finrank E
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  unfold deg
  omega

theorem localAwayFromLevel : Formalism.FourierDecayAlt.S6.LocOrdinary := by
  intro E _ _ _ g k ν P hP hg
  have hg0 : (g : E) ≠ 0 := by
    intro h
    apply hg
    have : g = 0 := by exact_mod_cast h
    simp [this]
  have key : ∀ (k k' : ℤ) (t : E), t ∈ locAt E P (zsub E (idl E g k ν)) →
      t ∈ locAt E P (zsub E (idl E g k' ν)) := by
    intro k k' t
    rintro ⟨a, ha, h⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k' ≤ k + n := ⟨(k' - k).toNat, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k + n = k' + m := ⟨(k + n - k').toNat, by omega⟩
    refine ⟨(g : 𝓞 (maximalRealSubfield E)) ^ n * a,
      fun hh => (hP.mem_or_mem hh).elim (fun h' => hg (hP.mem_of_pow_mem _ h')) ha, ?_⟩
    change _ ∈ idl E g k ν at h
    show _ ∈ idl E g k' ν
    unfold idl at h ⊢
    rw [mul_comm, FractionalIdeal.mem_singleton_mul] at h ⊢
    obtain ⟨z, hz, hh⟩ := h
    refine ⟨(g : E) ^ m * z, ?_, ?_⟩
    · have := (dd E ^ ν : FI E).coeToSubmodule.smul_mem ((g : 𝓞 E) ^ m) hz
      rw [Algebra.smul_def] at this
      simpa using this
    · rw [map_mul, mul_assoc, hh, map_pow, map_natCast, ← mul_assoc, ← mul_assoc, ← zpow_natCast,
        ← zpow_natCast, ← zpow_add₀ hg0, ← zpow_add₀ hg0, add_comm (n : ℤ) k, hm]
  ext t
  exact ⟨key _ _ t, key _ _ t⟩

theorem localTwistedLattice : Formalism.FourierDecayAlt.S6.LocTw := by
  intro E _ _ _ A B s P hP t
  constructor
  · rintro ⟨a, ha, h⟩
    rw [mem_twLat] at h
    refine ⟨⟨a, ha, h.1⟩, ⟨a, ha, ?_⟩⟩
    have := h.2
    rw [map_mul, conj_real] at this
    show _ ∈ B
    convert this using 1; ring
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
    rw [mem_twLat]
    constructor
    · have := smul_mem_FI E A b _ h1
      rw [map_mul]; convert this using 1; ring
    · have := smul_mem_FI E B a _ h2
      rw [map_mul, map_mul, map_mul, conj_real, conj_real]; convert this using 1; ring

theorem scaledIdealNorm : Formalism.FourierDecayAlt.S6.NormIdl := by
  intro E _ _ _ g k ν hg
  have hdeg := degreeFacts_statement E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hrd : 0 < rd E := by
    unfold rd
    apply Real.rpow_pos_of_pos
    have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
    exact_mod_cast this
  have hD : ((|discr E| : ℤ) : ℝ) = rd E ^ (2 * deg E) := by
    unfold rd
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, hdeg.1]
    have : ((2 * deg E : ℕ) : ℝ) ≠ 0 := by
      have := hdeg.2.2
      positivity
    rw [inv_mul_cancel₀ this, Real.rpow_one]
  have h1 : FractionalIdeal.absNorm (dd E) = ((|discr E| : ℤ) : ℚ) := by
    unfold dd
    rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E, Nat.cast_natAbs]
  have h2 : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ k))
      = ((g : ℚ) ^ (2 * deg E)) ^ k := by
    rw [FractionalIdeal.absNorm_span_singleton,
      show (g : E) ^ k = algebraMap ℚ E ((g : ℚ) ^ k) by rw [map_zpow₀, map_natCast],
      Algebra.norm_algebraMap, hdeg.1, abs_of_nonneg (by positivity)]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  unfold idl
  rw [map_mul, map_zpow₀, h1, h2]
  push_cast
  have hD' : (|(discr E : ℝ)|) = rd E ^ (2 * deg E) := by rw [← hD]; push_cast; rfl
  rw [hD']
  have : (rd E ^ (2 * deg E)) ^ ν * ((g : ℝ) ^ (2 * deg E)) ^ k
      = (((g : ℝ) ^ k * rd E ^ ν) ^ deg E) ^ 2 := by
    rw [← zpow_natCast (rd E), ← zpow_natCast (g : ℝ), ← zpow_mul, ← zpow_mul, ← pow_mul, mul_pow,
      ← zpow_natCast (((g : ℝ) ^ k)), ← zpow_natCast ((rd E ^ ν)), ← zpow_mul, ← zpow_mul, mul_comm]
    congr 2 <;> (push_cast; ring)
  rw [this, Real.sqrt_sq (by positivity)]

theorem twistedLatticeBetween : Formalism.FourierDecayAlt.S6.Between := by
  intro E _ _ _ A B s hBA hB
  refine ⟨fun t ht => ?_, fun t ht => ((mem_twLat E A B s t).1 ht).1⟩
  rw [mem_twLat]
  refine ⟨hBA ht, ?_⟩
  have h1 : complexConj E t ∈ B := hB t ht
  have h2 : (-1 : E) ^ s * complexConj E t ∈ B := by
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · simpa using h1
    · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
  exact B.coeToSubmodule.sub_mem ht h2

theorem dualIdealEqLiftIdeal : Formalism.FourierDecayAlt.S6.IdealsMatch := by
  intro E _ _ _ g r i s
  refine ⟨?_, ?_, ?_⟩
  · unfold dualIdl liftIdl nuBlock; congr 1; ring
  · unfold dualIdl nuBlock; congr 1; ring
  · unfold nuBlock; ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RootPushforwardDensity
section
open MeasureTheory Set Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.NthRootMeasurability

open Formalism.FourierDecayAlt.crystallineComparison

theorem detC (d : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).det = ‖d‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

def zeta (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)

def R (s k : ℕ) (w : ℂ) : ℂ := zeta s ^ k * w ^ ((s : ℂ)⁻¹)

def A (s k : ℕ) : Set ℂ := {z | z ≠ 0 ∧ R s k (z ^ s) = z}

theorem measurable_R (s k : ℕ) : Measurable (R s k) := by
  unfold R; fun_prop

theorem measurableSet_A (s k : ℕ) : MeasurableSet (A s k) := by
  have h1 : MeasurableSet {z : ℂ | z ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
  have h2 : MeasurableSet {z : ℂ | R s k (z ^ s) = z} :=
    measurableSet_eq_fun ((measurable_R s k).comp (by fun_prop)) measurable_id
  exact h1.inter h2

theorem R_pow (s k : ℕ) (hs : s ≠ 0) (w : ℂ) : R s k w ^ s = w := by
  unfold R zeta
  rw [mul_pow, ← pow_mul, mul_comm k s, pow_mul, (Complex.isPrimitiveRoot_exp s hs).pow_eq_one,
    one_pow, one_mul, Complex.cpow_nat_inv_pow w hs]

theorem nthRoots_eq_R (s : ℕ) (hs : s ≠ 0) (w : ℂ) :
    nthRoots s w = (Multiset.range s).map (fun k => R s k w) :=
  (Complex.isPrimitiveRoot_exp s hs).nthRoots_eq (Complex.cpow_nat_inv_pow w hs)

theorem A_disjoint (s : ℕ) (hs : s ≠ 0) :
    Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (A s) := by
  intro j hj k hk hjk
  rw [Function.onFun, Set.disjoint_left]
  intro z hzj hzk
  apply hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  have e : zeta s ^ j * (z ^ s) ^ ((s : ℂ)⁻¹) = zeta s ^ k * (z ^ s) ^ ((s : ℂ)⁻¹) := by
    have := hzj.2.trans hzk.2.symm
    simpa [R] using this
  have hα : (z ^ s) ^ ((s : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have := hzj.2
    simp only [R, h0, mul_zero] at this
    exact hzj.1 this.symm
  exact (Complex.isPrimitiveRoot_exp s hs).pow_inj hj hk (mul_right_cancel₀ hα e)

theorem A_union (s : ℕ) (hs : s ≠ 0) : (⋃ k ∈ Finset.range s, A s k) = {0}ᶜ := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, A,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, hz, _⟩; exact hz
  · intro hz
    have hmem : z ∈ nthRoots s (z ^ s) := (mem_nthRoots (Nat.pos_of_ne_zero hs)).mpr rfl
    rw [nthRoots_eq_R s hs, Multiset.mem_map] at hmem
    obtain ⟨k, hk, hkz⟩ := hmem
    exact ⟨k, Multiset.mem_range.mp hk, hz, hkz⟩

theorem image_A (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    (fun z => u⁻¹ * z ^ s) '' A s k = {0}ᶜ := by
  ext c
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz, _⟩, rfl⟩
    exact mul_ne_zero (inv_ne_zero hu) (pow_ne_zero _ hz)
  · intro hc
    refine ⟨R s k (u * c), ⟨?_, ?_⟩, ?_⟩
    · intro h0
      have := R_pow s k hs (u * c)
      rw [h0, zero_pow hs] at this
      exact mul_ne_zero hu hc this.symm
    · rw [R_pow s k hs]
    · rw [R_pow s k hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem injOn_A (s k : ℕ) (u : ℂ) (hu : u ≠ 0) : InjOn (fun z => u⁻¹ * z ^ s) (A s k) := by
  intro z hz z' hz' e
  have e' : z ^ s = z' ^ s := mul_left_cancel₀ (inv_ne_zero hu) e
  rw [← hz.2, ← hz'.2, e']

end Formalism.FourierDecayAlt.P.NthRootMeasurability
end
end

