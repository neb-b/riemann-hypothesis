module

public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Formalism.FormalGroupLog.Statement

@[expose] public section

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
section
noncomputable section

universe u v

namespace Formalism.LT.FrobP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_sigma_le {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1)
    (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    first
      | exact pow_le_one₀ (norm_nonneg a) ha
      | exact pow_le_one q (norm_nonneg a) ha
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp.le) h2

def sigmaO {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1) :
    unitBall K →+* unitBall K :=
  (σ.comp (unitBall K).subtype).codRestrict (unitBall K)
    (fun x => norm_sigma_le hσ hp x.1 x.2)

theorem natCast_coe (p : ℕ) : (((p : unitBall K)) : K) = (p : K) := by
  first
    | exact map_natCast (unitBall K).subtype p
    | simp

theorem norm_le_of_mem_span {p : ℕ} (x : unitBall K)
    (hx : x ∈ Ideal.span {((p : ℕ) : unitBall K)}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hy : ‖(y : K)‖ ≤ 1 := y.2
  have e : ((y * ((p : ℕ) : unitBall K) : unitBall K) : K) = (y : K) * (p : K) := by
    rw [← natCast_coe p]
    rfl
  rw [e, norm_mul]
  calc ‖(y : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = ‖(p : K)‖ := one_mul _

theorem mem_span_of_norm_le {p : ℕ} (hp0 : (p : K) ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖(p : K)‖) : x ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
  have hy : ‖(x : K) / (p : K)‖ ≤ 1 := by
    rw [norm_div]
    first
      | exact div_le_one_of_le₀ hx (norm_nonneg _)
      | exact (div_le_one (norm_pos_iff.mpr hp0)).mpr hx
  refine Ideal.mem_span_singleton'.mpr ⟨⟨(x : K) / (p : K), hy⟩, ?_⟩
  apply Subtype.ext
  show (x : K) / (p : K) * ((p : unitBall K) : K) = (x : K)
  rw [natCast_coe, div_mul_cancel₀ _ hp0]

theorem natCast_nonunit {p : ℕ} (hp : ‖(p : K)‖ < 1) :
    ((p : ℕ) : unitBall K) ∈ nonunits (unitBall K) := by
  rw [mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  have h2 : (u : K) * (p : K) = 1 := by
    have h0 := congrArg Subtype.val hu'
    rw [← natCast_coe p]
    exact h0
  have hu1 : ‖(u : K)‖ ≤ 1 := u.2
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖(u : K)‖ * ‖(p : K)‖ ≤ ‖(p : K)‖ := by
    calc ‖(u : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _
  linarith

def liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries ι (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d A, hA d⟩

theorem map_liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries.map (unitBall K).subtype (liftO A hA) = A := by
  ext d
  rw [MvPowerSeries.coeff_map]
  rfl

theorem main {ι : Type v} (p h : ℕ) (hpr : p.Prime) (σ : K →+* K) (hp0 : (p : K) ≠ 0)
    (hp : ‖(p : K)‖ < 1) (hσ : IsFrobLift p (p ^ h) σ) (A : MvPowerSeries ι K)
    (hA : IntegralMv A) :
    DivByMv (p : K) (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero)
      (MvPowerSeries.map σ A)) := by
  classical
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI hchar : CharP (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p :=
    CharP.quotient (unitBall K) p (natCast_nonunit hp)
  haveI : ExpChar (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p := ExpChar.prime hpr
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have hkey : (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})).comp (sigmaO hσ hp)
      = (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h).comp
          (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    first
      | rw [Ideal.Quotient.eq]
      | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply mem_span_of_norm_le hp0
    first
      | exact hσ c.1 c.2
      | (push_cast; exact hσ c.1 c.2)
  have h1 : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h)
        (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) (liftO A hA)) := by
    ext d
    simp only [MvPowerSeries.coeff_map]
    exact RingHom.congr_fun hkey _
  have hmain : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
      ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) = 0 := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h1, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_iterateFrobenius_expand p hpr.ne_zero, sub_self]
  have hcoeffI : ∀ d, MvPowerSeries.coeff d ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
      (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
    intro d
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPowerSeries.coeff_map, hmain, map_zero]
  have h2 : MvPowerSeries.map (unitBall K).subtype (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map σ A := by
    ext d
    first
      | rfl
      | (simp only [MvPowerSeries.coeff_map]; rfl)
  have hsub : MvPowerSeries.map (unitBall K).subtype ((liftO A hA) ^ (p ^ h)
      - MvPowerSeries.expand (p ^ h) hq (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA)))
      = A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) (MvPowerSeries.map σ A) := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h2, map_liftO]
  intro d
  rw [← hsub, MvPowerSeries.coeff_map]
  exact norm_le_of_mem_span (p := p) _ (hcoeffI d)

end Formalism.LT.FrobP

namespace Formalism.LT

open Formalism.G

theorem FrobCongr_valid : Formalism.LT.FrobCongr.{u, v} := by
  intro K _ _ _ p q hq σ hset ι A hA
  obtain ⟨hpr, ⟨h, _, rfl⟩, hp, hσ⟩ := hset
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact FrobP.main p h hpr σ hp0 hp hσ A hA

end Formalism.LT
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd
section
noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.ExpP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_natCast_of_not_dvd {p m : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * m = 1 := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact ⟨Nat.gcdA p m, Nat.gcdB p m, by push_cast at h; linarith⟩
  have h1 : (1 : K) = (a : K) * (p : K) + (b : K) * (m : K) := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hle : (1 : ℝ) ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(a : K) * p + (b : K) * m‖ := by rw [← h1]
      _ ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := IsUltrametricDist.norm_add_le_max _ _
  have ha := IsUltrametricDist.norm_intCast_le_one K a
  have hb := IsUltrametricDist.norm_intCast_le_one K b
  rcases le_max_iff.1 hle with h | h
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (p : K), norm_nonneg (a : K)]
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (m : K), norm_nonneg (b : K)]

lemma norm_natCast_eq {p n : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(p : K)‖ ^ padicValNat p n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  haveI := Fact.mk hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hp.ne_zero) hm0, _root_.Nat.padicValNat_def, _root_.Nat.multiplicity_prime_pow, _root_.Nat.padicValNat_def,
    _root_.multiplicity_eq_zero_of_not_dvd hm, add_zero]
  push_cast
  rw [norm_mul, norm_pow, norm_natCast_of_not_dvd hp hp1 hm, mul_one]

end Formalism.LT.ExpP
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.NormSigmaLeOne
section
noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT

open Formalism.G

namespace InverseIntegralClassesKeyFacts

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

lemma norm_add_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma norm_sub_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  rw [sub_eq_add_neg]; exact norm_add_le_of ha (by simpa using hb)

lemma norm_sigma_le_one {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ 1 := (hσ a ha).trans hp1
  have h2 : ‖a ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have : σ a = (σ a - a ^ q) + a ^ q := by ring
  rw [this]; exact norm_add_le_of h1 h2

end InverseIntegralClassesKeyFacts

open InverseIntegralClassesKeyFacts

theorem FunEqSubst_of (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by
  intro K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hppos : 0 < ‖(p : K)‖ := norm_pos_iff.mpr hpne

  set fs : PowerSeries K := PowerSeries.map σ f with hfs
  set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg
  set β : MvPowerSeries ι K := MvPowerSeries.expand q hq (MvPowerSeries.map σ α) with hβ
  have hαS : PowerSeries.HasSubst α := HasSubst.of_constantCoeff_zero hα0
  have hαq0 : MvPowerSeries.constantCoeff (α ^ q) = 0 := by
    rw [map_pow, hα0, zero_pow hq]
  have hαqS : PowerSeries.HasSubst (α ^ q) := HasSubst.of_constantCoeff_zero hαq0
  have hmα0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ α) = 0 := by
    simp [hα0]
  have hmαS : PowerSeries.HasSubst (MvPowerSeries.map σ α) := HasSubst.of_constantCoeff_zero hmα0
  have hβ0 : MvPowerSeries.constantCoeff β = 0 := by
    rw [hβ, MvPowerSeries.constantCoeff_expand, hmα0]
  have hβS : PowerSeries.HasSubst β := HasSubst.of_constantCoeff_zero hβ0
  have hXqS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries K) ^ q) :=
    HasSubst.of_constantCoeff_zero' (by simp [hq])

  have hdec : f.subst α - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α))
      = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β) := by
    have e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) := by
      rw [hg]; abel
    have e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q) := by
      rw [PowerSeries.subst_comp_subst_apply hXqS hαS, PowerSeries.subst_pow hαS,
        PowerSeries.subst_X hαS]
    have e3 : MvPowerSeries.expand q hq (MvPowerSeries.map σ (f.subst α)) = fs.subst β := by
      rw [PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]
    have e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q) := by
      conv_lhs => rw [e1]
      rw [PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]
    rw [e3, e4, smul_sub]; abel

  have hXqI : IntegralPS ((PowerSeries.X : PowerSeries K) ^ q) := by
    intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hαqI : IntegralMv (α ^ q) := by
    have := h4 K ι _ α hXqI hα0 hαI
    rwa [PowerSeries.subst_pow hαS, PowerSeries.subst_X hαS] at this
  have hdiv : DivByMv (p : K) (α ^ q - β) := h7 K p q hq σ hS ι α hαI
  have hβI : IntegralMv β := by
    intro d
    have e : MvPowerSeries.coeff d β
        = MvPowerSeries.coeff d (α ^ q) - MvPowerSeries.coeff d (α ^ q - β) := by
      rw [map_sub]; ring
    rw [e]
    exact norm_sub_le_of (hαqI d) ((hdiv d).trans hp1')
  have hgI : IntegralMv (g.subst α) := h4 K ι g α hfT hα0 hαI

  have hbr : ∀ d, ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖ := by
    intro d
    rw [map_sub, PowerSeries.coeff_subst hαqS, PowerSeries.coeff_subst hβS,
      ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hαqS fs d)
        (PowerSeries.coeff_subst_finite hβS fs d)]
    apply norm_finsum_le (norm_nonneg _)
    intro n
    rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]
    obtain ⟨k, hkdvd, hk⟩ := h5 K p q σ hS f hf0 hfT n
    obtain ⟨m, rfl⟩ := hkdvd
    have hn : q ^ k * m = p ^ (h * k) * m := by rw [hqh, ← pow_mul]
    have hdiv' : DivByMv ((p : K) ^ 1) (α ^ q - β) := by simpa using hdiv
    have hc0 := h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d
    rw [← hn] at hc0
    have hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
      have h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hk
      have h' := norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hc : ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ := by
      refine hc0.trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' (Nat.le_mul_of_pos_left k hh)) (norm_nonneg _)
    calc ‖σ (coeff (q ^ k * m) f)‖ * ‖MvPowerSeries.coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖σ (coeff (q ^ k * m) f)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = (‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _

  unfold IsFunEqTypeMv
  rw [hdec]
  intro d
  rw [map_add (f := _), MvPowerSeries.coeff_smul]
  refine norm_add_le_of (hgI d) ?_
  rw [norm_mul, norm_inv]
  calc ‖(p : K)‖⁻¹ * ‖MvPowerSeries.coeff d (fs.subst (α ^ q) - fs.subst β)‖
      ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ := mul_le_mul_of_nonneg_left (hbr d) (inv_nonneg.mpr (norm_nonneg _))
    _ = 1 := inv_mul_cancel₀ hppos.ne'

end Formalism.LT
end
end

-- bundled from Formalism.TorsionNormIteration.InverseIntegralClasses.SolveExistsProof
section
noncomputable section

universe u v

namespace Formalism.LT.SolveP

open PowerSeries

theorem SolveExists_proof : Formalism.LT.SolveExists.{u, v} := by
  intro R _ ι _ f G hf0 hf1 hG0
  have hu : IsUnit (coeff 1 f) := by rw [hf1]; exact isUnit_one
  set g := f.substInvOfIsUnit hu with hg
  have hgS : HasSubst g := HasSubst.substInvOfIsUnit f hu
  have hGS : HasSubst G := HasSubst.of_constantCoeff_zero hG0
  refine ⟨g.subst G, ?_, ?_⟩
  · exact constantCoeff_subst_eq_zero hG0 g (constantCoeff_substInvOfIsUnit f hu)
  · rw [← subst_comp_subst_apply hgS hGS, subst_substInvOfIsUnit_right f hf0 hu, subst_X hGS]

end Formalism.LT.SolveP

theorem Formalism.LT.SolveExists_proof : Formalism.LT.SolveExists.{u, v} := Formalism.LT.SolveP.SolveExists_proof
end
end

