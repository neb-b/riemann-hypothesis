module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
public import Formalism.WindowSums.AnnihilatorPolynomials.Bundle0001
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

@[expose] public section

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open PowerSeries

theorem ramified_valuation_inequality : RamifiedValuationInequality := by
  intro O _ _ _ ℓ hℓ ϖ e hϖ he hass ε u hε hu b y t hb hby hmem
  have hℓpos : 0 < ℓ := hℓ.out.pos
  obtain ⟨v₀, hv₀⟩ := hass

  have hℓnu : ¬ IsUnit (ℓ : O) := by
    intro h
    have h1 : IsUnit (ϖ ^ e) := by rw [← hv₀]; exact h.mul v₀.isUnit
    exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h1)

  have hpow : ∀ k : ℕ, (ℓ : O) ^ k = ((v₀⁻¹ : Oˣ) : O) ^ k * ϖ ^ (e * k) := by
    intro k
    have : (ℓ : O) = ((v₀⁻¹ : Oˣ) : O) * ϖ ^ e := by
      rw [← hv₀, mul_comm (ℓ : O), ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, mul_pow, ← pow_mul]

  set i₀ := (b - 1) / ℓ with hi₀def
  have h1 : ℓ * i₀ ≤ b - 1 := Nat.mul_div_le (b - 1) ℓ
  have h2 : b - 1 < ℓ * (i₀ + 1) := Nat.lt_mul_div_succ (b - 1) hℓpos
  have hi₀b : ℓ * i₀ < b := by omega
  have hbi : b ≤ ℓ * (i₀ + 1) := by omega
  have hyb : b ≤ ℓ * y := by
    have : (b : ℝ) ≤ (ℓ : ℝ) * (y : ℝ) := by
      rw [div_le_iff₀ (by exact_mod_cast hℓpos)] at hby; linarith
    exact_mod_cast this
  have hi₀y : i₀ < y := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hi₀b hyb)

  let vv : ℕ → ℕ := fun i => (y.choose i).factorization ℓ
  let mm : ℕ → ℕ := fun i => ordCompl[ℓ] (y.choose i)
  have hmmU : ∀ i ∈ Finset.range (y + 1), IsUnit ((mm i : ℕ) : O) := by
    intro i hi
    have hle : i ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcop : Nat.Coprime ℓ (mm i) := Nat.coprime_ordCompl hℓ.out (Nat.choose_pos hle).ne'
    have hic : IsCoprime (ℓ : ℤ) (mm i : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, c, hac⟩ := hic
    have hac' : (a : O) * ℓ + (c : O) * (mm i : O) = 1 := by
      have := congrArg (Int.cast : ℤ → O) hac
      push_cast at this
      exact this
    have : IsUnit ((a : O) * ℓ + (c : O) * (mm i : O)) := by rw [hac']; exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hℓnu
    · exact isUnit_of_mul_isUnit_right h
  let mexp : ℕ → ℕ := fun i => vv i + (y - i)
  let w : ℕ → PowerSeries O := fun i =>
    C ((mm i : ℕ) : O) * ε ^ (y - i) * u ^ i * C (((v₀⁻¹ : Oˣ) : O) ^ mexp i)
  let ee : ℕ → ℕ := fun i => ℓ * i
  let ms : ℕ → ℕ := fun i => e * mexp i
  have hsum : (Formalism.WindowSums.p1 ℓ ε u) ^ y =
      ∑ i ∈ Finset.range (y + 1), w i * X ^ ee i * C (ϖ ^ ms i) := by
    unfold Formalism.WindowSums.p1
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hn : ((y.choose i : ℕ) : PowerSeries O) = C (ℓ : O) ^ vv i * C ((mm i : ℕ) : O) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (y.choose i) ℓ]
      rw [Nat.cast_mul, Nat.cast_pow, ← map_natCast (C (R := O)) ℓ,
        ← map_natCast (C (R := O)) (mm i)]
    have hC : C (ℓ : O) ^ vv i * C (ℓ : O) ^ (y - i) =
        C (((v₀⁻¹ : Oˣ) : O) ^ mexp i) * C (ϖ ^ ms i) := by
      rw [← pow_add, ← map_pow, ← map_mul, ← hpow]
    have : (u * X ^ ℓ) ^ i * (C (ℓ : O) * ε) ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)
        = (C (ℓ : O) ^ vv i * C (ℓ : O) ^ (y - i)) * (C ((mm i : ℕ) : O) * ε ^ (y - i) * u ^ i)
          * X ^ (ℓ * i) := by
      rw [hn, mul_pow, mul_pow, ← pow_mul]; ring
    rw [this, hC]
    simp only [w, ee]
    ring
  have hw : ∀ i ∈ Finset.range (y + 1), IsUnit (w i) := fun i hi =>
    ((((hmmU i hi).map C).mul (hε.pow _)).mul (hu.pow _)).mul
      (((v₀⁻¹).isUnit.pow _).map C)
  have hinj : Set.InjOn ee (Finset.range (y + 1) : Set ℕ) := fun a _ c _ h =>
    Nat.eq_of_mul_eq_mul_left hℓpos h
  have hmem' : (∑ i ∈ Finset.range (y + 1), w i * X ^ ee i * C (ϖ ^ ms i)) ∈
      Ideal.span {(X : PowerSeries O) ^ b, C (ϖ ^ t)} := by
    rw [← hsum, Set.pair_comm]; exact hmem
  have hterm := (Formalism.WindowSums.mem_span_iff_of_distinct_exponents O ϖ hϖ.ne_zero hϖ.not_isUnit (Finset.range (y + 1))
    w ee ms b t hw hinj).1 hmem' i₀ (Finset.mem_range.2 (by omega))
  have htm : t ≤ e * (vv i₀ + (y - i₀)) := by
    rcases hterm with h | h
    · exact absurd h (by simp only [ee]; omega)
    · exact h
  have hv : vv i₀ ≤ Nat.log ℓ y := Nat.factorization_choose_le_log
  have hlog : ((Nat.log ℓ y : ℕ) : ℝ) ≤ Real.logb ℓ y := Real.natLog_le_logb y ℓ
  have hbl : (b : ℝ) / (ℓ : ℝ) ≤ (i₀ : ℝ) + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hℓpos)]
    exact_mod_cast (by linarith [hbi] : b ≤ (i₀ + 1) * ℓ)
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hte : (t : ℝ) / (e : ℝ) ≤ ((vv i₀ + (y - i₀) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hepos]
    have : (t : ℝ) ≤ ((e * (vv i₀ + (y - i₀)) : ℕ) : ℝ) := by exact_mod_cast htm
    rw [Nat.cast_mul] at this
    linarith
  rw [Nat.cast_add, Nat.cast_sub hi₀y.le] at hte
  have hvR : (vv i₀ : ℝ) ≤ (Nat.log ℓ y : ℝ) := by exact_mod_cast hv
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Formalism.WachCohomologyFacts.PLenBound in
theorem submodule_generator_count : SubGen := by
  intro O _ _ _ M _ _ _ _ ℓ e F P h
  classical

  have hA : ∀ n : ℕ, Module.length O (O ⧸ Ideal.span {ℓ ^ n}) ≤
      (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    intro n
    induction n with
    | zero =>
      have : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) := by
        rw [pow_zero, Ideal.span_singleton_one]
        infer_instance
      simp [Module.length_eq_zero]
    | succ n ih =>
      have hle : Ideal.span {ℓ ^ (n + 1)} ≤ Ideal.span {ℓ ^ n} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ (Nat.le_succ n))
      let g : (O ⧸ Ideal.span {ℓ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ n}) :=
        Submodule.mapQ _ _ LinearMap.id (fun x hx => hle hx)
      have hg : Function.Surjective g := by
        intro y
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact ⟨Submodule.Quotient.mk a, rfl⟩

      let f0 : (O ⧸ Ideal.span {ℓ}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ (n + 1)}) :=
        (Ideal.span {ℓ}).liftQ (ℓ ^ n • (Ideal.span {ℓ ^ (n + 1)}).mkQ) (by
          intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
          rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
          exact ⟨c, by rw [smul_eq_mul]; ring⟩)
      have hf0 : ∀ x, f0 x ∈ LinearMap.ker g := by
        intro x
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.mem_ker]
        simp only [f0, g, Submodule.liftQ_apply, LinearMap.smul_apply, Submodule.mkQ_apply,
          map_smul, Submodule.mapQ_apply, LinearMap.id_apply]
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
        exact ⟨a, by rw [smul_eq_mul, mul_comm]⟩
      have hf1 : Function.Surjective (f0.codRestrict (LinearMap.ker g) hf0) := by
        rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [LinearMap.mem_ker] at hy
        have ha : a ∈ Ideal.span {ℓ ^ n} := (Submodule.Quotient.mk_eq_zero _).mp hy
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        apply Subtype.ext
        simp only [LinearMap.codRestrict_apply, f0, Submodule.liftQ_apply, LinearMap.smul_apply,
          Submodule.mkQ_apply]
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]
      have hker : Module.length O (LinearMap.ker g) ≤ Module.length O (O ⧸ Ideal.span {ℓ}) :=
        Module.length_le_of_surjective _ hf1
      rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
        (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)]
      calc Module.length O (LinearMap.ker g) + Module.length O (O ⧸ Ideal.span {ℓ ^ n})
          ≤ Module.length O (O ⧸ Ideal.span {ℓ}) +
              (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := add_le_add hker ih
        _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
          push_cast
          ring

  obtain ⟨k, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  have hk : k ≤ Module.finrank O M := by
    have h1 := Submodule.finrank_le F
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin] at h1
    exact h1
  set Q := P.comap F.subtype with hQ
  have hPF : ∀ y : F, ℓ ^ e • y ∈ Q := by
    intro y
    rw [hQ, Submodule.mem_comap, map_smul]
    exact h _ y.2

  let φ : Fin k → (O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := fun i =>
    (Ideal.span {ℓ ^ e}).liftQ (LinearMap.toSpanSingleton O (↥F ⧸ Q) (Q.mkQ (bF i))) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, mul_smul]
      exact Q.smul_mem c (hPF _))
  let ψ : (Fin k → O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := ∑ i, (φ i).comp (LinearMap.proj i)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨fun i => Submodule.Quotient.mk (bF.repr x i), ?_⟩
    have hx : (Submodule.Quotient.mk x : ↥F ⧸ Q) =
        ∑ i, bF.repr x i • Submodule.Quotient.mk (bF i) := by
      conv_lhs => rw [← bF.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    rw [hx]
    simp only [ψ, φ, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
  have hB : Module.length O (↥F ⧸ Q) ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
    calc Module.length O (↥F ⧸ Q) ≤ Module.length O (Fin k → O ⧸ Ideal.span {ℓ ^ e}) :=
          Module.length_le_of_surjective ψ hψ
      _ = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
          rw [Module.length_pi_of_fintype]
          simp
  calc Module.length O (↥F ⧸ Q)
      ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := hB
    _ ≤ (k : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) := by
        gcongr
        exact hA e
    _ ≤ ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
        push_cast
        rw [mul_assoc]
        gcongr

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Module

section Snake

variable {O : Type} [CommRing O]

theorem len_coker_add {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    [AddCommGroup C] [Module O C] (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (a : Module.End O A) (b : Module.End O B) (c : Module.End O C)
    (h1 : ∀ x, b (f x) = f (a x)) (h2 : ∀ y, c (g y) = g (b y)) (hc : Function.Injective c) :
    Module.length O (B ⧸ LinearMap.range b) =
      Module.length O (A ⧸ LinearMap.range a) + Module.length O (C ⧸ LinearMap.range c) := by
  have hF : LinearMap.range a ≤ (LinearMap.range b).comap f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, h1 x⟩
  have hG : LinearMap.range b ≤ (LinearMap.range c).comap g := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, h2 y⟩
  let F := Submodule.mapQ (LinearMap.range a) (LinearMap.range b) f hF
  let G := Submodule.mapQ (LinearMap.range b) (LinearMap.range c) g hG
  refine Module.length_eq_add_of_exact F G ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [F, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    have hgy : g y = 0 := by
      apply hc
      rw [h2, hy, hfg.apply_apply_eq_zero, map_zero]
    obtain ⟨z, rfl⟩ := (hfg y).1 hgy
    have : a z = x := hf (by rw [← h1, hy])
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, this⟩
  · intro w
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, rfl⟩ := hg w
    exact ⟨Submodule.Quotient.mk y, by simp [G]⟩
  · intro w
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [G, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨v, rfl⟩ := hg u
      have : g (y - b v) = 0 := by rw [map_sub, ← h2, hu, sub_self]
      obtain ⟨z, hz⟩ := (hfg _).1 this
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      simp only [F, Submodule.mapQ_apply, hz]
      rw [Submodule.Quotient.eq]
      exact ⟨-v, by simp⟩
    · rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      simp only [F, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.eq'] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨g t, ?_⟩
      rw [h2, ht, map_add (f := _), map_neg, hfg.apply_apply_eq_zero, neg_zero, zero_add]

end Snake

section Main

variable {O : Type} [CommRing O] [IsDomain O]

theorem sub_smul_one_injective {M : Type} [AddCommGroup M] [Module O M] [IsTorsionFree O M]
    (ℓ : O) (hℓ : ℓ ≠ 0) (q : Module.End O M) (n : ℕ) (hq : q ^ n = 0) :
    Function.Injective (q - ℓ • (1 : Module.End O M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : q x = ℓ • x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  have h2 : ∀ k : ℕ, (q ^ k) x = ℓ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h1, smul_smul, pow_succ]
  have h3 := h2 n
  rw [hq, LinearMap.zero_apply] at h3
  exact (smul_eq_zero.mp h3.symm).resolve_left (pow_ne_zero n hℓ)

theorem len_base (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
    (ℓ : O) :
    Module.length O (R ⧸ LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))) =
      (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  let e := (Module.finBasis O R).equivFun
  have hmap : (LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))).map
      (e : R →ₗ[O] (Fin (finrank O R) → O)) =
      Submodule.pi Set.univ (fun _ => Ideal.span {ℓ}) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      exact ⟨-(e y i), by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨_, ⟨e.symm (fun i => -c i), rfl⟩, ?_⟩
      ext i
      change e (((0 : Module.End O R) - ℓ • (1 : Module.End O R)) (e.symm fun i => -c i)) i = v i
      simp [← hc, mul_comm]
  rw [(Submodule.Quotient.equiv _ _ e hmap).length_eq, (Submodule.quotientPi _).length_eq,
    Module.length_pi_of_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem len_main [IsPrincipalIdealRing O] (ℓ : O) (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∀ (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
      (q : Module.End O R), q ^ (n + 1) = 0 →
      Module.length O (R ⧸ LinearMap.range (q - ℓ • (1 : Module.End O R))) =
        (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction n with
  | zero =>
    intro R _ _ _ _ q hq
    rw [zero_add, pow_one] at hq
    subst hq
    exact len_base R ℓ
  | succ n ih =>
    intro R _ _ _ _ q hq
    have hK : ∀ x ∈ LinearMap.ker q, q x ∈ LinearMap.ker q := fun x hx => by
      rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
    have hQ : ∀ x ∈ LinearMap.range q, q x ∈ LinearMap.range q :=
      fun x _ => LinearMap.mem_range_self q x
    let qK := q.restrict hK
    let qQ := q.restrict hQ
    have hqK : qK = 0 := by
      ext ⟨x, hx⟩
      simpa [qK] using hx
    have key : ∀ (k : ℕ) (x : LinearMap.range q), (((qQ ^ k) x : LinearMap.range q) : R) =
        (q ^ k) (x : R) := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ihk =>
        intro x
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
        rfl
    have hqQ : qQ ^ (n + 1) = 0 := by
      ext ⟨x, y, rfl⟩
      rw [key, LinearMap.zero_apply, Submodule.coe_zero, ← Module.End.mul_apply, ← pow_succ, hq,
        LinearMap.zero_apply]
    have hex : Function.Exact (LinearMap.ker q).subtype q.rangeRestrict :=
      LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])
    have hsn := len_coker_add (LinearMap.ker q).subtype q.rangeRestrict
      (LinearMap.ker q).injective_subtype q.surjective_rangeRestrict hex
      (qK - ℓ • (1 : Module.End O _)) (q - ℓ • (1 : Module.End O R))
      (qQ - ℓ • (1 : Module.End O _))
      (fun x => by simp [qK]) (fun y => by ext; simp [qQ])
      (sub_smul_one_injective ℓ hℓ qQ (n + 1) hqQ)
    rw [hsn, ih _ qK (by rw [hqK, zero_pow (Nat.succ_ne_zero _)]), ih _ qQ hqQ, ← add_mul,
      ← Nat.cast_add]
    congr 2
    have h1 := (LinearMap.ker q).finrank_quotient_add_finrank
    rw [LinearEquiv.finrank_eq q.quotKerEquivRange] at h1
    omega

end Main

theorem length_pi_zero_bound : LenPi0 := by
  intro O _ _ _ R _ _ _ _ ℓ hℓ q hq
  obtain ⟨n, hn⟩ := hq
  exact len_main ℓ hℓ n R q (by rw [pow_succ, hn, zero_mul])

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

