module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElements
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeltaPowQExpansionIffLaurentSeries
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem laurent_exp_shift (M : ℕ) (hM : 0 < M) (w : ℕ) (k : ℤ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * ((k - (w * M : ℕ) : ℤ) : ℂ) * τ / M) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem laurent_qAll_int (E : Subring ℂ) (M : ℕ) (hM : 0 < M) (f : ℍ → ℂ) (c : ℕ → ℤ)
    (h : HasQ 1 f fun n => (c n : ℂ)) : QAll (· ∈ E) M f :=
  QAll.of_dvd hM (one_dvd M) E.zero_mem ⟨_, h, fun n => intCast_mem E (c n)⟩

theorem laurent_iff : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  intro E M φ hM
  obtain ⟨⟨cD, -, hD⟩, ⟨cI, -, hI⟩⟩ := _root_.GlobalTheory.FN.dd_div_q_and_q_div_dd
  obtain ⟨-, -, -, hmul, hpow, -⟩ := GlobalTheory.QFam.QAllSubring.ring_closed E M hM
  have hqD := laurent_qAll_int E M hM _ cD hD
  have hqI := laurent_qAll_int E M hM _ cI hI
  have hDD0 : ∀ τ : ℍ, DD τ ≠ 0 := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, hbE⟩ := hmul _ _ (hpow _ w hqI) hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    let c : ℤ → ℂ := fun n => if -((w * M : ℕ) : ℤ) ≤ n then b (n + ((w * M : ℕ) : ℤ)).toNat else 0
    refine ⟨c, -((w * M : ℕ) : ℤ), fun n => ?_, fun n hn => ?_, fun τ => ?_⟩
    · simp only [c]
      split_ifs
      · exact hbE _
      · exact E.zero_mem
    · simp only [c]
      rw [if_neg (not_le.mpr hn)]
    · rw [← hginj.hasSum_iff]
      · have h1 := (hb τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹
        have hφ : (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) ^ w * (DD τ ^ w * φ τ)) = φ τ := by
          rw [div_pow]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))),
            pow_ne_zero w (hDD0 τ)]
        rw [hφ] at h1
        have key : (fun k : ℕ => (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            (b k * Complex.exp (2 * Real.pi * Complex.I * k * τ / M))) =
            (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) ∘ g := by
          funext k
          simp only [Function.comp, g, c]
          rw [if_pos (by omega)]
          have hk : ((k : ℤ) - ((w * M : ℕ) : ℤ) + ((w * M : ℕ) : ℤ)).toNat = k := by omega
          rw [hk]
          have := laurent_exp_shift M hM w k τ
          rw [← Int.cast_natCast k, ← this]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
        rw [key] at h1
        exact h1
      · intro n hn
        have : ¬ (-((w * M : ℕ) : ℤ) ≤ n) := fun h => hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by
          simp only [g]; omega⟩
        simp only [c]
        rw [if_neg this, zero_mul]
  · rintro ⟨c, n₀, hcE, hc0, hs⟩
    refine ⟨(-n₀).toNat, ?_⟩
    set w := (-n₀).toNat with hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    have hwM : (w : ℤ) ≤ ((w * M : ℕ) : ℤ) := by
      have : w ≤ w * M := Nat.le_mul_of_pos_right w hM
      exact_mod_cast this
    have hq : HasQ M (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ) fun k => c (g k) := by
      intro τ
      have h1 := (hs τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)
      rw [← hginj.hasSum_iff] at h1
      · have key : (fun i : ℤ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / M))) ∘ g =
            fun k : ℕ => c (g k) * Complex.exp (2 * Real.pi * Complex.I * k * τ / M) := by
          funext k
          simp only [Function.comp, g]
          rw [mul_left_comm, laurent_exp_shift M hM w k τ]
          push_cast
          rfl
        rw [key] at h1
        exact h1
      · intro n hn
        have : n < n₀ := by
          by_contra hh
          exact hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by simp only [g]; omega⟩
        simp [hc0 n this]
    have hqE : QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ :=
      ⟨_, hq, fun k => hcE _⟩
    have h2 := hmul _ _ (hpow _ w hqD) hqE
    have key : (fun τ : ℍ => (DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) ^ w *
        (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ)) = fun τ => DD τ ^ w * φ τ := by
      funext τ
      rw [div_pow]
      field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
    rw [key] at h2
    exact h2

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsTowerLevelModIntegral
section
open GlobalTheory.K5 GlobalTheory.KumDlog Polynomial

noncomputable section
namespace GlobalTheory.LevDer

theorem int_div_of_mk {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] [CharZero Ω]
    (m : ℕ) (a : integralClosure (O0 p) Ω)
    (ha : Ideal.Quotient.mk (Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}) a = 0) :
    IsInt (p := p) ((a : Ω) / (p : Ω) ^ m) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  have hp : (p : Ω) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine int_congr c.2 ?_
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
  field_simp

theorem natCast_eq_pow {Ω : Type} [Field Ω] (N p k : ℕ) (h : N = p ^ (k + 1)) :
    (N : Ω) = (p : Ω) ^ (k + 1) := by
  subst h; push_cast; rfl


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_levDer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
    ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  intro p _ Ω _ _ hC T m hm
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  obtain ⟨ι, hι⟩ := Basic.exists_isEmb T m
  obtain ⟨hinj, hrange⟩ := _root_.GlobalTheory.K5.LevEmb.emb_inj_range p Ω hC T m hm ι hι
  have hιA : ∀ z, ι z ∈ integralClosure (O0 p) Ω := fun z =>
    Lev_int T m _ (hrange ▸ AlgHom.mem_range_self ι z)
  let ιA : On p m →ₐ[O0 p] integralClosure (O0 p) Ω := ι.codRestrict _ hιA
  have hιAv : ∀ z, ((ιA z : integralClosure (O0 p) Ω) : Ω) = ι z := fun z => rfl
  let I : Ideal (integralClosure (O0 p) Ω) := Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}
  letI : Algebra (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    ((Ideal.Quotient.mk I).comp ιA.toRingHom).toAlgebra
  have halg : ∀ z, algebraMap (On p m) (integralClosure (O0 p) Ω ⧸ I) z = Ideal.Quotient.mk I (ιA z) :=
    fun z => rfl
  haveI : IsScalarTower (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [halg, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]

  let g : Ω → On p m := Function.invFun ι
  have hg : ∀ x ∈ Lev T m, ι (g x) = x := fun x hx =>
    Function.invFun_eq ((AlgHom.mem_range ι).1 (hrange.symm ▸ hx))
  have hgm : ∀ x ∈ Lev T m, ∀ z, ι z = x → g x = z := fun x hx z hz =>
    hinj ((hg x hx).trans hz.symm)
  let lift : (integralClosure (O0 p) Ω ⧸ I) → integralClosure (O0 p) Ω :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ s, Ideal.Quotient.mk I (lift s) = s := Function.surjInv_eq _
  have hdiv := fun a ha => GlobalTheory.LevDer.int_div_of_mk (p := p) (Ω := Ω) m a ha

  have hF : ∀ D : Derivation (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I),
      IsDer (Lev T m) (fun x => ((lift (D (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ m) := by
    intro D
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
    · have e : g (x + y) = g x + g y :=
        hgm _ (add_mem hx hy) _ (by rw [map_add (f := _), hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x + y))) - lift (D (g x)) - lift (D (g y))) ?_) ?_
      · rw [map_sub (Ideal.Quotient.mk I), map_sub (Ideal.Quotient.mk I), hlift, hlift, hlift, e, map_add (f := _)]; ring
      · push_cast; ring
    · have e : g (x * y) = g x * g y :=
        hgm _ (mul_mem hx hy) _ (by rw [map_mul, hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x * y))) - ιA (g x) * lift (D (g y))
        - ιA (g y) * lift (D (g x))) ?_) ?_
      · rw [map_sub (Ideal.Quotient.mk I), map_sub (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), hlift, hlift, hlift, e, Derivation.leibniz,
          Algebra.smul_def, Algebra.smul_def, halg, halg]; ring
      · push_cast; rw [hιAv, hιAv, hg x hx, hg y hy]; ring
    · have e : g (algebraMap (O0 p) Ω c) = algebraMap (O0 p) (On p m) c :=
        hgm _ (Subalgebra.algebraMap_mem _ c) _ (ι.commutes c)
      refine hdiv _ ?_
      rw [hlift, e, Derivation.map_algebraMap]

  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (ppow_pos (p := p) 1))
  let u : integralClosure (O0 p) Ω := ⟨(p : Ω) / (T.ζ 1 - 1) ^ 1, hpd⟩
  have hz1 : T.ζ 1 - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt))
  have hpow : T.ζ (k + 1) ^ p ^ k = T.ζ 1 := by
    have := zeta_pow T 1 k; rwa [add_comm] at this
  have hxn : Ideal.Quotient.mk (towerIdeal p (k + 1)) (C X) = xn p (k + 1) := rfl
  have hyn : Ideal.Quotient.mk (towerIdeal p (k + 1)) X = yn p (k + 1) := rfl
  have hd := congrArg ι (DlogUniq.derivative_cyclotomic_mul p k)
  simp only [map_mul, map_sub, map_pow, map_natCast, map_one, hι.1, hpow] at hd
  have hxz : algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)
      (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1)) = 0 := by
    rw [← map_mul, halg, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA (xn p (k + 1)) ^ (p ^ (k + 1) - 1) * u * ιA (xn p (k + 1)), Subtype.ext ?_⟩
    have hp' : (p : Ω) = (T.ζ 1 - 1) * ((p : Ω) / (T.ζ 1 - 1) ^ 1) := by field_simp
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast, hι.1, u]
    linear_combination (-((p : Ω) / (T.ζ 1 - 1) ^ 1 * T.ζ (k + 1))) * hd -
      (ι (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) * T.ζ (k + 1)) * hp'
  obtain ⟨Dz, hzx, hzy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) (p ^ (k + 1))
    (qO p) (towerIdeal p (k + 1)) rfl (integralClosure (O0 p) Ω ⧸ I)
    (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1))) 0 hxz (mul_zero _)
  have hyq : ∀ N : ℕ, N = p ^ (k + 1) → (N : integralClosure (O0 p) Ω ⧸ I) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1)) = 0 := by
    intro N hN
    rw [← map_natCast (algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)) N, ← map_mul, halg,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA ((p : On p (k + 1)) * yn p (k + 1)), Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast]
    rw [natCast_eq_pow (Ω := Ω) N p k hN]
    ring
  obtain ⟨N, hN⟩ : ∃ N, N = p ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨Dq, hqx, hqy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) N
    (qO p) (towerIdeal p (k + 1)) (by rw [hN]; rfl) (integralClosure (O0 p) Ω ⧸ I)
    0 (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1))) (mul_zero _)
    (hyq N hN)
  rw [hxn] at hzx hqx
  rw [hyn] at hzy hqy
  have hgz : g (T.ζ (k + 1)) = xn p (k + 1) := hgm _ (zeta_mem_Lev T _) _ hι.1
  have hgq : g (T.qq (k + 1)) = yn p (k + 1) := hgm _ (qq_mem_Lev T _) _ hι.2
  refine ⟨fun x => ((lift (Dz (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    fun x => ((lift (Dq (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    hF Dz, hF Dq, ?_, ?_, ?_, ?_⟩
  · refine int_congr (hdiv (lift (Dz (xn p (k + 1))) - ιA ((p : On p (k + 1)) * xn p (k + 1))) ?_) ?_
    · rw [map_sub (Ideal.Quotient.mk I), hlift, hzx, halg, sub_self]
    · simp only [hgz, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.1]
      ring
  · exact int_congr (hdiv (lift (Dz (yn p (k + 1)))) (by rw [hlift, hzy])) (by simp only [hgq])
  · exact int_congr (hdiv (lift (Dq (xn p (k + 1)))) (by rw [hlift, hqx])) (by simp only [hgz])
  · refine int_congr (hdiv (lift (Dq (yn p (k + 1))) - ιA ((p : On p (k + 1)) * yn p (k + 1))) ?_) ?_
    · rw [map_sub (Ideal.Quotient.mk I), hlift, hqy, halg, sub_self]
    · simp only [hgq, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.2]
      ring

end GlobalTheory.LevDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTraceStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace : ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (W₁ W₂ : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W₁ ↔ algebraMap F L a ∈ W₂) → ∃ σ : L ≃ₐ[F] L, ∀ x : L, σ x ∈ W₂ ↔ x ∈ W₁ := by
  first | exact @GlobalTheory.KZ.ES.exists_conj_of_same_trace | exact GlobalTheory.KZ.ES.exists_conj_of_same_trace | (intros; apply GlobalTheory.KZ.ES.exists_conj_of_same_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruence
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem intCast_zmod_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {x y : ℤ} (hx : (x : ZMod K) = y) :
    (x : ZMod K₁) = y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

theorem mem_Gamma_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ CongruenceSubgroup.Gamma K₁ := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h4)

theorem mem_Gam_of_Gamma {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ Gam N l := by
  have h1 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hN hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hl hδ)
  show δ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
  exact Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N δ).mpr ⟨h1.1, h1.2.2.2, h1.2.2.1⟩,
    CongruenceSubgroup.Gamma0_mem.mpr h2.2.2.1⟩

theorem entries_eq_one_of_mem_Gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h1, h2, h3, h4]

theorem exists_coc_near : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ,
    IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)),
      IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  intro N l w hN hl hl2 hlN hw Φ hΦ n
  obtain ⟨hhom, hadd, hinv, -⟩ := hΦ
  obtain ⟨M₁, hM₁, hadd₁⟩ := hadd n
  obtain ⟨M₂, hM₂, hinv₂⟩ :=
    _root_.GlobalTheory.KZ.H3.unif_level N l (ZMod (l ^ n)) (Φ n) hN hl.pos ⟨M₁, hM₁, hadd₁⟩ (hinv n)
  obtain ⟨b, M', hlM', hMeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := M₁ * M₂) (Nat.mul_pos hM₁ hM₂).ne' l hl.one_lt.ne'
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · exact absurd (h ▸ dvd_zero l) hlM'
    · exact h
  obtain ⟨c, hcΓ, hcomm, hcneg⟩ := _root_.GlobalTheory.KZ.exists_scalar_mod_level N l (max b n) M' hN hl hl2 hlN hM'pos hlM'
  have hMK : M₁ * M₂ ∣ M' * N * l ^ (max b n) := by
    rw [hMeq]
    exact dvd_trans (mul_dvd_mul (pow_dvd_pow l (le_max_left b n)) (dvd_refl M')) ⟨N, by ring⟩
  have hM₁K : M₁ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_right _ _) hMK
  have hM₂K : M₂ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_left _ _) hMK
  have hnA : l ^ n ∣ l ^ (max b n) := pow_dvd_pow l (le_max_right b n)
  have hnK : l ^ n ∣ M' * N * l ^ (max b n) := dvd_trans hnA (dvd_mul_left _ _)
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := _root_.GlobalTheory.KZ.polySlash_laws (ZMod (l ^ n))
  have hΔ : ((CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))).subgroupOf (Gam N l)).Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M' * N * l ^ (max b n))
    exact Subgroup.normal_subgroupOf
  have h2 : IsUnit (2 : ZMod (l ^ n)) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    simpa using (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  obtain ⟨z, hzS, hzc, hzΔ⟩ := _root_.GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action (Gam N l) (ZMod (l ^ n)) (MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap)
    (fun g h v => by simp [L1]) (fun v => by simp [L2]) h2
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod (l ^ n)) w)
    (fun g v hv => by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv ⊢
      exact L3 _ _ _ hv)
    _ hΔ
    (fun δ hδ v => by
      have hδ' : (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (l ^ n) :=
        mem_Gamma_of_dvd hnK (Subgroup.mem_subgroupOf.mp hδ)
      show slP _ v = v
      rw [L6 _ 1 v (entries_eq_one_of_mem_Gamma hδ'), L2])
    ⟨c, hcΓ⟩
    (fun v hv => by
      show slP _ v = -v
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv
      rw [L6 _ (-1) v ?_, L7 w v hv, hw.neg_one_pow, neg_one_smul]
      intro i j
      have h := hcneg i j
      fin_cases i <;> fin_cases j <;> simp at h ⊢
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h))
    (fun g => by
      rw [Subgroup.mem_subgroupOf]
      simpa using hcomm g)
    (fun g => Φ n g)
    (fun δ _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhom n _))
    (fun δ hδ δ' hδ' => by
      have := hadd₁ _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ)) _
        (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ'))
      simpa using this)
    (fun g δ hδ => by
      have := hinv₂ g g.2 δ (mem_Gamma_of_dvd hM₂K (Subgroup.mem_subgroupOf.mp hδ))
      simpa using this)
  classical
  refine ⟨fun γ => if h : γ ∈ Gam N l then z ⟨γ, h⟩ else 0, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp (hzS _)
  · intro γ hγ δ hδ
    simp only [dif_pos hγ, dif_pos hδ, dif_pos (mul_mem hγ hδ)]
    simpa using hzc ⟨γ, hγ⟩ ⟨δ, hδ⟩
  · refine ⟨M' * N * l ^ (max b n) * l,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM'pos hN) (pow_pos hl.pos _)) hl.pos, fun δ hδ => ?_⟩
    have hδG : δ ∈ Gam N l :=
      mem_Gam_of_Gamma (dvd_mul_of_dvd_left ⟨M' * l ^ (max b n), by ring⟩ _) (dvd_mul_left _ _) hδ
    have hδK : δ ∈ CongruenceSubgroup.Gamma (M' * N * l ^ (max b n)) :=
      mem_Gamma_of_dvd (dvd_mul_right _ _) hδ
    simp only [dif_pos hδG]
    exact hzΔ ⟨δ, hδG⟩ (Subgroup.mem_subgroupOf.mpr hδK)

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElementsStatement
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ∀ (d : ℕ) (e : Fin d → Ω), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) → ∃ (E F : ℕ) (π : Ω) (κ : Fin F → Ω) (lam : Fin d → Fin F → Fin E → ℤ_[p]), 1 ≤ E ∧ IsAlgZp (p := p) π ∧ v π ^ E = v (p : Ω) ∧ (∀ j, IsInt (p := p) (κ j) ∧ IsAlgZp (p := p) (κ j)) ∧ (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * zp Ω (μ j)) = 1) ∧ ∀ t, e t = ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * zp Ω (lam t j s) := by
  first | exact @GlobalTheory.K5.OkBasis.okbasis | exact GlobalTheory.K5.OkBasis.okbasis | (intros; apply GlobalTheory.K5.OkBasis.okbasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizesStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ GlobalTheory.K5.IsInt (p := p) (j x)) → ∀ (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | exact GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | (intros; apply GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevelStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ), (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) → ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧ (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧ ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  first | exact @GlobalTheory.FamOfLevel.exists_family | exact GlobalTheory.FamOfLevel.exists_family | (intros; apply GlobalTheory.FamOfLevel.exists_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaPowers

theorem cycMod_Ine_surjective (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) :
    Function.Surjective ((cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype) := by
  intro u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hs : Function.Surjective (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) :=
    ZMod.ringHom_surjective _
  haveI := IsLocalHom.of_surjective _ hs
  obtain ⟨v, hv⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hs this u
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
  refine ⟨⟨σ, hσ⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [cycMod, MonoidHom.comp_apply, hσv]
  exact hv

end GlobalTheory.InertiaPowers
end

