module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartQuadraticPhaseEqCmThetaExp
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitPhase

open scoped TensorProduct

theorem phase_eq : ∀ D : D7, ∃ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E),
  Setup ψ θ S T cc δ r → ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
  ψ (-symplOH S T (GlobalTheory.FinWeilO.intA D w • finPt (S := S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z)) =
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D
  have hsq := D.host.sqd_sq
  let b : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩
  have hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2 := rfl
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star (b : D.host.E) = 1 - (b : D.host.E) := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  refine ⟨b, ?_, ?_⟩
  · apply NumberField.RingOfIntegers.ext
    show (b : D.host.E) + ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = 1
    have hc : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := by
      have e1 : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E) := rfl
      rw [e1]
      exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
    rw [hc, hbs]; ring
  · intro ψ θ S T cc δ r hset z
    have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hset.crv.1.1 hset.scale
    set X : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.of fun i j => -(r⁻¹ * z i j) with hX
    have hfin : finPt (S := S) (T := T) rfl rfl r z = GlobalTheory.LatVac.finTens 1 X := by
      funext i j; rfl
    have hmap : GlobalTheory.FinWeilO.intA D b • GlobalTheory.LatVac.finTens 1 X =
        GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * X i j) := by
      funext i j
      show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (X i j)) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * X i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    set n : D.host.E := ∑ c, ∑ a, star (X c a) * X c a with hn
    have hns : star n = n := by
      rw [hn, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [star_mul', star_star, mul_comm]
    have hR : GlobalTheory.LatVac.hRat S T X X = n := by
      rw [GlobalTheory.LatVac.hRat, hset.gS, hset.gT, inv_one]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have e : ∀ x, (∑ x_1, ∑ x_2, if x = x_1 then star (X x_2 x_1) * X x_2 x else 0) =
          ∑ x_2, star (X x_2 x) * X x_2 x := fun x => by
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]
    have hs : symplOH S T (GlobalTheory.FinWeilO.intA D b • finPt (S := S) (T := T) rfl rfl r z)
        (finPt (S := S) (T := T) rfl rfl r z) = pairA D.host.F 0
        (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by
      rw [hfin, hmap, symplOH, GlobalTheory.LatVac.symplO_finTens, GlobalTheory.ThetaSignLat.hRat_smul_left, hR]
      refine Prod.ext (mul_zero _) ?_
      show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _
      rw [one_mul, one_mul, ← RingHom.map_mul]
      rfl
    have hq := GlobalTheory.ThetaSignLat.trace_val n (b : D.host.E) hns hbv
    set q : D.host.F := 1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) with hqdef
    have hneg : -(pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (-q)) := by
      refine Prod.ext ?_ ?_
      · show -(0 : Ainf D.host.F) = 0
        exact neg_zero
      · show -(algebraMap D.host.F (Af D.host.F) q) = _
        rw [map_neg]
        rfl
    rw [hs, hneg, GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap ψ hset.std]
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n := ⟨_, rfl⟩
    obtain ⟨hxi, hN1, hd1⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
    have hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
    have hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0 := by exact_mod_cast hNR
    have hdR : Real.sqrt D.host.d ≠ 0 := by linarith
    have hsumq : ∑ τ, tauE D τ ((-q : D.host.F) : D.host.E) = c / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := by
      have e : ∀ τ, tauE D τ ((-q : D.host.F) : D.host.E) = tauE D τ n / (2 * (Ideal.absNorm D.host.ccK : ℂ)) :=
        fun τ => by
          rw [show ((-q : D.host.F) : D.host.E) = -((q : D.host.F) : D.host.E) from rfl, hq, neg_div, neg_neg,
            map_div₀, map_mul, map_natCast, map_ofNat]
      rw [Finset.sum_congr rfl fun τ _ => e τ, ← Finset.sum_div, hc]
    have hcre : ((c.re : ℝ) : ℂ) = c := by
      have : starRingEnd ℂ c = c := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hc, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← GlobalTheory.FockCompare.tauE_star, hns]
      exact Complex.conj_eq_iff_re.1 this
    set Z : VC D S.rank T.rank := fun τ i j => -(embT D τ (X i j)) with hZ
    have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * Z τ i j := by
      funext τ i j
      have ez : z i j = r * -(X i j) := by
        rw [hX, Matrix.of_apply]
        field_simp
      show δ * embT D τ (z i j) = δ * embT D τ r * -(embT D τ (X i j))
      rw [ez, map_mul, map_neg]
      ring
    have hsum : ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j) = c := by
      rw [hc]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hn, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, GlobalTheory.FockCompare.tauE_star, hZ]
      show -(tauE D τ (X i j)) * starRingEnd ℂ (-(tauE D τ (X i j))) = _
      rw [map_neg]
      ring
    rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.TaylorLogMetric.qH, hpt, GlobalTheory.NormExact.Hf_scale hset.crv hset.scale, hsum, Formalism.MainNotions.StandardLatticesGL3.ee,
      hsumq]
    have hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re / 2 =
        c.re / (2 * Ideal.absNorm D.host.ccK) := by
      rw [show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring,
        Complex.re_ofReal_mul, hxi]
      field_simp
    rw [hre]
    congr 1
    push_cast
    rw [hcre]
end GlobalTheory.SplitPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZeroAtPlaces

section Generic

variable {K : Type} [Field K] [NumberField K]

theorem ev_mul (a b : FiniteAdeleRing (𝓞 K) K) (Q : HeightOneSpectrum (𝓞 K)) : (a * b) Q = a Q * b Q := rfl

theorem val_nat (Q : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = Q.valuation K ((n : 𝓞 K) : K) := by
  rw [← Formalism.UG.P.levelaf_valued_algebraMap, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) n]
  rfl

theorem val_nat_eq_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = 1 := by
  rw [val_nat]
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), not_lt] at hn
  exact le_antisymm (Q.valuation_le_one (K := K) _) hn

theorem val_nat_lt_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∈ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) < 1 := by
  rw [val_nat]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) Q _).2 hn

theorem divisible_iff {q : ℕ} (hq : q.Prime) (y : FiniteAdeleRing (𝓞 K) K)
    (hy : ∃ n : ℕ, 0 < n ∧ ∀ Q, ((n : FiniteAdeleRing (𝓞 K) K) * y) Q ∈ Q.adicCompletionIntegers K) :
    (∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m q ∧ ∃ s : FiniteAdeleRing (𝓞 K) K,
      (∀ Q, s Q ∈ Q.adicCompletionIntegers K) ∧
        (m : FiniteAdeleRing (𝓞 K) K) * y = (q : FiniteAdeleRing (𝓞 K) K) ^ k * s) ↔
    ∀ Q : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∈ Q.asIdeal → y Q = 0 := by
  constructor
  · intro h Q hQ
    by_contra h0
    have h1 : Valued.v (y Q) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨k, hk⟩ := exists_pow_lt₀ (val_nat_lt_one Q hQ) (Units.mk0 _ h1)
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have hm' : (m : 𝓞 K) ∉ Q.asIdeal := by
      intro hmem
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hm).map (Int.castRingHom (𝓞 K))
      simp only [eq_intCast, Int.cast_natCast] at hab
      refine Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hQ)
    have e1 : (m : FiniteAdeleRing (𝓞 K) K) Q * y Q = ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k * s Q :=
      congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) e
    have e2 := congrArg Valued.v e1
    rw [map_mul, map_mul, map_pow, val_nat_eq_one Q hm', one_mul] at e2
    have hs1 : Valued.v (s Q) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hs Q)
    rw [Units.val_mk0, e2] at hk
    exact absurd hk (not_lt.2 (mul_le_of_le_one_right' hs1))
  · intro h k
    obtain ⟨n, hn, hint⟩ := hy
    obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _))
    have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    have hu : (q : FiniteAdeleRing (𝓞 K) K) ^ k * algebraMap K _ ((q : K) ^ k)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) q, ← map_pow, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero k hq0), map_one]
    refine ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm,
      algebraMap K _ ((q : K) ^ k)⁻¹ * ((m : FiniteAdeleRing (𝓞 K) K) * y), fun Q => ?_,
      by rw [← mul_assoc, hu, one_mul]⟩
    by_cases hQ : (q : 𝓞 K) ∈ Q.asIdeal
    · rw [ev_mul, ev_mul, h Q hQ, mul_zero, mul_zero]
      exact zero_mem _
    · have h1 := val_nat_eq_one Q hQ
      have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint Q)
      have e1 : ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k *
          (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((q : K) ^ k)⁻¹) Q = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) hu
      have e2 := congrArg Valued.v e1
      rw [map_mul, map_pow, h1, one_pow, one_mul, map_one] at e2
      have e3 : (((q ^ j * m : ℕ) : FiniteAdeleRing (𝓞 K) K) * y) Q =
          ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ j * ((m : FiniteAdeleRing (𝓞 K) K) * y) Q := by
        rw [Nat.cast_mul, Nat.cast_pow, mul_assoc]
        rfl
      rw [e3, map_mul, map_pow, h1, one_pow, one_mul] at h2
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, map_mul, e2, one_mul]
      exact h2

end Generic

open GlobalTheory.BotFormula GlobalTheory.BotClassDict

theorem mem_OhE_iff {D : D7} (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    y ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔ ∀ Q, toFinE D y Q ∈ Q.adicCompletionIntegers D.host.E :=
  ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int (ι := (toFinE D).toRingHom) toFinE_tmul hy,
    fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (toFinE D).toRingHom) toFinE_tmul hy⟩

theorem zeroAt_iff_comp {D : D7} {q : ℕ} (hq : q.Prime) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q y ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (q : 𝓞 D.host.E) ∈ Q.asIdeal → toFinE D y Q = 0 := by
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.AdelicApprox.approx_mod_ideal D ⊤ top_ne_bot).2.1 y
  rw [mem_OhE_iff, map_mul, map_natCast] at hint
  rw [← divisible_iff hq (toFinE D y) ⟨n, hn, hint⟩]
  refine forall_congr' fun k => exists_congr fun m => and_congr_right' (and_congr_right' ⟨?_, ?_⟩)
  · rintro ⟨s, hs, e⟩
    refine ⟨toFinE D s, (mem_OhE_iff s).1 hs, ?_⟩
    have := congrArg (toFinE D) e
    rwa [map_mul, map_mul, map_pow, map_natCast, map_natCast] at this
  · rintro ⟨s, hs, e⟩
    obtain ⟨s, rfl⟩ := (toFinE D).surjective s
    refine ⟨s, (mem_OhE_iff s).2 hs, (toFinE D).injective ?_⟩
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast]
    exact e

theorem toFinE_finQ {D : D7} (a : AE D) :
    toFinE D (finQ D a) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D a) := by
  rw [← finAdEquiv_toAfE, toAfE_finQ]
  rfl

theorem comp_base {D : D7} (η : AF D.host.F) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) := by
  have h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (algebraMap (AF D.host.F) (AE D) η)) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E η.2 * algebraMap D.host.E _ 1 := GlobalTheory.LFun.toFinAd_tmul η.2 1
  rw [toFinE_finQ, h, map_one, mul_one]
  rfl

theorem idem_mul_eq_zero_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) η * a = 0 ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v → toFinE D (finQ D a) Q = 0 := by
  have hev : ∀ Q, toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η * a)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) * toFinE D (finQ D a) Q := by
    intro Q
    rw [RingHom.map_mul, map_mul, ev_mul, comp_base]
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  have k1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 1 := by
    intro Q hQ
    subst hQ
    exact (congrArg _ h1).trans (map_one _)
  have k0 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ≠ v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 0 :=
    fun Q hQ => (congrArg _ (h0 _ hQ)).trans (map_zero _)
  constructor
  · intro e Q hQ
    have := hev Q
    rw [e, k1 Q hQ, one_mul, RingHom.map_zero, map_zero] at this
    exact this.symm
  · intro e
    refine GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [← toFinE_finQ, RingHom.map_zero, map_zero]
    refine FiniteAdeleRing.ext _ fun Q => (hev Q).trans ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [e Q hQ, mul_zero]
      rfl
    · rw [k0 Q hQ, zero_mul]
      rfl

theorem zeroAt_finQ_iff : ∀ (D : D7) (q : ℕ), q.Prime → ∀ a : AE D, (Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D a) ↔
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η → (q : 𝓞 D.host.F) ∈ v.asIdeal →
    algebraMap (AF D.host.F) (AE D) η * a = 0) := by
  intro D q hq a
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      (q : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal ↔ (q : 𝓞 D.host.E) ∈ Q.asIdeal := by
    intro Q
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal ↔ _
    rw [map_natCast]
  rw [zeroAt_iff_comp hq]
  constructor
  · intro h v η hη hv
    refine (idem_mul_eq_zero_iff hη a).2 fun Q hQ => h Q ((hmem Q).1 ?_)
    rw [hQ]
    exact hv
  · intro h Q hQ
    obtain ⟨η, hη⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
    exact (idem_mul_eq_zero_iff hη a).1 (h _ η hη ((hmem Q).2 hQ)) Q rfl

end GlobalTheory.ZeroAtPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.FockChi

theorem fockIn_chi_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht i hi e0 he f hf
  have hcf := _root_.GlobalTheory.VacConj.isVacO_conj_negSp _ _ _ _ _ _ _ _ f hf
  obtain ⟨c, hc'⟩ := _root_.GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.fr _) (N.fr _) (N.fr_on _ ⟨hi, rfl⟩) (N.fr_on _ ⟨by omega, rfl⟩)
    (W.cart_is _ ⟨hi, le_rfl⟩) (W.cart_is _ ⟨by omega, le_rfl⟩) δ t0 hc hδ ht e0 he _ hcf
  refine ⟨Units.map (starRingEnd ℂ).toMonoidHom c, fun k => ?_⟩
  have h2 := _root_.GlobalTheory.FockConj.pureTensorO_negSp_monomial W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.frC (.grid (i + 1) D.R.m)) (N.frC (.grid i D.R.m)) f hf.1 hf.2.inf k 0
  have e1 : N.frC (.grid (i + 1) D.R.m) = fun τ => (N.fr (.grid (i + 1) D.R.m)).1.map (tauE D τ) := rfl
  have e2 : N.frC (.grid i D.R.m) = fun τ => (N.fr (.grid i D.R.m)).1.map (tauE D τ) := rfl
  show pureTensorO _ _ _ _ _ _ _ _ f _ 0 = _
  rw [h2, e1, e2, hc' k, map_mul]
  rfl

end GlobalTheory.FunObj.FockChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StdPairPlaces

theorem coprime_of_splitK {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by
  have hn : ¬ p ∣ H.condN := not_dvd_of_splitK hp h
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn

theorem natCast_two_q_d_notMem : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D large₂ hR T L sc G μ₀ hL t w hw
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  have hsp : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp h =>
    coprime_of_splitK hp (Pm.level_split p h)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ LevelStarExponents.condE D := dvd_rfl
  rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine GlobalTheory.HalfCompare.not_mem_of_coprime w (b := q0 D) ?_ ((GlobalTheory.FunObj.Good.natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      exact (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1 (hdvd.mul_left _)).symm
    · simp only [S1_mem_OmF, GlobalTheory.FunObj.Good.natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 0) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 1) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde_prime D.host.pde_level.1).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde'_prime D.host.pde_level.2).symm a
  · exact fun h => (hL.Q_off t w b).1 (GlobalTheory.HalfCompare.mem_of_dvd h ⟨D.sp.T, by ring⟩)

end GlobalTheory.StdPairPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficients
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.TieIdem

theorem coeff_conj_of_central' {K : Type} [Field K] {G : Type} [Group G] (e : MonoidAlgebra K G)
    (he : ∀ x, x * e = e * x) (k g : G) : e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun a : MonoidAlgebra K G => a.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply] at h
  simpa [mul_assoc] using h.symm

theorem idemOf_props {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (∀ k : G, ∑ g, (idemOf X).coeff g * (idemOf X).coeff (g⁻¹ * k) = (idemOf X).coeff k) ∧
    (∀ g h : G, (idemOf X).coeff (h * g * h⁻¹) = (idemOf X).coeff g) ∧
    (∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * (idemOf X).coeff g)) ∧
    ∀ (σ : K →+* ℂ) (g : G), σ ((idemOf X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf X).coeff g)) := by
  refine ⟨fun k => ?_, fun g h => ?_, fun g => ?_, fun σ g => ?_⟩
  · rw [← coeff_mul_fin, idemOf_mul_self X hX]
  · exact coeff_conj_of_central' _ (fun b => idemOf_central X hX b) h g
  · obtain ⟨b, hb⟩ := idemOf_integral X hX g
    rw [← hb]
    exact b.isIntegral_coe
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have h1 := (hX χ hχ).map_inv σ 1
      have h2 := (hX χ hχ).map_inv σ g
      rw [inv_one] at h1
      simp only [map_mul, map_div₀, map_natCast, inv_inv, h2, Complex.conj_conj]
      rw [← h1]

end GlobalTheory.TieIdem

namespace GlobalTheory.TieIdem

end GlobalTheory.TieIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIffStatement
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂], IsLocIso j → ∀ (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → ∀ (Z : Matrix A D k), IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  first | exact @GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | exact GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | (intros; apply GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff <;> assumption)
end

