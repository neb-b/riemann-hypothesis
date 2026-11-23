module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

namespace GlobalTheory.BdRQuot

theorem isUnit_one_add {R : Type} [CommRing R] (I : Ideal R) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I 1 z = 0) : IsUnit (1 + z) := by
  have h1 : z.val 1 = 0 := by
    have h' : (I ^ 1 • ⊤ : Ideal R) = I ^ 1 := by ext x; simp
    exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective).1 hz
  have hu : ∀ n, IsUnit (1 + z.val n) := by
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z.val (n + 1))
    have e1 := z.property (show 1 ≤ n + 1 by omega)
    have e2 := z.property (show n ≤ n + 1 by omega)
    rw [← hr, AdicCompletion.transitionMap_ideal_mk] at e1 e2
    rw [h1, Ideal.Quotient.eq_zero_iff_mem] at e1
    have hrI : r ∈ I := by simpa using e1
    refine IsNilpotent.isUnit_one_add ⟨n, ?_⟩
    rw [← e2, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    simpa using Ideal.pow_mem_pow hrI n
  let u : AdicCompletion I R := ⟨fun n => Ring.inverse (1 + z.val n), fun {m n} hmn => by
    have e := congrArg (AdicCompletion.transitionMap I R hmn) (Ring.inverse_mul_cancel _ (hu n))
    rw [AdicCompletion.transitionMap_map_mul, map_add (f := _), AdicCompletion.transitionMap_map_one,
      z.property hmn] at e
    exact left_inv_eq_right_inv e (Ring.mul_inverse_cancel _ (hu m))⟩
  refine IsUnit.of_mul_eq_one u ?_
  ext n
  exact Ring.mul_inverse_cancel _ (hu n)

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_FilP_zero : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_one, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 0)), Ideal.Quotient.eq_zero_iff_mem]
  simp

theorem mem_FilD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact fun h => GlobalTheory.RingIface.exists_of_mem_FilD_nat l h
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem mem_filtration_zero (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  simpa using Ideal.mul_mem_left _ y one_mem_FilP_zero

variable {P : LocPrime l} {AI : LocAinf l P}

theorem eD_ιA (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = Per.pD l (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA, ← GlobalTheory.RingIface.pD_eq_alg] at h
  simpa using h

theorem exists_approx (T : LocTied l P AI) (n : ℕ) (x : P.R.BdR) (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) := by
  obtain ⟨y, -, hy⟩ := (mem_FilD_nat 0 _).1 ((T.fil _ _ _).1 hx)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Per.ev l n y)
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (S := Per.AinfP l) (l : Per.Ainf l) s
  refine ⟨k, a, (T.fil _ _ _).2 ((mem_FilD_nat n _).2
    ⟨(l : Per.BdRp l) ^ k * y - algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) _ a), ?_, ?_⟩)⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have e : ∀ r : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) r) =
        Ideal.Quotient.mk _ r := fun r => GlobalTheory.RingIface.ev_alg l n r
    rw [map_sub, e, ← ha, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast,
      hs, mul_comm, sub_self]
  · rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, eD_ιA, hy,
      GlobalTheory.RingIface.pD_eq_alg]

theorem exists_inv (T : LocTied l P AI) (y : P.R.BdR) (hy : y ∈ (P.PD (botExt l)).Fil 1) :
    ∃ u ∈ (P.PD (botExt l)).Fil 0, (1 + y) * u = 1 := by
  obtain ⟨z, hz, e⟩ := (mem_FilD_nat 1 _).1 ((T.fil _ _ _).1 hy)
  have hU : IsUnit (1 + z : Per.BdRp l) := by
    obtain ⟨c, -, hc⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    have h := isUnit_one_add (Per.kerP l) (c z) (by rw [hc]; exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 1 z).1 hz)
    have h' := h.map c.symm
    rwa [map_add, map_one, RingEquiv.symm_apply_apply] at h'
  obtain ⟨v, hv'⟩ := hU.exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), (T.fil _ _ _).2 ?_, T.eD.injective ?_⟩
  · rw [RingEquiv.apply_symm_apply]
    exact (mem_FilD_nat 0 _).2 ⟨v, mem_filtration_zero _, rfl⟩
  · rw [map_mul, map_add (f := _), map_one, RingEquiv.apply_symm_apply, ← e,
      ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_add, ← map_mul, hv']

theorem mul_mem_zero {a : ℤ} {x y : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0)
    (hy : y ∈ (P.PD (botExt l)).Fil a) : x * y ∈ (P.PD (botExt l)).Fil a := by
  simpa using (P.PD (botExt l)).Fil_mul 0 a x y hx hy

theorem pow_mem_Fil {a : ℤ} {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) (n : ℕ) :
    x ^ n ∈ (P.PD (botExt l)).Fil (n * a) := by
  induction n with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih hx

theorem theta_pow (J : ThetaL P AI) (a : Ainf l) (k : ℕ) :
    J.θ (P.ιB (AI.ιA (a ^ k))) = J.θ (P.ιB (AI.ιA a)) ^ k := by
  induction k with
  | zero => simpa using J.θ_one
  | succ k ih => rw [pow_succ, map_mul, map_mul, J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ (AI.ainf_image_mem_filtration_zero _ _), ih, pow_succ]

theorem εroot_pow (n : ℕ) : AI.εroot (n + 1) ^ l ^ n = AI.ε1 := by
  induction n with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    rfl

theorem ζ_pow (n : ℕ) : AI.ζ (n + 1) ^ l ^ n = AI.ζ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, AI.ζ_succ, ih]

theorem theta_teich (J : ThetaL P AI) :
    J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) = ((AI.ζ 1 : OC l) : PadicComplex l) := by
  have key : ∀ n : ℕ, ‖J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) -
      ((AI.ζ 1 : OC l) : PadicComplex l)‖ ≤ ‖(l : PadicComplex l)‖ ^ (n + 1) := by
    intro n
    let c : OC l := ⟨J.θ (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot (n + 1))))),
      (GlobalTheory.RingBasics.mem_OC _).2 (J.θ_int _)⟩
    have h1 := J.θ_teich (AI.εroot (n + 1)) (AI.ζ (n + 1)) (by
      rw [LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add, AI.ε_coeff])
    have h2 : ((l : ℕ) : OC l) ∣ c - AI.ζ (n + 1) := by
      have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (c - AI.ζ (n + 1))).2 (by simpa using h1)
      rwa [pow_one, Ideal.mem_span_singleton] at this
    have h3 := dvd_sub_pow_of_dvd_sub h2 n
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, GlobalTheory.RingBasics.mem_span_pow_OC, ζ_pow] at h3
    rw [← εroot_pow (AI := AI) n, map_pow, theta_pow]
    simpa using h3
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : PadicComplex l))
    GlobalTheory.RingBasics.norm_p_lt).comp (Filter.tendsto_add_atTop_nat 1)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' lim key))

theorem exists_t_eq (T : LocTied l P AI) (J : ThetaL P AI) :
    ∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
  obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t 1 _).1 J.t_μ
  obtain ⟨u, hu, hyu⟩ := exists_inv T y hy
  have hy0 : y ∈ (P.PD (botExt l)).Fil 0 := (P.PD (botExt l)).Fil_anti 0 hy
  have h1 := (P.PD (botExt l)).one_mem
  have hθu : J.θ u = 1 := by
    have := congrArg J.θ hyu
    rwa [J.θ_mul _ (add_mem h1 hy0) _ hu, J.θ_add _ h1 _ hy0, (J.θ_ker y hy0).2 hy, J.θ_one,
      add_zero, one_mul] at this
  have hπ : J.θ (P.ιB (AI.ιA AI.π₁)) = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
    rw [eq_sub_iff_add_eq, ← theta_teich J, ← J.θ_one, ← J.θ_add _ (AI.ainf_image_mem_filtration_zero _ _) _ h1]
    simp [LocAinf.π₁]
  refine ⟨P.ιB (AI.ιA AI.π₁) * u, mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) hu, ?_, ?_⟩
  · rw [AI.μ_eq, map_mul, map_mul] at e
    linear_combination (-u) * e - P.ιB P.tB * hyu
  · rw [J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ hu, hθu, mul_one, hπ]

theorem exists_t_pow (J : ThetaL P AI) (a : ℤ) (n : ℕ) (x : P.R.BdR)
    (hx : x ∈ (P.PD (botExt l)).Fil (a + n)) :
    ∃ y ∈ (P.PD (botExt l)).Fil a, x = P.ιB P.tB ^ n * y := by
  induction n generalizing x with
  | zero => exact ⟨x, by simpa using hx, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc] at hx
    obtain ⟨z, hz, rfl⟩ := (J.fil_succ_iff_mul_t _ _).1 hx
    obtain ⟨y, hy, rfl⟩ := ih z hz
    exact ⟨y, hy, by ring⟩

theorem mem_Fil_iff (T : LocTied l P AI) (J : ThetaL P AI) (n : ℕ) (a : Ainf l) :
    P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a := by
  have hξ : P.ιB (AI.ιA AI.ξ) ∈ (P.PD (botExt l)).Fil 1 :=
    (AI.ainf_image_mem_filtration_one_iff _ _).2 ⟨1, (mul_one _).symm⟩
  constructor
  · obtain ⟨w, hw, ht, -⟩ := exists_t_eq T J
    have hunit : IsUnit (P.ιB (AI.ιA AI.ξ)) := by
      have := (P.PD (botExt l)).t_unit.map P.ιB
      rw [P.period_datum_t_eq, ht] at this
      exact isUnit_of_mul_isUnit_left this
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      rw [Nat.cast_succ] at h
      obtain ⟨b, rfl⟩ := ih ((P.PD (botExt l)).Fil_anti _ h)
      rw [add_comm] at h
      obtain ⟨y, hy, e⟩ := exists_t_pow J 1 n _ h
      rw [map_mul, map_mul, map_pow, map_pow, ht, mul_pow, mul_assoc] at e
      have e' := (hunit.pow n).mul_left_cancel e
      have hb : P.ιB (AI.ιA b) ∈ (P.PD (botExt l)).Fil 1 := by
        rw [e']
        exact mul_mem_zero (by simpa using pow_mem_Fil hw n) hy
      obtain ⟨c, rfl⟩ := (AI.ainf_image_mem_filtration_one_iff _ _).1 hb
      exact ⟨c, by rw [pow_succ, mul_assoc]; rfl⟩
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm]
    exact mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) (by simpa using pow_mem_Fil hξ n)

theorem fil_quotient : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (J : ThetaL P AI) (n : ℕ),
    (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l),
      (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧
    (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧
    (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1) :=
  fun _ _ _ _ T J n => ⟨exists_approx T n, mem_Fil_iff T J n, exists_t_eq T J⟩

end GlobalTheory.BdRQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousNormCharLFunctionNeZeroOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory
namespace NormCharL

theorem norm_cast_eq_one (K : Type) [Field K] [NumberField K] (m : ℕ) (β : 𝓞 K)
    (h : β - 1 ∈ Ideal.span {(m : 𝓞 K)}) : ((Algebra.norm ℤ β : ℤ) : ZMod m) = 1 := by
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 h
  have hβ : β = 1 + (m : 𝓞 K) * γ := by rw [mul_comm, hγ]; ring
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1 := by
    rw [hβ, map_add (f := _), map_one, map_mul, map_natCast, map_add (f := _), map_one, map_mul, map_natCast]
    ext i j
    simp [Matrix.one_apply]
  have h2 := (Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)
  rw [key, Matrix.det_one, ← Algebra.norm_eq_matrix_det] at h2
  simpa using h2

theorem sup_eq_top_iff (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : m.Prime)
    (I : Ideal (𝓞 K)) : I ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ ↔ ¬ m ∣ Ideal.absNorm I := by
  constructor
  · intro h hdvd
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hmem : i - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨-z, by rw [← hiy]; ring⟩
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m i hmem
    have hd : Ideal.absNorm I ∣ (Algebra.norm ℤ i).natAbs := by
      rw [← Ideal.absNorm_span_singleton]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hi)
    have hz : ((Algebra.norm ℤ i : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 (hdvd.trans hd)
    rw [hz] at h1
    have : Fact m.Prime := ⟨hm⟩
    exact zero_ne_one h1
  · intro h
    have hc : Nat.Coprime (Ideal.absNorm I) m := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 h))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K) = (u : 𝓞 K) * (Ideal.absNorm I : 𝓞 K) + (v : 𝓞 K) * (m : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this
      exact this.symm
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem I)))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem exists_continuous_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  intro K _ _ m hm χ cl hcl hχ
  have : Fact m.Prime := ⟨hm⟩
  set M : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hMdef
  let ψ : ZMod m → ℂ := fun x => if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    by_cases hx : x = 0
    · simp [ψ, hx]
    by_cases hy : y = 0
    · simp [ψ, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [ψ, dif_neg hx, dif_neg hy, dif_neg hxy]
    rw [← Units.val_mul, ← map_mul]
    congr 3
    ext
    simp
  have hψunit : ∀ u : (ZMod m)ˣ, ψ (u : ZMod m) = ((χ u : ℂˣ) : ℂ) := by
    intro u
    simp only [ψ, dif_neg u.ne_zero]
    congr 3
    ext
    simp
  let X : Ideal (𝓞 K) → ℂ := fun I => ψ (Ideal.absNorm I : ZMod m)
  have hcop : ∀ I : Ideal (𝓞 K), I ⊔ M = ⊤ ↔ (Ideal.absNorm I : ZMod m) ≠ 0 := by
    intro I
    rw [GlobalTheory.NormCharL.sup_eq_top_iff K m hm I, Ne, ZMod.natCast_eq_zero_iff]
  have hM0 : M ≠ ⊥ := by
    rw [hMdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hX0 : X ⊥ = 0 := by simp [X, hψ0]
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    simp only [X, map_mul, Nat.cast_mul, hψmul]
  have hXnorm : ∀ I, I ≠ ⊥ → I ⊔ M = ⊤ → ‖X I‖ = 1 := by
    intro I _ hI
    have hne := (hcop I).1 hI
    simp only [X, ψ, dif_neg hne]
    exact GlobalTheory.Mem.RayPrimes.norm_char χ _
  have hXzero : ∀ I, I ⊔ M ≠ ⊤ → X I = 0 := by
    intro I hI
    have : (Ideal.absNorm I : ZMod m) = 0 := by
      by_contra h
      exact hI ((hcop I).2 h)
    simp [X, this, hψ0]
  set ε : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← Units.val_mul, ← map_mul]
    simp
  obtain ⟨φ, hφmul, hφhom, hφsm, hφnorm, hφβ⟩ := GlobalTheory.T.exists_mixedSpace_norm_sign_character K ε hεε
  have hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ M → X (Ideal.span {β}) = φ (mixedEmbedding K β) := by
    intro β hβ0 hβ1
    rw [hφβ β hβ0]
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m β hβ1
    have hN0 : Algebra.norm ℤ β ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact hβ0
    simp only [X, Ideal.absNorm_span_singleton]
    split_ifs with hpos
    · have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = 1 := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le, h1]
      rw [this, ← Units.val_one, hψunit]
      simp
    · have hneg : Algebra.norm ℤ β ≤ 0 := le_of_not_gt hpos
      have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg, h1]
        simp
      rw [this, hψunit]
  obtain ⟨P, hPm, hPχ⟩ := hχ
  have hPtop : P.asIdeal ⊔ M = ⊤ := (GlobalTheory.NormCharL.sup_eq_top_iff K m hm P.asIdeal).2 hPm
  have hclX (Q : HeightOneSpectrum (𝓞 K)) (hQ : ¬ m ∣ Ideal.absNorm Q.asIdeal) :
      X Q.asIdeal = ((χ (cl Q) : ℂˣ) : ℂ) := by
    show ψ (Ideal.absNorm Q.asIdeal : ZMod m) = _
    rw [← hcl Q hQ, hψunit]
  have hnt : ∃ J, J ≠ ⊥ ∧ J ⊔ M = ⊤ ∧ X J ≠ 1 := by
    refine ⟨P.asIdeal, P.ne_bot, hPtop, ?_⟩
    rw [hclX P hPm]
    intro h
    exact hPχ (Units.val_eq_one.1 h)
  let c : HeightOneSpectrum (𝓞 K) → ℂ := fun Q => ((χ (cl Q) : ℂˣ) : ℂ)
  have hc : ∀ Q, ‖c Q‖ ≤ 1 := fun Q => (GlobalTheory.Mem.RayPrimes.norm_char χ (cl Q)).le
  have hcX : ∀ Q : HeightOneSpectrum (𝓞 K), ¬ M ≤ Q.asIdeal → c Q = X Q.asIdeal := by
    intro Q hQ
    have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
    have htop : Q.asIdeal ⊔ M = ⊤ := by
      refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left ?_)
      intro h
      exact hQ (h ▸ le_sup_right)
    rw [hclX Q ((GlobalTheory.NormCharL.sup_eq_top_iff K m hm Q.asIdeal).1 htop)]
  obtain ⟨L, hLd, hLe, hL1⟩ := GlobalTheory.idealCharacterL_continuation_ne_zero_one K M X φ hM0 hX0 hXmul
    hXnorm hXzero hφmul hφhom hφsm hφnorm hXφ hnt c hc hcX
  refine ⟨fun z => L ((max z.re 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · refine hLd.continuousOn.comp_continuous (by fun_prop) (fun z => ?_)
    show (0 : ℝ) < ((max z.re 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · simpa using hL1
  · intro s hs
    have hmax : max (s : ℂ).re 1 = s := by
      rw [Complex.ofReal_re]
      exact max_eq_left hs.le
    simp only [hmax]
    exact (hLe s (by rwa [Complex.ofReal_re])).symm

end NormCharL
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplitting
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem natCard_algHom_intermediateField_of_range_le {F E A : Type} [Field F] [Field E] [Field A]
    [Algebra F E] [Algebra F A] [FiniteDimensional F E] [Algebra.IsSeparable F E] [IsAlgClosed A]
    (M : IntermediateField F A) (h : ∀ (f : E →ₐ[F] A) (x : E), f x ∈ M) :
    Nat.card (E →ₐ[F] ↥M) = finrank F E := by

  have e : (E →ₐ[F] ↥M) ≃ (E →ₐ[F] A) :=
    { toFun := fun g => M.val.comp g
      invFun := fun f => f.codRestrict M.toSubalgebra (h f)
      left_inv := fun _ => AlgHom.ext fun _ => rfl
      right_inv := fun _ => AlgHom.ext fun _ => rfl }
  rw [Nat.card_congr e]
  exact AlgHom.natCard_of_splits F E A fun _ => IsAlgClosed.splits _

private theorem exists_fd_intermediateField_contains_embeddings (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ N : IntermediateField ℚ_[l] (Om l), FiniteDimensional ℚ_[l] ↥N ∧
      ∀ (f : E →ₐ[ℚ_[l]] Om l) (x : E), f x ∈ N := by
  have hfin : ∀ f : E →ₐ[ℚ_[l]] Om l, FiniteDimensional ℚ_[l] ↥f.fieldRange :=
    fun f => f.toLinearMap.finiteDimensional_range
  exact ⟨⨆ f : E →ₐ[ℚ_[l]] Om l, f.fieldRange,
    IntermediateField.finiteDimensional_iSup_of_finite,
    fun f x => (le_iSup (fun g : E →ₐ[ℚ_[l]] Om l => g.fieldRange) f) ⟨x, rfl⟩⟩

theorem exists_finExt_embedding_splitting (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧
      Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧
      Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := Module.Finite.left ℚ_[l] ↥(K0 K) ↥K.1
  obtain ⟨N1, hN1, hK1⟩ := exists_fd_intermediateField_contains_embeddings l ↥K.1
  obtain ⟨N0, hN0, hK0⟩ := exists_fd_intermediateField_contains_embeddings l ↥(K0 K)

  let φ : LL →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have : FiniteDimensional ℚ_[l] ↥φ.fieldRange := φ.toLinearMap.finiteDimensional_range

  refine ⟨⟨φ.fieldRange ⊔ N1 ⊔ N0, inferInstance⟩,
    ⟨φ.codRestrict (φ.fieldRange ⊔ N1 ⊔ N0).toSubalgebra fun x => ?_⟩, ?_, ?_⟩
  · exact (le_sup_left.trans le_sup_left : φ.fieldRange ≤ _) ⟨x, rfl⟩
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right.trans le_sup_left : N1 ≤ _) (hK1 f x)
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right : N0 ≤ _) (hK0 f x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Cyc

theorem exists_integral_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∃ χ : GQ l →* ℤ_[l]ˣ, (∀ g, (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l])) ∧ Continuous χ ∧ ∀ (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → ∃ g ∈ GK K, χ g = u := by
  intro l _ P
  have hχ : IsCyc P.χQ := P.χQ_cyc
  obtain ⟨hn, hc, hK⟩ := cyc_basic l P.χQ hχ
  let f : GQ l →* ℤ_[l] :=
    { toFun := fun g => ⟨(P.χQ g : ℚ_[l]), (hn g).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (P.χQ (a * b) : ℚ_[l]) = (P.χQ a : ℚ_[l]) * (P.χQ b : ℚ_[l])
        rw [map_mul, Units.val_mul]) }
  have hf : Continuous f := hc.subtype_mk _
  refine ⟨f.toHomUnits, fun g => rfl, ?_, ?_⟩
  · rw [Units.continuous_iff]
    exact ⟨hf, hf.comp continuous_inv⟩
  · intro K s hs u hu
    have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
    obtain ⟨g, hg, hgu⟩ := exists_chi_eq K P.χQ hχ _ hu1
    have hG : g ∈ Gj K s := ((hK K g hg).1 s).2 (by
      rw [hgu]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow ((u : ℤ_[l]) - 1) s).2
        (Ideal.mem_span_singleton.2 hu)
      rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] at this)
    refine ⟨g, IntermediateField.fixingSubgroup_antitone hs hG, ?_⟩
    exact Units.ext (Subtype.ext hgu)

end GlobalTheory.Cyc
end

