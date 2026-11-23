module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortInterval
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem sum_lam_zero_le_card_normPrimes (𝓕 : LFam) (d M : ℕ)
    (hN : ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p) (X Y : ℝ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, 𝓕.lam 0 n ≤
      2 * Real.log Y * ((GlobalTheory.Mem.An.normPrimes d M X Y).card : ℝ) +
        2 * (Chebyshev.psi Y - Chebyshev.theta Y) := by
  have hl : ∀ n, 𝓕.lam 0 n ≤ 2 * vonMangoldt n := fun n =>
    le_trans (Finset.single_le_sum (f := fun g => 𝓕.lam g n) (fun g _ => 𝓕.lam_nonneg g n)
      (Finset.mem_univ _)) (𝓕.lam_le n)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun n : ℕ => n.Prime)]
  apply add_le_add
  · have h1 : ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun n : ℕ => n.Prime), 𝓕.lam 0 n =
        ∑ n ∈ GlobalTheory.Mem.An.normPrimes d M X Y, 𝓕.lam 0 n := by
      symm
      apply Finset.sum_subset
      · intro p hp
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
      · intro p hp hq
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp hq
        by_contra h
        exact hq ⟨hp.1, hp.2, hN p hp.2 h⟩
    rw [h1, mul_comm, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    have h2 : (p : ℝ) ≤ Y := (Nat.le_floor_iff (by linarith)).1 hp.1.2
    have h3 : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by exact_mod_cast hp.2.1.pos) h2
    have h4 := hl p
    rw [vonMangoldt_apply_prime hp.2.1] at h4
    linarith
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun n _ => hl n) ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
    · intro n _ _
      have := @vonMangoldt_nonneg n
      positivity

theorem sqrt_le_short_main {A K c B X h : ℝ} (hA : 0 < A) (hK : 0 < K) (hc : 0 < c)
    (hcT : c ≤ 1 / (2 * (1 + A) + 2 + K)) (hB : 4 ≤ B) (hX : 1 ≤ X)
    (hBX : Real.log B ≤ c * Real.sqrt (Real.log X))
    (hh : Real.exp (-c * Real.sqrt (Real.log X)) ≤ h) :
    1 ≤ Real.log X ∧ K * Real.sqrt X ≤ h * X / B ^ A := by
  set s := Real.sqrt (Real.log X) with hs
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log X := Real.mul_self_sqrt hL
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set T := 2 * (1 + A) + 2 + K with hT
  have hT0 : 0 < T := by positivity
  have hcT' : c * T ≤ 1 := by rwa [le_div_iff₀ hT0] at hcT
  have hsT : T ≤ s := by
    by_contra h'
    have : c * s < c * T := mul_lt_mul_of_pos_left (not_le.1 h') hc
    linarith
  have hc1 : c ≤ 1 := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  refine ⟨by nlinarith, ?_⟩
  have hX0 : 0 < X := by linarith
  have hsq : Real.sqrt X = Real.exp (s * s / 2) := by
    rw [hss, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]
    congr 1; ring
  have hXe : X = Real.exp (s * s) := by rw [hss, Real.exp_log hX0]
  have hcs : c * s ≤ s := by nlinarith
  have hBA : B ^ A ≤ Real.exp (A * s) := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.2
    nlinarith
  have hh' : Real.exp (-s) ≤ h := le_trans (Real.exp_le_exp.2 (by linarith)) hh
  have hKe : K ≤ Real.exp (s * s / 2 - (1 + A) * s) := by
    have := Real.add_one_le_exp (s * s / 2 - (1 + A) * s)
    have h5 : s * 1 ≤ s * (s / 2 - (1 + A)) := mul_le_mul_of_nonneg_left (by linarith) hs0
    nlinarith
  have hBA0 : 0 < B ^ A := Real.rpow_pos_of_pos hB0 A
  rw [le_div_iff₀ hBA0, hsq]
  calc K * Real.exp (s * s / 2) * B ^ A
      ≤ Real.exp (s * s / 2 - (1 + A) * s) * Real.exp (s * s / 2) * Real.exp (A * s) := by
        gcongr
    _ = Real.exp (-s) * Real.exp (s * s) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ h * X := by
        rw [← hXe]; gcongr

theorem normPrimes_short_interval_lower : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  obtain ⟨A, c₀, e, hA, hc₀, he, H⟩ := _root_.GlobalTheory.Hk.ShortInt.trivialClass_shortInterval
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K : ℝ := 8 * (|C| + 1) / e with hKdef
  have hK : 0 < K := by positivity
  refine ⟨A, min c₀ (1 / (2 * (1 + A) + 2 + K)), e / 8, hA, lt_min hc₀ (by positivity),
    by positivity, ?_⟩
  intro d M X h hd hd4 hd100 hM hX hB hh hh1
  obtain ⟨𝓕, hFB, hN⟩ := _root_.GlobalTheory.Hk.exists_lFam_ray d M hd hd4 hd100 hM
  rw [← hFB] at hB ⊢
  set c := min c₀ (1 / (2 * (1 + A) + 2 + K)) with hc
  have hc0 : 0 < c := lt_min hc₀ (by positivity)
  have hcc : c * Real.sqrt (Real.log X) ≤ c₀ * Real.sqrt (Real.log X) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hh
  have H1 := H 𝓕 X h hX (hB.trans hcc) (le_trans (Real.exp_le_exp.2 (by linarith)) hh) hh1
  obtain ⟨hL, hS⟩ := sqrt_le_short_main hA hK hc0 (min_le_right _ _) 𝓕.B_ge hX hB hh
  have hY1 : 1 ≤ X * (1 + h) := by nlinarith
  have hY2 : X * (1 + h) ≤ 2 * X := by nlinarith
  have H2 := sum_lam_zero_le_card_normPrimes 𝓕 d M hN X (X * (1 + h)) hY1
  have hlog : Real.log (X * (1 + h)) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + h by linarith)
    linarith
  have hsq : Real.sqrt (X * (1 + h)) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have H3 : Chebyshev.psi (X * (1 + h)) - Chebyshev.theta (X * (1 + h)) ≤
      (|C| + 1) * (2 * Real.sqrt X) := by
    refine (hC _).trans ?_
    have := le_abs_self C
    have := abs_nonneg C
    have := Real.sqrt_nonneg (X * (1 + h))
    gcongr
    linarith
  have hBA0 : 0 < 𝓕.B ^ A := Real.rpow_pos_of_pos (by linarith [𝓕.B_ge]) A
  set N : ℝ := ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have H4 : 8 * (|C| + 1) * Real.sqrt X ≤ e * (h * X / 𝓕.B ^ A) := by
    have : 8 * (|C| + 1) * Real.sqrt X = e * (K * Real.sqrt X) := by
      rw [hKdef]; field_simp
    rw [this]; gcongr
  have H5 : e * h * X / 𝓕.B ^ A = e * (h * X / 𝓕.B ^ A) := by ring
  have H6 : 2 * Real.log (X * (1 + h)) * N ≤ 4 * Real.log X * N := by
    apply mul_le_mul_of_nonneg_right _ hN0
    linarith
  have H7 : e / 8 * h * X / (𝓕.B ^ A * Real.log X) = e * (h * X / 𝓕.B ^ A) / (8 * Real.log X) := by
    field_simp
  rw [H7, div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.PeriodIdealUnit

theorem not_dvd_different {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ} (hl : l.Prime)
    (v : Ideal (𝓞 E)) [hvp : v.IsPrime] (hv : ((l : ℕ) : 𝓞 E) ∈ v) (h2 : ((l : ℕ) : 𝓞 E) ∉ v ^ 2) :
    ¬ v ∣ differentIdeal (𝓞 K) (𝓞 E) := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : v.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hvp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have he : v.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact h2 (by simpa using hne)
  have : Algebra.IsUnramifiedAt ℤ v := Ideal.ramificationIdx_eq_one_iff.1 he
  exact not_dvd_differentIdeal_iff.2 (Algebra.IsUnramifiedAt.of_restrictScalars ℤ v)

theorem locP_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E)
    (h1 : I ≤ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h2 : ∃ n, n ∉ P.asIdeal ∧ n • (1 : E) ∈ I) :
    localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
  le_antisymm ((ThetaMove.localization_mono P h1).trans (localization_localization₂ P _).le)
    ((ThetaMove.localization_mono P (Submodule.one_le.2 h2 : (1 : Submodule (𝓞 E) E) ≤ localization₂ P.asIdeal I)).trans (localization_localization₂ P _).le)

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem one_mem_inv_b (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  refine (FractionalIdeal.mem_inv_iff (b_ne_zero D)).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem locP_AA_eq_one : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)), (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal) → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  intro X D s cc δ B χ cD P hp h2 hc
  let e : 𝓞 D.host.E ≃+* 𝓞 X.E := RingOfIntegers.mapRingEquiv s.iE.symm
  have he : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 X.E) X.E (e x) = s.iE.symm (algebraMap _ D.host.E x) := fun x => rfl
  have := P.isPrime
  let v : Ideal (𝓞 D.host.E) := P.asIdeal.comap (e : 𝓞 D.host.E →+* 𝓞 X.E)
  have hvp : v.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hv1 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v := by
    rw [Ideal.mem_comap, map_natCast]; exact hmem
  have hv2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v ^ 2 := fun h => by
    have h3 := Ideal.le_comap_pow (e : 𝓞 D.host.E →+* 𝓞 X.E) 2 h
    rw [Ideal.mem_comap, map_natCast] at h3
    exact h2 h3
  have hnd := not_dvd_different (K := D.host.K) hp v hv1 hv2
  have hnot : ¬ D.host.𝔟 ≤ v := fun hle => hnd (by
    rw [D.host.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hN : ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => by
    have h3 : IsCoprime ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) := hc.cast
    obtain ⟨a, b, hab⟩ := h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hmem)))
  refine locP_eq_one P _ ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine ⟨e z, hzP, Submodule.mem_one.2 ⟨e (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def, he, he, ← map_mul, map_mul (algebraMap _ D.host.E), hw]
    congr 1
    have : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) = ((c : D.host.K) : D.host.E) := rfl
    rw [this]
    ring
  · refine ⟨_, hN, Submodule.subset_span ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, 1, one_mem_inv_b D, ?_⟩⟩
    have h1 : (((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K)) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) :=
      map_natCast ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)) _
    rw [h1, mul_one, map_natCast, Algebra.smul_def, map_natCast, mul_one]

end GlobalTheory.PeriodIdealUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdDetConjFinite
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.OrdDetConj

open GlobalTheory.CharValCompare

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem ordE_mul (P : HeightOneSpectrum (𝓞 E)) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordE P (a * b) = ordE P a + ordE P b := by
  unfold ordE
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]

theorem exists_ordE_star (P : HeightOneSpectrum (𝓞 E)) :
    ∃ m : ℤ, 0 ≤ m ∧ ∀ a : E, a ≠ 0 → ordE (conjPrime₂ P) (star a) = m * ordE P a := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hs0 : (conjPrime₂ P).valuation E (star π) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 hπ0)
  refine ⟨ordE (conjPrime₂ P) (star π), ?_, fun a ha => ?_⟩
  · have h1 : (conjPrime₂ P).valuation E (star π) ≤ 1 := intAt_iff.1 (intAt_star (intAt_iff.2 (by
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)))
    unfold ordE
    rw [neg_nonneg, WithZero.log_le_iff_le_exp hs0]
    exact h1
  · have ha' : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have hsa : (conjPrime₂ P).valuation E (star a) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 ha)
    have h1 : P.valuation E (a * π ^ (WithZero.log (P.valuation E a))) = 1 := by
      rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      conv_lhs => arg 1; rw [← WithZero.exp_log ha']
      rw [← WithZero.exp_add]
      simp
    have h2 := congrArg WithZero.log (val_star_eq_one h1)
    rw [star_mul', star_zpow₀, map_mul, map_zpow₀, WithZero.log_mul hsa (zpow_ne_zero _ hs0), WithZero.log_zpow,
      WithZero.log_one, smul_eq_mul] at h2
    unfold ordE
    linear_combination -h2

theorem ordE_star (P : HeightOneSpectrum (𝓞 E)) {a : E} (ha : a ≠ 0) : ordE (conjPrime₂ P) (star a) = ordE P a := by
  obtain ⟨m, hm, h⟩ := exists_ordE_star P
  obtain ⟨m', hm', h'⟩ := exists_ordE_star (conjPrime₂ P)
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have h1 : ordE P π = 1 := by
    unfold ordE
    rw [hπ, WithZero.log_exp, neg_neg]
  have h2 := h' (star π) (star_ne_zero.2 hπ0)
  rw [conjP_conjP, star_star, h π hπ0, h1, mul_one] at h2
  have h3 : m = 1 := Int.eq_one_of_mul_eq_one_left hm h2.symm
  rw [h a ha, h3, one_mul]

theorem ordDet_conjP {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ordDet (conjPrime₂ P) N = -ordDet P N := by
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨f', hf'⟩ := exists_isFr (conjPrime₂ P) hN
  have h := val_dual hN hf hf'
  have h0 : star (dt f) ≠ 0 := star_ne_zero.2 (dt_ne _)
  rw [← ordE_eq_zero_iff (mul_ne_zero h0 (dt_ne _)), ordE_mul _ h0 (dt_ne _), ordE_star P (dt_ne _)] at h
  rw [ordDet_eq hf, ordDet_eq hf']
  linear_combination h

theorem finite_pos {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N}.Finite := by
  rcases Set.eq_empty_or_nonempty {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N} with h | ⟨P, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((gen_detI hf).2 _).2 le_rfl)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (zero_mem _)
  have hx0 : s • dt f ≠ 0 := smul_ne_zero hs0 (dt_ne _)
  refine (HeightOneSpectrum.Support.finite (𝓞 E) (s • dt f)⁻¹).subset fun Q hQ => ?_
  obtain ⟨g, hg⟩ := exists_isFr Q hN
  have h1 := ((gen_detI hg).2 _).1 (le_locP Q _ hx)
  have h2 : Q.valuation E (dt g) < 1 := by
    rw [Set.mem_ofPred_eq, ordDet_eq hg, ordE, neg_pos,
      WithZero.log_lt_iff_lt_exp ((Valuation.ne_zero_iff _).2 (dt_ne _))] at hQ
    exact hQ
  show 1 < Q.valuation E (s • dt f)⁻¹
  rw [map_inv₀, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]
  exact h1.trans_lt h2

theorem ordDet_conj_finite : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 E), ordDet (conjPrime₂ P) N = -ordDet P N) ∧ {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite := by
  intro E _ _ _ n N hN
  refine ⟨ordDet_conjP hN, ((finite_pos hN).union ((finite_pos hN).image conjPrime₂)).subset fun Q hQ => ?_⟩
  rcases lt_or_gt_of_ne hQ with h | h
  · refine Or.inr ⟨conjPrime₂ Q, ?_, conjP_conjP Q⟩
    rw [Set.mem_ofPred_eq, ordDet_conjP hN]
    exact neg_pos.2 h
  · exact Or.inl h

end GlobalTheory.OrdDetConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PTermOfStd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerT.PAll

section Hom

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap P g N _).2 (by simpa using hy))
    exact (mem_localization_gmap P g' N' _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap P g N _).1 hy)
    refine (mem_localization_gmap P g' N' _).2 ?_
    simpa using this

omit [NumberField E] [StarRing E] in
theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    (g'.symm.toLinearMap ∘ₗ (c • x : HomE E a b) ∘ₗ g.toLinearMap : HomE E a b) =
      c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) := by
  rw [← algebraMap_smul E c x, ← algebraMap_smul E c, LinearMap.smul_comp, LinearMap.comp_smul]

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB N N' Ξ) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have h1 : ((cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b)) ∈ homAt S N N' := h.1 _ hx
    change ((cA : 𝓞 E) • x) ∈ homAt S (gmap g N) (gmap g' N')
    rwa [mem_homAt_gmap, conj_osmul]
  · obtain ⟨z, hz, rfl⟩ := hy
    have := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    refine Eq.trans ?_ this
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) =
      Ξ (_ + (cB : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap : HomE E a b))
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]

end Hom

variable {X : Fields} {n : ℕ}

theorem framed_gmap {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) fun P => g * fr P := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem rho_inv_apply (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem mem_localization_map {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (f : V →ₗ[𝓞 K] V) (hf : Function.Injective f) (M : Submodule (𝓞 K) V) (y : V) :
    f y ∈ localization₂ w.asIdeal (M.map f) ↔ y ∈ localization₂ w.asIdeal M := by
  rw [mem_locP, mem_locP]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← map_smul]
  exact ⟨fun ⟨z, hz, h⟩ => hf h ▸ hz, fun h => ⟨_, h, rfl⟩⟩

theorem rho_mem_valAt (w : HeightOneSpectrum (𝓞 X.K)) (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ) y ∈ valAt w lam (gmap γ.1 L) ↔ y ∈ valAt w lam L := by
  unfold valAt
  rw [delAtr_gmap]
  exact mem_localization_map w ((rhoVr X.emb lam (ufGL X.E n γ)).restrictScalars (𝓞 X.K))
    (Function.LeftInverse.injective (rho_inv_apply lam γ)) _ y

theorem pTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet (E := Z.X.E) (n := Z.R.N i) (ST := Z.Pr.vT u) (SG := SG)) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet (E := Z.X.E) (n := Z.R.N (i + 1)) (ST := Z.Pr.vT u) (SG := SG')) (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ((Z.Pr.T u : Z.X.K) ^ (((Z.X.f * Z.R.N i : ℕ) : ℤ) - ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift)) • term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.L) → PTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  have e1 : (((γ, 1) : UF Z.X.E (Z.R.N i) × GLG (E := Z.X.E) (n := Z.R.N i) (SG := SG)) • d).1.Lsh = gmap γ.1 d.1.Lsh :=
    Deco.Lsh_act d.1 γ.2 1
  have e2 : (((γ', 1) : UF Z.X.E (Z.R.N (i + 1)) × GLG (E := Z.X.E) (n := Z.R.N (i + 1)) (SG := SG')) • d').1.L = gmap γ'.1 d'.1.L :=
    Deco.L_act d'.1 γ'.1 1
  have h := hstd _ (fun P => γ.1 * fr P) _ (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩
    (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1) (inBox_gmap hbox γ.1 γ'.1) (fun _ => hint _)
    (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by rw [e1, rho_mem_valAt]; exact hy)
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, e2, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul,
    rho_mem_valAt] at h
  exact h

end GlobalTheory.KerT.PAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
section
open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.Inh.ResFin

theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

end GlobalTheory.LvT.Inh.ResFin
end

