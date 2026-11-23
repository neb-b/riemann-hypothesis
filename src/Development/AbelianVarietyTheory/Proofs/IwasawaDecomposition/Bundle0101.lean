module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubSelfDual
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.DetSD

variable {L : Type} [Field L] [NumberField L]

theorem exists_det_ge {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L)) (k : L) (hk0 : k ≠ 0)
    (hk : k ∈ detSub M) :
    ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧ w.valuation L k ≤ w.valuation L (Matrix.of x).det := by
  by_contra hn
  push Not at hn
  have h0 : w.valuation L k ≠ 0 := by simpa using hk0
  have key : ∀ z ∈ detSub M, w.valuation L z < w.valuation L k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      exact hn x hx
    | zero => rw [map_zero]; exact zero_lt_iff.2 h0
    | add x y _ _ hx hy => exact Valuation.map_add_lt _ hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (w.valuation_le_one r)) hx
  exact lt_irrefl _ (key k hk)

theorem coord_le_one {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L))
    (x : Fin N → Fin N → L) (hx : ∀ i, x i ∈ M) (hd : (Matrix.of x).det ≠ 0)
    (hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L (Matrix.of x).det) (m : Fin N → L) (hm : m ∈ M)
    (j : Fin N) : w.valuation L (Matrix.vecMul m (Matrix.of x)⁻¹ j) ≤ 1 := by
  have hu : IsUnit (Matrix.of x).det := IsUnit.mk0 _ hd
  have h1 := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose (Matrix.of x) m hu) j
  rw [Matrix.cramer_transpose_apply] at h1
  have h2 : ((Matrix.of x).updateRow j m).det ∈ detSub M := by
    refine det_mem_detSub (Function.update x j m) fun i => ?_
    by_cases h : i = j
    · subst h; simpa using hm
    · simpa [Function.update_of_ne h] using hx i
  have h3 := hmax _ h2
  rw [← h1, Pi.smul_apply, smul_eq_mul, map_mul] at h3
  have h0 : 0 < w.valuation L (Matrix.of x).det := zero_lt_iff.2 (by simpa using hd)
  exact (mul_le_iff_le_one_right h0).1 h3

theorem exists_den_prime {V : Type} [AddCommGroup V] [Module (𝓞 L) V] {N : ℕ} (M : Submodule (𝓞 L) V) (hM : M.FG)
    (w : HeightOneSpectrum (𝓞 L)) (f : Fin N → V → L) (hadd : ∀ j x y, f j (x + y) = f j x + f j y)
    (hsm : ∀ j (r : 𝓞 L) x, ∃ r' : 𝓞 L, f j (r • x) = r' • f j x)
    (hf : ∀ j, ∀ m ∈ M, w.valuation L (f j m) ≤ 1) :
    ∃ s : 𝓞 L, s ∉ w.asIdeal ∧ ∀ j, ∀ m ∈ M, (s : L) * f j m ∈ (algebraMap (𝓞 L) L).range := by
  classical
  obtain ⟨t, rfl⟩ := hM
  have := w.isPrime
  choose n d h using fun p : Fin N × t => w.exists_primeCompl_mul_eq_of_integer (f p.1 p.2)
    (hf p.1 p.2 (Submodule.subset_span p.2.2))
  refine ⟨((∏ p, d p : w.asIdeal.primeCompl) : 𝓞 L), (∏ p, d p).2, fun j m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, (⟨x, hx⟩ : t)))]
    refine ⟨((∏ p ∈ Finset.univ.erase (j, (⟨x, hx⟩ : t)), d p : w.asIdeal.primeCompl) : 𝓞 L) * n (j, ⟨x, hx⟩), ?_⟩
    rw [map_mul, ← h]
    simp only [Submonoid.coe_mul]
    push_cast
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero =>
    obtain ⟨r, hr⟩ := hsm j 0 0
    have h0 : f j 0 = 0 := by simpa using hadd j 0 0
    rw [h0, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd, mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := hsm j r x
    rw [hr, Algebra.smul_def, mul_left_comm]
    exact mul_mem ⟨r', rfl⟩ hx

variable [StarRing L]

theorem star_integer (r : 𝓞 L) : ∃ r' : 𝓞 L, (r' : L) = star (r : L) :=
  ⟨RingOfIntegers.mapRingEquiv (starRingAut : RingAut L) r, rfl⟩

theorem star_mul_integer {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L))
    (hM : ∀ y ∈ M, ∀ x ∈ M, stdH L N x y ∈ (algebraMap (𝓞 L) L).range) (a b : L) (ha : a ∈ detSub M)
    (hb : b ∈ detSub M) : star a * b ∈ (algebraMap (𝓞 L) L).range := by
  induction ha using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    induction hb using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      have e : star (Matrix.of x).det * (Matrix.of y).det = (Matrix.of fun i j => stdH L N (x j) (y i)).det := by
        rw [← Matrix.det_conjTranspose, mul_comm, ← Matrix.det_mul]
        congr 1
        ext i j
        simp [Matrix.mul_apply, stdH, mul_comm]
      rw [e]
      exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hM _ (hy i) _ (hx j)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Algebra.smul_def, mul_left_comm]; exact mul_mem ⟨r, rfl⟩ hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, add_mul]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := star_integer r
    rw [Algebra.smul_def, star_mul', mul_assoc]
    exact mul_mem ⟨r', hr⟩ hx

theorem ordSub_add_eq_zero {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : IsSDLat L N M)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : ∀ x : L, w'.valuation L (star x) = w.valuation L x) :
    ordSub w (detSub M) + ordSub w' (detSub M) = 0 := by
  obtain ⟨hfg, hsp, hsd⟩ := hM
  have hl := (ordSub_detSub_lattice L N M hfg hsp).2.1
  obtain ⟨⟨k, hk, ek⟩, hkl⟩ := hl w
  obtain ⟨⟨k', hk', ek'⟩, hkl'⟩ := hl w'
  have nz : ∀ (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ), v.valuation L (a : L) ≠ 0 := fun v a => by simp
  apply le_antisymm
  · obtain ⟨x, hx, hxk⟩ := exists_det_ge M w k k.ne_zero hk
    have hd : (Matrix.of x).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hxk
      exact nz w k (le_zero_iff.1 hxk)
    have hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L k := by
      intro z hz
      by_cases h0 : z = 0
      · simp [h0]
      · have h1 := hkl ⟨Units.mk0 z h0, hz, rfl⟩
        rw [← ek] at h1
        exact (WithZero.log_le_log (nz w (Units.mk0 z h0)) (nz w k)).1 (neg_le_neg_iff.1 h1)
    have hdk : w.valuation L (Matrix.of x).det = w.valuation L k := le_antisymm (hmax _ (det_mem_detSub x hx)) hxk
    have hc := coord_le_one M w x hx hd (fun z hz => hdk ▸ hmax z hz)
    set Y : Matrix (Fin N) (Fin N) L := ((Matrix.of x)⁻¹).conjTranspose with hY
    have hf : ∀ j m, stdH L N m (Y j) = star (Matrix.vecMul m (Matrix.of x)⁻¹ j) := by
      intro j m
      simp [stdH, hY, Matrix.vecMul, dotProduct]
    obtain ⟨s, hs, hint⟩ := exists_den_prime M hfg w' (fun j m => stdH L N m (Y j))
      (fun j a b => by simp [stdH, add_mul, Finset.sum_add_distrib])
      (fun j r a => by
        obtain ⟨r', hr⟩ := star_integer r
        refine ⟨r', ?_⟩
        have hr' : algebraMap (𝓞 L) L r' = star (algebraMap (𝓞 L) L r) := hr
        simp [stdH, Algebra.smul_def, hr', Finset.mul_sum, mul_assoc])
      (fun j m hm => by
        show w'.valuation L (stdH L N m (Y j)) ≤ 1
        rw [hf, hw]; exact hc m hm j)
    have hsY : ∀ j, ((s : L) • Y) j ∈ M := fun j => (hsd _).2 fun m hm => by
      have := hint j m hm
      convert this using 1
      simp [stdH, Finset.mul_sum, mul_left_comm]
    have hmem : ((s : L) • Y).det ∈ detSub M := det_mem_detSub (fun j => ((s : L) • Y) j) hsY
    have hsv : w'.valuation L (s : L) = 1 :=
      le_antisymm (w'.valuation_le_one s) (not_lt.1 fun h => hs ((w'.valuation_lt_one_iff_mem s).1 h))
    have hval : w'.valuation L ((s : L) • Y).det = (w.valuation L k)⁻¹ := by
      rw [Matrix.det_smul, map_mul, map_pow, hsv, one_pow, one_mul, hY, Matrix.det_conjTranspose, hw,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hdk]
    have h0 : ((s : L) • Y).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hval
      exact inv_ne_zero (nz w k) hval.symm
    have h1 := hkl' ⟨Units.mk0 _ h0, hmem, rfl⟩
    have h2 : ordF w' (Units.mk0 _ h0) = -ordF w k := by
      unfold ordF
      rw [Units.val_mk0, hval, WithZero.log_inv]
    omega
  · have h1 := star_mul_integer M (fun y hy => (hsd y).1 hy) k k' hk hk'
    have h2 := DetOrd.ordF_nonneg_of_isInteger w' (star k * k') h1
    rw [DetOrd.ordF_mul'] at h2
    have h3 : ordF w' (star k) = ordF w k := by
      unfold ordF
      rw [Units.coe_star, hw]
    omega

end GlobalTheory.Mem.Chr.DetSD

namespace GlobalTheory.Mem.Chr


open Classical in
theorem ordSub_detSub_selfDual : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; ∀ (M : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' → ordSub w (detSub M.1) + ordSub w' (detSub M.1) = 0 := by
  intro R H N
  letI := H.cmStar
  intro M w w' h
  have hc : ConjPl H.conj.toRingEquiv w w' := (conjPl_main.2.1 R H w w').1 h
  refine DetSD.ordSub_add_eq_zero M.1 M.2 w w' fun x => ?_
  have := H.isCMField_hostE
  have e : star x = H.conj x :=
    H.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ H.φ₀ x).trans
      (H.conjE_apply H.φ₀ x).symm)
  rw [e]
  exact hc x

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.GoodPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem plc_eq_absNorm (v : HeightOneSpectrum (𝓞 F)) (h : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have := v.isPrime
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  unfold Formalism.EigenvalueLevelCeiling.plc
  apply CharP.ringChar_of_prime_eq_zero h
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem _

theorem absNorm_map (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_under_dvd (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (P.under (𝓞 F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) le_rfl).toAddMonoidHom Ideal.quotientMap_injective

theorem of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.L2.DIV.DegOne v)
    {Q Q' : HeightOneSpectrum (𝓞 E)} (hne : Q ≠ Q')
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal) (hQ : Q.under (𝓞 F) = v) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, absNorm_map h2]
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  refine ⟨((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1, ?_⟩
  intro hmem
  have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
    Ideal.dvd_span_singleton.2 hqv
  have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_span_singleton.2 hmem
  rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
  rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
  · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
  · have hle : I ≤ v.asIdeal := by
      rw [← hQ]
      exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hv.2
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
    exact Ideal.mul_mono_right hle

theorem under_eq_of_map_eq {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} {J : Ideal (𝓞 E)}
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * J) : Q.under (𝓞 F) = v := by
  refine (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top ?_)).symm
  exact Ideal.map_le_iff_le_comap.1 (hm ▸ Ideal.mul_le_left)

theorem map_eq_mul (h2 : Module.finrank F E = 2) {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hu : P'.under (𝓞 F) = P.under (𝓞 F)) :
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal * P'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_isCoprime (HeightOneSpectrum.isCoprime_of_ne P P' hne)]
    refine le_inf Ideal.map_comap_le ?_
    rw [← hu]
    exact Ideal.map_comap_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := absNorm_map h2 (P.under (𝓞 F)).asIdeal
  obtain ⟨a, ha⟩ := absNorm_under_dvd (F := F) P
  obtain ⟨b, hb⟩ := absNorm_under_dvd (F := F) P'
  rw [hu] at hb
  have h0 : Ideal.absNorm (P.under (𝓞 F)).asIdeal ≠ 0 := fun h => (P.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  rw [hJ, map_mul, map_mul, ha, hb] at hN
  have h3 : (a * b) * Ideal.absNorm J = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 h0)
    rw [mul_one]
    refine Eq.trans ?_ hN
    ring
  rw [hJ, Ideal.absNorm_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_left h3), Ideal.mul_top]

theorem goodPl_iff (h2 : Module.finrank F E = 2) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.GoodPl E S (P.under (𝓞 F)) ↔ ((∃ P', P ≠ P' ∧ P'.under (𝓞 F) = P.under (𝓞 F)) ∧
      (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧
      Ideal.absNorm P.asIdeal ∉ S) := by
  constructor
  · rintro ⟨⟨Q, Q', hne, hm⟩, hv, hS⟩
    obtain ⟨P', hne', hm'⟩ : ∃ P', P ≠ P' ∧
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
      have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
        rw [← hm]
        exact Ideal.map_comap_le
      rcases P.isPrime.mul_le.1 hle with h | h
      · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q', hne, hm⟩
      · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q, hne.symm, by rw [hm, mul_comm]⟩
    obtain ⟨e, hn⟩ := of_split h2 hv hne' hm' rfl
    rw [plc_eq_absNorm _ hv.1] at hS
    rw [e]
    exact ⟨⟨P', hne', under_eq_of_map_eq (hm'.trans (mul_comm _ _))⟩, hv.1, hn, hS⟩
  · rintro ⟨⟨P', hne, hu⟩, hp, hn, hS⟩
    have e : Ideal.absNorm (P.under (𝓞 F)).asIdeal = Ideal.absNorm P.asIdeal :=
      ((Nat.dvd_prime hp).1 (absNorm_under_dvd P)).resolve_left fun h =>
        (P.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    refine ⟨⟨P, P', hne, map_eq_mul h2 hne hu⟩, ⟨e ▸ hp, fun h => hn ?_⟩, ?_⟩
    · rw [e] at h
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
      rw [map_natCast, Ideal.map_pow] at h3
      exact Ideal.pow_right_mono Ideal.map_comap_le 2 h3
    · rw [plc_eq_absNorm _ (e ▸ hp), e]
      exact hS

end General

theorem isSplitPl_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (P : HeightOneSpectrum (𝓞 H.E)) :
    IsSplitPl H P ↔ ∃ P', P ≠ P' ∧ P'.under (𝓞 H.F) = P.under (𝓞 H.F) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨P', hP', -⟩ := existsUnique_conjPl c.toRingEquiv P
    refine ⟨P', ?_, (under_eq_iff_conjPl c hcm.rank hcm.ne P P').2 (Or.inr hP')⟩
    rintro rfl
    exact hy (RingOfIntegers.mapRingEquiv c.toRingEquiv x) (hc x) (((conjPl_iff_mem _ P P).1 hP' x _ rfl).1 hx)
  · rintro ⟨P', hne, hu⟩
    have hP' := ((under_eq_iff_conjPl c hcm.rank hcm.ne P P').1 hu).resolve_left hne.symm
    rw [conjPl_iff_mem] at hP'
    by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    refine hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun y hy => ?_).symm)
    have hxy : (y : H.E) = c.toRingEquiv ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm y : 𝓞 H.E) :=
      congrArg (fun z : 𝓞 H.E => (z : H.E)) ((RingOfIntegers.mapRingEquiv c.toRingEquiv).apply_symm_apply y).symm
    obtain ⟨z, hz, hzP⟩ := hn _ ((hP' _ y hxy).2 hy)
    have e : z = y := RingOfIntegers.ext (hz.trans ((hc _).symm.trans hxy.symm))
    exact e ▸ hzP


open Classical in
theorem goodPl_under_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 H.E)), Formalism.L2.DIV.GoodPl H.E S (P.under (𝓞 H.F)) ↔ (IsSplitPl H P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2 ∧ Ideal.absNorm P.asIdeal ∉ S) := by
  intro R H S P
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [isSplitPl_iff]
  exact goodPl_iff hcm.rank S P

end GlobalTheory.Mem.GoodPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedEqOneOfLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.TupHecke

section General

variable {L : Type} [Field L] [NumberField L]

abbrev FI (L : Type) [Field L] [NumberField L] : Type := (FiniteAdeleRing (𝓞 L) L)ˣ

def sing (P : HeightOneSpectrum (𝓞 L)) : (P.adicCompletion L)ˣ →* FI L := Units.map (finiteSingle L P)

def cmp (P : HeightOneSpectrum (𝓞 L)) : FI L →* (P.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a P, map_one' := rfl, map_mul' := fun _ _ => rfl }



variable (L) in
def finP : Neutral.B1.Ideles L →* FI L := Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem cmp_val (P : HeightOneSpectrum (𝓞 L)) (u : FI L) :
    (cmp P u : P.adicCompletion L) = (u : FiniteAdeleRing (𝓞 L) L) P := rfl

open Classical in
theorem cmp_sing_self (P : HeightOneSpectrum (𝓞 L)) (x) : cmp P (sing P x) = x := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) P x P = x
  exact Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) P _ _

open Classical in
theorem cmp_sing_ne {P Q : HeightOneSpectrum (𝓞 L)} (h : P ≠ Q) (x) : cmp P (sing Q x) = 1 := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) Q x P = 1
  exact Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) h _ _


theorem valued_eq_one_of_le {P : HeightOneSpectrum (𝓞 L)} (x : (P.adicCompletion L)ˣ)
    (h : Valued.v (x : P.adicCompletion L) ≤ 1) (h' : Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≤ 1) :
    Valued.v (x : P.adicCompletion L) = 1 := by
  refine le_antisymm h ?_
  have e : Valued.v (x : P.adicCompletion L) * Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact e.symm.le.trans (mul_le_of_le_one_right' h')

theorem finite_nonunit (u : FI L) : {P | ¬ IsUnitAt P (cmp P u)}.Finite := by
  have h1 := Filter.eventually_cofinite.1 (u : FiniteAdeleRing (𝓞 L) L).2
  have h2 := Filter.eventually_cofinite.1 ((u⁻¹ : FI L) : FiniteAdeleRing (𝓞 L) L).2
  refine (h1.union h2).subset fun P hP => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hP (valued_eq_one_of_le _ hn.1 hn.2)

theorem finite_nat {N : ℕ} (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | Valued.v (N : P.adicCompletion L) ≠ 1}.Finite := by
  refine (finite_nonunit (Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom
    (Units.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')))).subset fun P hP h => hP ?_
  rw [← map_natCast (algebraMap L (P.adicCompletion L))]
  exact h

def Cong (N : ℕ) (u : FI L) : Prop :=
  ∀ P, IsUnitAt P (cmp P u) ∧ Valued.v ((cmp P u : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)

variable {G : Type} [CommGroup G]

theorem cong_sing {N : ℕ} {P : HeightOneSpectrum (𝓞 L)} {x : (P.adicCompletion L)ˣ} (h : IsUnitAt P x)
    (h' : Valued.v ((x : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)) : Cong N (sing P x) := by
  intro Q
  by_cases e : Q = P
  · subst e
    rw [cmp_sing_self]
    exact ⟨h, h'⟩
  · rw [cmp_sing_ne e]
    simp [IsUnitAt]

theorem continuous_finP {N : ℕ} (hN : 0 < N) (ψ : FI L →* ℂˣ) (hψ : ∀ u, Cong N u → ψ u = 1) :
    Continuous (ψ.comp (finP L)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ P, P ∉ T → Valued.v (N : P.adicCompletion L) = 1 :=
    ⟨(finite_nat (L := L) hN).toFinset, fun P hP => by simpa using hP⟩
  choose n hn using fun P : HeightOneSpectrum (𝓞 L) =>
    GlobalTheory.Idele.exists_exp_neg_lt (GlobalTheory.AdLat.valued_natCast_ne_zero P hN)
  have ho := (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).2 T (T.sup n)
  have h1 := ho.mem_nhds (x := (1 : Neutral.B1.Ideles L)) ⟨one_mem _, fun v _ => by
    have : ((1 : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 := rfl
    rw [this, sub_self, map_zero]
    exact zero_le⟩
  have h2 : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : Neutral.B1.Ideles L)] (ψ.comp (finP L)) := by
    filter_upwards [h1] with a ha
    have hu : ∀ P, IsUnitAt P (cmp P (finP L a)) := ha.1
    refine (hψ (finP L a) fun P => ⟨hu P, ?_⟩).symm
    by_cases hP : P ∈ T
    · refine le_trans (ha.2 P hP) (le_trans ?_ (hn P).le)
      rw [WithZero.exp_le_exp]
      have := Finset.le_sup (f := n) hP
      omega
    · rw [hT P hP]
      exact Valuation.map_sub_le _ (hu P).le (by simp)
  exact continuous_of_continuousAt_one _ (continuousAt_const.congr h2)

end General

end GlobalTheory.Mem.TupHecke
end
end

