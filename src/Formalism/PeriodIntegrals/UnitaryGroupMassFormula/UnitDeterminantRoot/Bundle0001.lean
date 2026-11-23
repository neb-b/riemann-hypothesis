module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
public import Lemmata.GeneralBFactLeftTer.Imports

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

lemma conj_theta (b : ℤ) (d : ℕ) : conj (UnitDetRootDefs.cmTheta b d) = (b : ℂ) - UnitDetRootDefs.cmTheta b d := by
  simp only [UnitDetRootDefs.cmTheta, map_div₀, map_add (f := _), map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast,
    map_ofNat]
  ring

theorem conjMem : ConjMem := by
  intro b d x hx
  have hle : KF b d ≤ IntermediateField.comap ((starRingEnd ℂ).toRatAlgHom) (KF b d) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    show conj (UnitDetRootDefs.cmTheta b d) ∈ KF b d
    rw [conj_theta]
    exact sub_mem (IntermediateField.intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
  exact hle hx

theorem conjLUnit : ConjLUnit := by
  rintro l x ⟨hx0, k, hk, h1, h2⟩
  refine ⟨(map_ne_zero _).mpr hx0, k, hk, ?_, ?_⟩
  · have h := h1.map (starRingEnd ℂ).toIntAlgHom
    change IsIntegral ℤ (conj ((k : ℂ) * x)) at h
    rwa [map_mul, map_natCast] at h
  · have h := h2.map (starRingEnd ℂ).toIntAlgHom
    change IsIntegral ℤ (conj ((k : ℂ) * x⁻¹)) at h
    rwa [map_mul, map_natCast, map_inv₀] at h

lemma norm_le_one_of_root {F : Type*} [NormedField F] [IsUltrametricDist F] {y : F}
    (p : Polynomial ℤ) (hp : p.Monic) (hpy : p.eval₂ (Int.castRingHom F) y = 0) : ‖y‖ ≤ 1 := by
  first | exact Bl.general_b_fact_left_ter.goal1 .. | (apply Bl.general_b_fact_left_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_ter.goal1 <;> assumption)

lemma norm_iota_natCast (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (k : ℕ) (hk : ¬ l ∣ k) :
    ‖ι (k : ℂ)‖ = 1 := by
  rw [map_natCast]
  have e : ((k : ℚ_[l]) : ℂ_[l]) = (k : ℂ_[l]) := by simp
  rw [← e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hk

theorem normOne : NormOne := by
  rintro l _ ι x ⟨hx0, k, hk, h1, h2⟩
  have hI : ∀ z : ℂ, IsIntegral ℤ z → ‖ι z‖ ≤ 1 := by
    rintro z ⟨p, hp, hpz⟩
    apply norm_le_one_of_root p hp
    have h : (ι.toRingHom) (p.eval₂ (algebraMap ℤ ℂ) z) = 0 := by rw [hpz, map_zero]
    rw [Polynomial.hom_eval₂, RingHom.ext_int (ι.toRingHom.comp (algebraMap ℤ ℂ)) (Int.castRingHom _)] at h
    exact h
  have e1 := hI _ h1
  have e2 := hI _ h2
  rw [map_mul, norm_mul, norm_iota_natCast l ι k hk, one_mul] at e1 e2
  have e3 : ‖ι x‖ * ‖ι x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι x⁻¹)]

lemma theta_sq {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) :
    UnitDetRootDefs.cmTheta b d ^ 2 = b * UnitDetRootDefs.cmTheta b d - (a : ℂ) * c := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have h4 : (4 : ℂ) * a * c = b ^ 2 + d := by exact_mod_cast hok.1
  simp only [UnitDetRootDefs.cmTheta]
  linear_combination (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) / 4) * Complex.I_mul_I
    - (1 / 4 : ℂ) * hs + (1 / 4 : ℂ) * h4

lemma theta_isIntegral {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : IsIntegral ℚ (UnitDetRootDefs.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C ((a : ℚ) * c), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    linear_combination theta_sq hok

lemma sigma_on_KF {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) (σ : ℂ ≃+* ℂ) :
    (∀ x ∈ KF b d, σ x = x) ∨ (∀ x ∈ KF b d, σ x = conj x) := by
  have hq : (σ (UnitDetRootDefs.cmTheta b d) - UnitDetRootDefs.cmTheta b d) * (σ (UnitDetRootDefs.cmTheta b d) - conj (UnitDetRootDefs.cmTheta b d)) = 0 := by
    have h := congrArg σ (theta_sq hok)
    simp only [map_pow, map_sub, map_mul, map_intCast, map_natCast] at h
    rw [conj_theta]
    linear_combination h - theta_sq hok
  have key : ∀ f : ℂ →+* ℂ, σ (UnitDetRootDefs.cmTheta b d) = f (UnitDetRootDefs.cmTheta b d) → ∀ x ∈ KF b d, σ x = f x := by
    intro f hf x hx
    let S : Subfield ℂ := RingHom.eqLocusField σ.toRingHom f
    let E : IntermediateField ℚ ℂ := S.toIntermediateField (fun q => by
      show σ (algebraMap ℚ ℂ q) = f (algebraMap ℚ ℂ q)
      simp [eq_ratCast])
    have hle : KF b d ≤ E := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact hf
    exact hle hx
  rcases mul_eq_zero.mp hq with h | h
  · exact Or.inl (key (RingHom.id ℂ) (sub_eq_zero.mp h))
  · exact Or.inr (key (starRingEnd ℂ) (sub_eq_zero.mp h))

theorem rootStep : RootStep := by
  intro a b c d hok β hβ hββ N hN
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq β⁻¹ hN
  have hnorm : ‖β‖ = 1 := by
    have h := congrArg (fun z => ‖z‖) hββ
    simp only [norm_mul, Complex.norm_conj, norm_one] at h
    nlinarith [norm_nonneg β]
  refine ⟨κ, hκ, ?_, ?_⟩
  · have := IntermediateField.adjoin.finiteDimensional (theta_isIntegral hok)
    have hβi : β⁻¹ ∈ KF b d := inv_mem hβ
    have : IsIntegral ℚ β⁻¹ := by
      have h := (Algebra.IsIntegral.isIntegral (R := ℚ) (⟨β⁻¹, hβi⟩ : KF b d)).map (KF b d).val
      simpa using h
    exact IsAlgebraic.of_pow hN (hκ ▸ this.isAlgebraic)
  · intro σ
    have h1 : ‖σ κ‖ ^ N = 1 := by
      rw [← norm_pow, ← map_pow, hκ, map_inv₀, norm_inv]
      rcases sigma_on_KF hok σ with h | h
      · rw [h β hβ, hnorm, inv_one]
      · rw [h β hβ, Complex.norm_conj, hnorm, inv_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

section Basic

variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

lemma cmL_ω₁ : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁ = lam * a := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]

lemma cmL_ω₂ : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₂ = lam * UnitDetRootDefs.cmTheta b d := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]

lemma mem_cmL {x : ℂ} :
    x ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice ↔ ∃ p q : ℤ, x = lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d) := by
  rw [PeriodPair.mem_lattice, cmL_ω₁, cmL_ω₂]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [← h]; ring⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [h]; ring⟩

lemma mem_stdLat {m : Type} {L : PeriodPair} {x : m → ℂ} : x ∈ UnitDetRootDefs.stdLat L m ↔ ∀ i, x i ∈ L.lattice := by
  simp [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]

lemma theta_re' : (UnitDetRootDefs.cmTheta b d).re = (b : ℝ) / 2 := by simp [UnitDetRootDefs.cmTheta]

lemma theta_im' : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by simp [UnitDetRootDefs.cmTheta]

lemma area_cmL : UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
  rw [UnitDetRootDefs.area, cmL_ω₁, cmL_ω₂]
  have hpos : 0 < Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have e : (conj (lam * a) * (lam * UnitDetRootDefs.cmTheta b d)).im = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re,
      Complex.natCast_im, theta_re', theta_im', Complex.normSq_apply, map_mul, map_natCast]
    ring
  rw [e, abs_of_pos hpos]

lemma pair_im (p q p' q' : ℤ) :
    ((lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d)) * conj (lam * ((p' : ℂ) * a + (q' : ℂ) * UnitDetRootDefs.cmTheta b d))).im
      = Complex.normSq lam * a * (Real.sqrt d / 2) * ((q * p' - p * q' : ℤ) : ℝ) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, theta_re', theta_im',
    Complex.normSq_apply, map_mul, map_add, map_intCast, map_natCast]
  push_cast
  ring

end Basic

lemma stdH_apply {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.stdH L m x y = ∑ i, x i * ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * conj (y i) := by
  simp [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply]

lemma altE_stdH {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.altE (UnitDetRootDefs.stdH L m) x y = ∑ i, (x i * conj (y i)).im / UnitDetRootDefs.area L := by
  rw [UnitDetRootDefs.altE, stdH_apply, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (x i), mul_assoc, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  field_simp

lemma stdLat_le_dual {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {x : m → ℂ} (hx : x ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) :
    x ∈ UnitDetRootDefs.dualLat (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) := by
  intro y hy
  rw [mem_stdLat] at hx hy
  choose p q hpq using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hx i)
  choose p' q' hpq' using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hy i)
  refine ⟨∑ i, (q i * p' i - p i * q' i), ?_⟩
  rw [altE_stdH]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpq i, hpq' i, pair_im, area_cmL]
  have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  push_cast
  field_simp

lemma nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (H K : AddSubgroup V) {x : V} (hx : x ∈ K) :
    (H.relIndex K) • x ∈ H := by
  have h := (H.addSubgroupOf K).nsmul_index_mem ⟨x, hx⟩
  rw [AddSubgroup.relIndex]
  simpa [AddSubgroup.mem_addSubgroupOf] using h

lemma altE_natsmul {V : Type*} [AddCommGroup V] [Module ℂ V] (H : UnitDetRootDefs.Sesq V) (k : ℕ) (x y : V) :
    UnitDetRootDefs.altE H ((k : ℂ) • x) y = UnitDetRootDefs.altE H x ((k : ℂ) • y) := by
  simp [UnitDetRootDefs.altE, LinearMap.map_smulₛₗ]

lemma mem_imgLat {m : Type} {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} {Λ : AddSubgroup (m → ℂ)} {z : m → ℂ} :
    z ∈ UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ ↔ δ.symm z ∈ Λ := by
  simp only [UnitDetRootDefs.imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨δ.symm z, h, by simp⟩

theorem localStd : LocalStd := by
  intro a b c d ha hd lam hlam m _ _ Λa hH l _ δ hA hl
  obtain ⟨hok, hsd, hth, hi1, hi2⟩ := hH
  obtain ⟨hiso, hc1, hc2⟩ := hA
  set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt
  set H := UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hHdef
  set M := UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hM
  set k := UnitDetRootDefs.relIdx Lt M with hk
  have partA : ∀ x ∈ M, (k : ℂ) • x ∈ Lt := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_relIdx_mem Lt M hx
  have hdualM : ∀ z, z ∈ UnitDetRootDefs.dualLat H M → z ∈ M := by
    intro z hz
    rw [hM, mem_imgLat]
    rw [UnitDetRootDefs.IsSelfDual] at hsd
    rw [← hsd]
    intro y hy
    have hδy : δ y ∈ M := by rw [hM, mem_imgLat]; simpa using hy
    obtain ⟨n, hn⟩ := hz (δ y) hδy
    refine ⟨n, ?_⟩
    rw [← hn, UnitDetRootDefs.altE, UnitDetRootDefs.altE, ← hiso (δ.symm z) y]
    simp
  refine ⟨k, hl, fun x hx => hdualM _ ?_, partA⟩
  intro y hy
  rw [altE_natsmul]
  exact stdLat_le_dual hx _ (partA y hy)

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.UnitDetRootOf
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

theorem unitDetRoot_of (h1 : DetInK) (h2 : LocalStd) (h3 : GlobalLUnit) (h4 : NormOne)
    (h5 : RootStep) (h6 : ConjMem) (h7 : ConjLUnit) : PI.UnitDetRoot := by
  intro a b c d ha hd lam hlam hOK m _ _ Λa hSD hθ hi1 hi2
  have hH : Hyp a b c d ha hd lam hlam m Λa := ⟨hOK, hSD, hθ, hi1, hi2⟩
  obtain ⟨γ, hγK, hγ0, n, hn, hγ⟩ := h3 a b c d ha hd lam hlam m Λa hH
  have hγc0 : conj γ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hγ0
  have hβK : γ / conj γ ∈ KF b d := div_mem hγK (h6 b d γ hγK)
  have hββ : γ / conj γ * conj (γ / conj γ) = 1 := by
    rw [map_div₀, Complex.conj_conj]
    field_simp
  obtain ⟨κ, hκN, hκalg, hκσ⟩ := h5 a b c d hOK (γ / conj γ) hβK hββ (4 * n) (by omega)
  refine ⟨κ, ?_, hκalg, hκσ, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega), eq_comm, inv_eq_zero, div_eq_zero_iff] at hκN
    exact hκN.elim hγ0 hγc0
  · intro l _ ι δ hIso hidx1 hnl hidx2
    have hA : admitted a b d ha hd lam hlam m Λa δ := ⟨hIso, hidx1, hidx2⟩
    have hEq := h2 a b c d ha hd lam hlam m Λa hH l δ hA hnl
    have hU := hγ l δ hA hEq
    have n1 := h4 l ι _ hU
    have n2 := h4 l ι _ (h7 l _ hU)
    obtain ⟨-, hdd⟩ := h1 a b c d ha hd lam hlam m Λa hH δ hA
    set D := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hD
    have hD0 : D ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hdd
      exact zero_ne_one hdd
    have hDc : conj D = D⁻¹ := eq_inv_of_mul_eq_one_right hdd
    have hu0 : 0 < ‖ι D‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hD0)
    have hDc0 : conj D ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hD0
    have n1' : ‖ι γ‖ = ‖ι D‖ ^ n := by
      have e : γ = (γ / D ^ n) * D ^ n := by field_simp
      rw [e, map_mul, norm_mul, n1, one_mul, map_pow, norm_pow]
    have n2' : ‖ι (conj γ)‖ = ‖ι D‖⁻¹ ^ n := by
      have e : conj γ = conj (γ / D ^ n) * (conj D) ^ n := by
        rw [map_div₀, map_pow]
        field_simp
      rw [e, map_mul, norm_mul, n2, one_mul, map_pow, norm_pow, hDc, map_inv₀, norm_inv]
    have e3 : ‖ι κ‖ ^ (4 * n) = ‖ι (conj γ)‖ / ‖ι γ‖ := by
      rw [← norm_pow, ← map_pow, hκN, inv_div, map_div₀, norm_div]
    have ht : (‖ι κ‖ ^ 2 * ‖ι D‖) ^ (2 * n) = 1 := by
      rw [mul_pow, ← pow_mul, show 2 * (2 * n) = 4 * n by ring, e3, n1', n2', inv_pow]
      field_simp
      ring
    exact (pow_eq_one_iff_of_nonneg (by positivity) (by omega)).mp ht

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

