module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PadicPlaceBound

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

def smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) : Ideal (𝓞 K) where
  carrier := {a | ‖φ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have h := IsUltrametricDist.norm_add_le_max (φ (a : K)) (φ (b : K))
    have h2 : φ ((a + b : 𝓞 K) : K) = φ (a : K) + φ (b : K) := by simp
    change ‖φ ((a + b : 𝓞 K) : K)‖ < 1
    rw [h2]
    exact h.trans_lt (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    have h2 : φ ((c • a : 𝓞 K) : K) = φ (c : K) * φ (a : K) := by simp
    change ‖φ ((c • a : 𝓞 K) : K)‖ < 1
    rw [h2, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral
      (map_isIntegral_int φ c.isIntegral_coe))).trans_lt ha

theorem mem_smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    a ∈ smallIdeal φ ↔ ‖φ (a : K)‖ < 1 := Iff.rfl

theorem norm_int_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    ‖φ (a : K)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int φ a.isIntegral_coe)

theorem smallIdeal_isPrime {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) :
    (smallIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    by_contra h
    rw [not_or, mem_smallIdeal, mem_smallIdeal, not_lt, not_lt] at h
    have h2 : φ ((a * b : 𝓞 K) : K) = φ (a : K) * φ (b : K) := by simp
    rw [mem_smallIdeal, h2, norm_mul] at hab
    exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)

theorem exists_embedding_smallIdeal_eq {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] {l : ℕ} (hl : l.Prime) (hlC : ‖(l : C)‖ < 1) (w : HeightOneSpectrum (𝓞 K))
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : ∃ φ : K →+* C, smallIdeal φ = w.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ φ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] C)) : Set (K →ₐ[ℚ] C)), (smallIdeal φ.toRingHom : Set (𝓞 K)) := by
    intro a ha
    by_contra hna
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
      not_exists, mem_smallIdeal, not_lt] at hna
    have h1 : ∀ φ : K →ₐ[ℚ] C, ‖φ (a : K)‖ = 1 := fun φ =>
      le_antisymm (norm_int_le_one φ.toRingHom a) (hna φ)
    have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ C (a : K))
    rw [norm_prod, Finset.prod_eq_one (fun φ _ => h1 φ), ← Algebra.coe_norm_int, map_intCast] at h2
    have h3 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).2 ha (Ideal.absNorm_mem _)
    rw [Ideal.absNorm_span_singleton] at h3
    have h4 : l ∣ (Algebra.norm ℤ a).natAbs := by
      by_contra hnd
      have hc : IsCoprime (l : 𝓞 K) (((Algebra.norm ℤ a).natAbs : ℕ) : 𝓞 K) :=
        Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨u, v, huv⟩ := hc
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hw) (w.asIdeal.mul_mem_left v h3)))
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h4
    rw [hc, Int.cast_mul, Int.cast_natCast, norm_mul] at h2
    have h5 := (mul_le_of_le_one_right (norm_nonneg (l : C))
      (IsUltrametricDist.norm_intCast_le_one C c)).trans_lt hlC
    exact absurd h2 h5.ne
  have φ₀ : K →ₐ[ℚ] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨φ, -, hφ⟩ := (Ideal.subset_union_prime φ₀ φ₀
    (fun φ _ _ _ => smallIdeal_isPrime φ.toRingHom)).1 hsub
  exact ⟨φ.toRingHom, (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hφ).symm⟩

theorem norm_le_one_of_valuation_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C)
    (w : HeightOneSpectrum (𝓞 K)) (hφ : smallIdeal φ = w.asIdeal) (y : K) (hy : w.valuation K y ≤ 1) :
    ‖φ y‖ ≤ 1 := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
  have hd' : d ∉ smallIdeal φ := by rw [hφ]; exact hd
  rw [mem_smallIdeal, not_lt] at hd'
  have h1 : ‖φ y‖ * ‖φ (d : K)‖ = ‖φ (n : K)‖ := by
    rw [← norm_mul, ← map_mul]
    exact congrArg (fun z => ‖φ z‖) hnd
  calc ‖φ y‖ ≤ ‖φ y‖ * ‖φ (d : K)‖ := le_mul_of_one_le_right (norm_nonneg _) hd'
    _ = ‖φ (n : K)‖ := h1
    _ ≤ 1 := norm_int_le_one φ n

theorem exists_lamC_eq {l : ℕ} [Fact l.Prime] (σ : K →+* ℂ) (φ : K →+* ℂ_[l]) :
    ∃ lam : Qbar →+* ℂ_[l], ∀ x : K, lamC lam (σ x) = φ x := by
  have hmem : ∀ x : K, σ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  let σ' : K →+* Qbar := σ.codRestrict Qbar hmem
  letI : Algebra K Qbar := σ'.toAlgebra
  letI : Algebra K ℂ_[l] := φ.toAlgebra
  haveI : IsScalarTower ℚ K Qbar := IsScalarTower.of_algebraMap_eq fun q =>
    ((eq_ratCast (algebraMap ℚ Qbar) q).trans (map_ratCast σ' q).symm).trans
      (congrArg σ' (eq_ratCast (algebraMap ℚ K) q).symm)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic K Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let lam : Qbar →ₐ[K] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lam.toRingHom, fun x => ?_⟩
  unfold lamC
  rw [dite_eq_left (hmem x)]
  exact lam.commutes x

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    ← Padic.norm_p]
  exact PadicAlgCl.norm_extends l _

theorem neg_mul_vw_le_vw : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (l : ℕ) [Fact l.Prime] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e : ℝ), x ≠ 0 → (l : 𝓞 K) ∈ w.asIdeal → (∀ lam : Qbar →+* ℂ_[l], ‖lamC lam (σ x)‖ ≤ (l : ℝ) ^ e) → -(e * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w x : ℝ) := by
  intro K _ _ σ x l hl w e hx hw h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := one_pos.trans hl1
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  obtain ⟨φ, hφ⟩ := exists_embedding_smallIdeal_eq (C := ℂ_[l]) hl.out
    (by rw [norm_prime_padicComplex]; exact inv_lt_one_of_one_lt₀ hl1) w hw
  obtain ⟨lam, hlam⟩ := exists_lamC_eq σ φ
  have hb := h lam
  rw [hlam] at hb
  have hvx : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x) := GlobalTheory.Idele.valuation_eq_exp_neg_count w hx
  have hvl : w.valuation K (l : K) = WithZero.exp (-Formalism.DivisionValues.vw w (l : K)) :=
    GlobalTheory.Idele.valuation_eq_exp_neg_count w hlK
  set n := Formalism.DivisionValues.vw w x
  set m := Formalism.DivisionValues.vw w (l : K)
  have hm : 0 ≤ m := by
    have h1 : w.valuation K (l : K) ≤ 1 := by
      simpa using w.valuation_le_one (K := K) (l : 𝓞 K)
    rw [hvl, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  have hy : w.valuation K ((l : K) ^ n / x ^ m) ≤ 1 := by
    rw [map_div₀, map_zpow₀, map_zpow₀, hvx, hvl, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
      ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    nlinarith
  have h1 := norm_le_one_of_valuation_le_one φ w hφ _ hy
  have hφx : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  rw [map_div₀, map_zpow₀, map_zpow₀, norm_div, norm_zpow, norm_zpow, map_natCast,
    norm_prime_padicComplex, div_le_one (zpow_pos hφx _)] at h1
  have h2 : ‖φ x‖ ^ m ≤ ((l : ℝ) ^ e) ^ m := zpow_le_zpow_left₀ hm hφx.le hb
  have h3 := h1.trans h2
  rw [inv_zpow', ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hl0.le,
    Real.rpow_le_rpow_left_iff hl1] at h3
  push_cast at h3
  linarith

end GlobalTheory.PadicPlaceBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OddTheta

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = latticeArea L := by
  have hA := latticeArea_eq L
  have hpos := latticeArea_pos L
  have key : ∀ w₁ ∈ L.lattice, ∀ w₂ ∈ L.lattice, ∃ k : ℤ,
      ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hw₁
    obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.1 hw₂
    refine ⟨m * n' - n * m', ?_⟩
    simp [Complex.mul_im, Complex.mul_re]
    ring
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hA ▸ hpos, L.ω₁, (h _).2 L.ω₁_mem_lattice, L.ω₂, (h _).2 L.ω₂_mem_lattice, hA⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := key w₁ ((h _).1 hw₁) w₂ ((h _).1 hw₂)
  rw [hk, abs_mul, ← hA] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left hpos.le hk1

theorem wpF_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) (z : ℂ) :
    wpF Λ z = L.weierstrassP z := by
  have hs : Summable (fun l : L.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) :=
    (L.hasSum_weierstrassP z).summable
  unfold wpF PeriodPair.weierstrassP
  rw [← hs.tsum_subtype_add_tsum_subtype_compl ({0} : Set L.lattice),
    tsum_singleton (0 : L.lattice) (fun l : L.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)]
  congr 1
  · simp
  · let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ (({0} : Set L.lattice)ᶜ : Set L.lattice) :=
      { toFun := fun w => ⟨⟨w.1, (h w.1).1 w.2.1⟩, fun hh =>
          w.2.2 (by simpa using congrArg Subtype.val (Set.mem_singleton_iff.1 hh))⟩
        invFun := fun l => ⟨l.1.1, (h _).2 l.1.2, fun hh =>
          l.2 (Set.mem_singleton_iff.2 (Subtype.ext (by simpa using hh)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (e.tsum_eq (fun l => 1 / (z - ((l : L.lattice) : ℂ)) ^ 2 - 1 / ((l : L.lattice) : ℂ) ^ 2))

theorem law_iff (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (ω z : ℂ) :
    U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z ↔
      G (z + ω) = sigmaSign L ω * Complex.exp (Real.pi * latticeForm L z ω +
        Real.pi * latticeForm L ω ω / 2) * G z := by
  have hs : (if ω / 2 ∈ Λ then (1 : ℂ) else -1) = sigmaSign L ω := by
    by_cases hw : ω / 2 ∈ Λ
    · rw [if_pos hw, sigmaSign_of_mem L ((h _).1 hw)]
    · rw [if_neg hw, sigmaSign_of_notMem L (fun hh => hw ((h _).2 hh))]
  have hU : U1 Λ ω G z = G (z + ω) *
      (Complex.exp (Real.pi * latticeForm L z ω + Real.pi * latticeForm L ω ω / 2))⁻¹ := by
    unfold U1
    rw [area_eq L Λ h, ← Complex.exp_neg]
    congr 2
    simp only [latticeForm]
    ring
  rw [hU, hs, mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)]
  constructor <;> intro hh <;> rw [hh] <;> ring

theorem eq_deriv_mul (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) (z : ℂ) :
    G z = deriv G 0 * canonicalSigma L z := by
  have hlaw' : ∀ w ∈ L.lattice, ∀ z, G (z + w) = sigmaSign L w *
      Complex.exp (Real.pi * latticeForm L z w + Real.pi * latticeForm L w w / 2) * G z :=
    fun w hw z => (law_iff L Λ h G w z).1 (hlaw w ((h w).2 hw) z)
  obtain ⟨c, hc⟩ := exists_eq_mul_canonicalSigma L hG hlaw'
  have hGf : G = fun z => c * canonicalSigma L z := funext hc
  have hd : deriv G 0 = c := by
    rw [hGf]
    exact ((hasDerivAt_canonicalSigma_zero L).const_mul c).deriv.trans (mul_one c)
  rw [hd]
  exact hc z

theorem canonicalSigma_spec (L : PeriodPair) (Λ : AddSubgroup ℂ)
    (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    Differentiable ℂ (canonicalSigma L) ∧ deriv (canonicalSigma L) 0 = 1 ∧
      (∀ z, canonicalSigma L (-z) = -canonicalSigma L z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω (canonicalSigma L) z =
        (if ω / 2 ∈ Λ then 1 else -1) * canonicalSigma L z := by
  refine ⟨differentiable_canonicalSigma L, (hasDerivAt_canonicalSigma_zero L).deriv,
    canonicalSigma_neg L, ?_⟩
  intro ω hω z
  exact (law_iff L Λ h _ ω z).2 (canonicalSigma_add L ((h ω).1 hω) z)

theorem sgStar_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    sgStar Λ = canonicalSigma L := by
  have hP : ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z :=
    ⟨_, canonicalSigma_spec L Λ h⟩
  unfold sgStar
  obtain ⟨hd, h1, -, hl⟩ := Classical.epsilon_spec hP
  funext z
  rw [eq_deriv_mul L Λ h _ hd hl z, h1, one_mul]

theorem exists_periodPair (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hind, rfl⟩ := hΛ
  refine ⟨⟨w₁, w₂, hind⟩, fun z => ?_⟩
  show z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ Submodule.span ℤ {w₁, w₂}
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]

theorem sgStar_laws : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  intro Λ hΛ
  obtain ⟨L, h⟩ := exists_periodPair Λ hΛ
  have hσ := sgStar_eq L Λ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ]
    exact canonicalSigma_spec L Λ h
  · intro z
    rw [hσ, canonicalSigma_eq_zero_iff L, h]
  · intro G hG hl z
    rw [hσ]
    exact eq_deriv_mul L Λ h G hG hl z
  · intro u v hu hv
    have hu' : u ∉ L.lattice := fun hh => hu ((h u).2 hh)
    have hv' : v ∉ L.lattice := fun hh => hv ((h v).2 hh)
    have hne : canonicalSigma L u ^ 2 * canonicalSigma L v ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hu'))
        (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hv'))
    rw [wpF_eq L Λ h, wpF_eq L Λ h, hσ, weierstrassP_sub_weierstrassP_canonicalSigma L hu' hv']
    exact div_mul_cancel₀ _ hne
  · intro c hc z
    have hhom := isHomothetic_scalePeriods L c hc
    have h' : ∀ x, x ∈ Λ.map (AddMonoidHom.mulLeft c) ↔ x ∈ (scalePeriods L c hc).lattice := by
      intro x
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hhom y).2 ((h y).1 hy)
      · intro hx
        refine ⟨c⁻¹ * x, (h _).2 ((hhom _).1 ?_), ?_⟩
        · rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        · simp [hc]
    rw [sgStar_eq (scalePeriods L c hc) _ h', hσ, hhom.canonicalSigma_mul]

end GlobalTheory.OddTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinates
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.OrthoCoord

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem embT_injective : Function.Injective (embT D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embT_indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, c τ * embT D τ x = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp
    (fun τ : D.what₂.Tau => ((embT D τ : D.host.E →+* ℂ) : D.host.E →* ℂ))
    (fun a b hab => embT_injective (RingHom.coe_monoidHom_injective hab))
  rw [Fintype.linearIndependent_iff] at h1
  refine h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply] using h x

theorem coordB_embV (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (j k : Fin r) :
    coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if j = k then 1 else 0 := by
  have h1 := h (∑ i, ∑ i', b k i i' * D.host.conj (b j i i'))
  have h2 := hb k j
  unfold hYY at h2
  rw [h2] at h1
  have h3 : coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) =
      ∑ τ, embT D τ (∑ i, ∑ i', b k i i' * D.host.conj (b j i i')) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coordB, embV, tor0, map_sum, map_mul, emb_conj]
  rw [h3, h1]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

theorem coordB_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (j : Fin r)
    (c : Fin r → ℂ) (v : Fin r → VC D a d) :
    coordB D T b j (∑ k, c k • v k) = ∑ k, c k * coordB D T b j (v k) := by
  let L : VC D a d →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b j
      map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  change L _ = ∑ k, c k * L (v k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

theorem embV_mem_span (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤)
    (A : Matrix (Fin d) (Fin a) D.host.E) :
    embV D (tor0 D cc δ) A ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => D.host.φ₀ (c k : D.host.E), ?_⟩
  funext τ i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [embV, tor0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← h τ, ← map_mul]
  rfl

theorem span_eq_top (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤) :
    Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  let e : D.what₂.Tau → Fin d → Fin a → VC D a d := fun τ i j => Pi.single τ (Pi.single i (Pi.single j 1))
  have hz : ∀ z : VC D a d, z = ∑ τ, ∑ i, ∑ j, z τ i j • e τ i j := by
    intro z
    funext τ i j
    simp [e, Finset.sum_apply, Pi.single_apply, ite_apply]
  have he : ∀ τ i j, f (e τ i j) = 0 := by
    intro τ i j
    refine embT_indep (fun τ => f (e τ i j)) (fun x => ?_) τ
    have h1 : f (embV D (tor0 D cc δ) (Matrix.single i j x)) = 0 := hf (embV_mem_span h cc δ hb _)
    have h2 : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • e τ i j := by
      funext τ' i' j'
      simp only [e, embV, tor0, Matrix.single_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply,
        smul_eq_mul]
      by_cases hi : i = i'
      · by_cases hj : j = j'
        · subst hi hj; simp
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    rw [h2] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul, mul_comm] using h1
  refine LinearMap.ext fun z => ?_
  rw [hz z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, he]

theorem orthonormal_coord : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  intro D h cc δ N N' r b hb
  refine ⟨coordB_embV h.2 cc δ hb.1, fun z => ?_⟩
  have hz : z ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
    rw [span_eq_top h.1 cc δ hb.2]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordB_sum]
  simp [coordB_embV h.2 cc δ hb.1]

end GlobalTheory.OrthoCoord
end
end

