module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def levCongr {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (e : M ≃ₗ[O] N) (c : O) : Lev M c ≃ Lev N c where
  toFun x := Lev.mk (e x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  invFun y := Lev.mk (e.symm y.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  left_inv x := Lev.ext (by simp [Lev.val_mk])
  right_inv y := Lev.ext (by simp [Lev.val_mk])

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def divPowQ (ϖ : O) (n : ℕ) : O →ₗ[O] Formalism.NG.KO O :=
  (1 : Submodule O (FractionRing O)).mkQ ∘ₗ
    LinearMap.mulLeft O ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹) ∘ₗ
      Algebra.linearMap O (FractionRing O)

theorem divPowQ_apply (ϖ : O) (n : ℕ) (a : O) :
    divPowQ ϖ n a = Submodule.Quotient.mk
      ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem ker_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.ker (divPowQ ϖ n) = Ideal.span {ϖ ^ n} := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext a
  rw [LinearMap.mem_ker, divPowQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [map_mul, map_pow, hb, mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, mul_comm (algebraMap O (FractionRing O) b), ← mul_assoc,
      inv_mul_cancel₀ hπ, one_mul]

theorem range_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.range (divPowQ ϖ n) = LinearMap.ker ((ϖ ^ n) • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O) := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [divPowQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one, Algebra.smul_def, map_pow, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    exact ⟨a, rfl⟩
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
      Algebra.smul_def, map_pow] at hy
    obtain ⟨b, hb⟩ := hy
    refine ⟨b, ?_⟩
    rw [divPowQ_apply, hb, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

theorem natCard_lev_KO {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (O ⧸ Ideal.span {ϖ ^ n}) := by
  have h1 : Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (LinearMap.range (divPowQ ϖ n)) := by
    rw [range_divPowQ hϖ n]; rfl
  rw [h1, ← Nat.card_congr (LinearMap.quotKerEquivRange (divPowQ ϖ n)).toEquiv, ker_divPowQ hϖ n]

theorem natCard_quot_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {ϖ ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hp : (Ideal.span {ϖ}).IsPrime := hϖ.maximalIdeal_eq ▸ inferInstance
  have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
    (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := n)
  rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  rw [hq, ← hϖ.maximalIdeal_eq]
  rfl

theorem lev_pow_card {ϖ : O} (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (e : M ≃ₗ[O] Formalism.NG.KO O) (n : ℕ) [Finite (IsLocalRing.ResidueField O)] :
    Finite (Lev M (ϖ ^ n)) ∧
      Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hc : Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
    rw [Nat.card_congr (levCongr e (ϖ ^ n)), natCard_lev_KO hϖ.ne_zero, natCard_quot_pow hϖ]
  refine ⟨Nat.finite_of_card_ne_zero ?_, hc⟩
  rw [hc]
  exact pow_ne_zero _ Nat.card_pos.ne'

end DVR

theorem levKO_card : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ n : ℕ,
    Finite (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) ∧
      Nat.card (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  fun hϖ _ _ _ e n => lev_pow_card hϖ e n

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitOrbitsStableLatticesSeparable
section
open Polynomial

namespace GlobalTheory.UnitLemma

theorem aeval_mul_mem_of_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {g : A} {M : Submodule O A}
    (hM : ∀ y ∈ M, g * y ∈ M) (p : O[X]) {m : A} (hm : m ∈ M) : aeval g p * m ∈ M := by
  induction p using Polynomial.induction_on with
  | C a => simpa [Algebra.smul_def] using M.smul_mem a hm
  | add p q hp hq => simpa [add_mul] using M.add_mem hp hq
  | monomial n a ih =>
    have := hM _ ih
    have e : aeval g (Polynomial.C a * X ^ (n + 1)) * m = g * (aeval g (Polynomial.C a * X ^ n) * m) := by
      simp only [map_mul, aeval_C, aeval_X, map_pow, pow_succ]; ring
    rw [e]; exact this

theorem finite_orbits_stLat_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hsep
  set C : Submodule O A := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  have hCfg : C.FG := _root_.GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly O E A g hsep
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_common_denominator_aeval_of_fg' O E A g (_root_.GlobalTheory.SepGenElt.exists_aeval_eq E A g hsep) C hCfg
  have hfin := _root_.GlobalTheory.finite_submodules_between_smul_and_self O A C hCfg c hc0

  have key : ∀ M : stLat O E g, ∃ t : Aˣ, mulLat O ((t⁻¹ : Aˣ) : A) (M : Submodule O A) ∈
      {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N} := by
    intro M
    obtain ⟨hML, hMg⟩ := M.2
    set N : Submodule O A := C * (M : Submodule O A) with hN
    have hMN : (M : Submodule O A) ≤ N := by
      intro m hm
      have := Submodule.mul_mem_mul (show (1 : A) ∈ C from (integralClosure O A).one_mem) hm
      simpa using this
    have hNlat : IsLat O E N := by
      refine ⟨Submodule.FG.mul hCfg hML.1, ?_⟩
      rw [eq_top_iff, ← hML.2]
      exact Submodule.span_mono hMN
    have hNC : ∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N := by
      intro x hx y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        rw [← mul_assoc]
        exact Submodule.mul_mem_mul ((integralClosure O A).mul_mem hx ha) hm
      · intro u v hu hv
        rw [mul_add]; exact N.add_mem hu hv
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable O E A g hsep N hNlat hNC
    have hcN : ∀ y ∈ N, c • y ∈ (M : Submodule O A) := by
      intro y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        obtain ⟨p, hp⟩ := hc a ha
        rw [← smul_mul_assoc, ← hp]
        exact aeval_mul_mem_of_stable hMg p hm
      · intro u v hu hv
        rw [smul_add]; exact Submodule.add_mem _ hu hv
    refine ⟨t, ?_, ?_⟩
    · intro x hx
      rw [mem_mulLat_iff, inv_inv] at hx
      have h1 : (t : A) * x ∈ N := hMN hx
      rw [ht, mem_mulLat_iff] at h1
      rw [hCdef, Subalgebra.mem_toSubmodule]
      rw [Subalgebra.mem_toSubmodule] at h1
      simpa [← mul_assoc] using h1
    · intro y hy
      rw [mem_mulLat_iff, inv_inv]
      have h1 : (t : A) * y ∈ N := by
        rw [ht, mem_mulLat_iff, Subalgebra.mem_toSubmodule]
        rw [hCdef, Subalgebra.mem_toSubmodule] at hy
        simpa [← mul_assoc] using hy
      simpa [mul_smul_comm] using hcN _ h1
  choose t ht using key
  let F : MulAction.orbitRel.Quotient Aˣ (stLat O E g) → {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} :=
    fun q => ⟨_, ht q.out⟩
  haveI : Finite {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} := hfin.to_subtype
  refine Finite.of_injective F ?_
  intro q₁ q₂ h
  have h' : mulLat O (((t q₁.out)⁻¹ : Aˣ) : A) (q₁.out : Submodule O A) = mulLat O (((t q₂.out)⁻¹ : Aˣ) : A) (q₂.out : Submodule O A) :=
    congrArg Subtype.val h
  rw [← q₁.out_eq, ← q₂.out_eq]
  apply Quotient.sound
  refine ⟨t q₁.out * (t q₂.out)⁻¹, ?_⟩
  apply Subtype.ext
  rw [stLat_smul_val, Units.val_mul, mulLat_mul, ← h', ← mulLat_mul]
  simp [mulLat_one]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem aeval_ne_zero_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : aeval π p ≠ 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have hπ0 : π ≠ 0 := by
    rw [← norm_pos_iff, hπ]; positivity
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  intro h
  rw [aeval_eq_sum_range' (Nat.lt_succ_self _)] at h
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = 0 := by
    rw [← h]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs, nnnorm_zero] at h6
  have hm : p.natDegree ∈ p.support := natDegree_mem_support_of_nonzero hp
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hm
  rw [← h6] at h7
  obtain ⟨n, hn⟩ := key _ hm
  have h8 : ‖p.coeff p.natDegree • π ^ p.natDegree‖ ≤ 0 := h7
  rw [hn] at h8
  exact absurd h8 (not_le.2 (by positivity))

theorem minpoly_unramifiedSubfield_eq_cyclotomic (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) : minpoly ↥(K0 K) ζ = cyclotomic (l ^ j) ↥(K0 K) := by
  have hlp : l.Prime := Fact.out
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot : aeval ζ (cyclotomic (l ^ j) ↥(K0 K)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
    (minpoly.dvd _ _ hroot)
  rw [natDegree_cyclotomic]
  by_contra hlt
  push_neg at hlt
  refine aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 (minpoly ↥(K0 K) ζ)) ?_ ?_ ?_
  · intro h
    exact minpoly.ne_zero hint (taylor_injective 1 (by rw [h, map_zero]))
  · rwa [natDegree_taylor]
  · rw [taylor_apply, aeval_comp]
    simp

theorem exists_primitiveRoot_Om (j : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ j) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  haveI : CharZero (Om l) := algebraRat.charZero _
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ j)

theorem Ks_eq_restrictScalars (K : FinExt l) (j : ℕ) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    Ks K j = ((↥(K0 K))⟮ζ⟯).restrictScalars ℚ_[l] := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, Ks]
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

theorem finrank_Ks (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ]
  have h1 : Module.finrank ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯) = (l - 1) * l ^ (j - 1) := by
    rw [IntermediateField.adjoin.finrank hint, minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ,
      natDegree_cyclotomic, Nat.totient_prime_pow hlp hj, mul_comm]
  rw [← h1]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯)).symm

theorem exists_chi_approx (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) (j : ℕ) (hj : 1 ≤ j) :
    ∃ g ∈ (K0 K).fixingSubgroup, ‖(χ g : ℚ_[l]) - u‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  let z : ℤ_[l] := ⟨u, hu.le⟩
  set a := z.appr j with ha
  have hza : ‖u - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).2 (PadicInt.appr_spec j z)
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  have hlt : (l : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hl1 (by omega)
  have hna : ‖(a : ℚ_[l])‖ = 1 := by
    have h1 : (a : ℚ_[l]) = u + -(u - a) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, hu, norm_neg,
      max_eq_left (hza.trans hlt.le)]
    rw [hu, norm_neg]
    exact (hza.trans_lt hlt).ne'
  have hcop : a.Coprime (l ^ j) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hlp.coprime_iff_not_dvd]
    intro hd
    have : ‖((a : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (by exact_mod_cast hd)
    rw [Int.cast_natCast, hna] at this
    exact lt_irrefl _ this
  have hζa := hζ.pow_of_coprime a hcop
  have hconj : IsConjRoot ↥(K0 K) (ζ ^ a) ζ := by
    unfold IsConjRoot
    rw [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, minpoly_unramifiedSubfield_eq_cyclotomic K j hj _ hζa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ.restrictScalars ℚ_[l], fun x => σ.commutes x, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hχ (σ.restrictScalars ℚ_[l]) j ζ hζ.pow_eq_one
  have hab : ζ ^ a = ζ ^ b := hσ.symm.trans hb'
  have hmod : a ≡ b [MOD l ^ j] := by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hpos.ne').pow_eq_pow_iff_modEq.1 hab
  have hba : ‖(b : ℚ_[l]) - a‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd ((b : ℤ) - a) j (p := l)).2
      (by exact_mod_cast hmod.dvd)
    simpa using this
  have h1 : (χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - u =
      ((χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - b) + (((b : ℚ_[l]) - a) + -(u - a)) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hba ?_)
  rwa [norm_neg]

theorem exists_chi_eq (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) : ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hcont := (cyc_basic l χ hχ).2.1
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  have hcl : IsClosed ((K0 K).fixingSubgroup : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed _
  have hc := (hcl.isCompact.image hcont).isClosed
  have hmem : u ∈ (fun g => (χ g : ℚ_[l])) '' ((K0 K).fixingSubgroup : Set (GQ l)) := by
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
    obtain ⟨g, hg, hg'⟩ := exists_chi_approx K χ hχ u hu (n + 1) (by omega)
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine hg'.trans_lt (lt_of_le_of_lt ?_ hn)
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hl1.le (by push_cast; omega)
  exact hmem

theorem finrank_Ks_and_chi_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧
    ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 →
      ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u :=
  fun _ _ K => ⟨finrank_Ks K, exists_chi_eq K⟩

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnity
section
open Polynomial IsLocalRing

namespace GlobalTheory.UnitLemma.InvolRes

theorem residue_pow_and_roots : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ),
    Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) →
    (∃ x, residue S (τ x) ≠ residue S x) →
    (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  intro S _ _ _ M hM τ hττ hne
  let e : S ≃+* S := RingEquiv.ofRingHom τ τ (RingHom.ext hττ) (RingHom.ext hττ)
  let s := ResidueField.mapEquiv e
  have hs : ∀ x, s (residue S x) = residue S (τ x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  haveI := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField S) p⟩
  obtain ⟨-, hsq⟩ := GlobalTheory.UnitLemma.UnrExt.invol_eq_pow p hM s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hττ]) (by
    obtain ⟨x, hx⟩ := hne
    exact ⟨residue S x, by rw [hs]; exact hx⟩)
  have h1 : ∀ x, residue S (τ x) = residue S x ^ M := fun x => by rw [← hs, hsq]
  refine ⟨h1, fun w hw => ?_⟩
  have hcard2 : 2 ≤ M ^ 2 := by
    have : 1 < Nat.card (ResidueField S) := Finite.one_lt_card
    omega
  set N := M ^ 2 - 1 with hN
  have hNk : (N : ResidueField S) ≠ 0 := by
    haveI := Fintype.ofFinite (ResidueField S)
    have h0 : ((N + 1 : ℕ) : ResidueField S) = 0 := by
      rw [show N + 1 = M ^ 2 by omega, ← hM, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h0
  refine GlobalTheory.UnitLemma.UnrExt.root_unique (residue S) (ker_residue) (X ^ N - 1 : S[X])
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) (a := τ w) (b := w ^ M) ?_ ?_ ?_
  · simp [← map_pow, hw]
  · simp only [eval_sub, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow, sub_self]
  · rw [h1, map_pow]

end GlobalTheory.UnitLemma.InvolRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaarStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  first | exact @GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | exact GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | (intros; apply GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduceStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryOrbitalIntegral_liftLastBasis_reduce : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0 → orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  first | exact @GlobalTheory.JR.Step.OrbULift.orbU_liftH | exact GlobalTheory.JR.Step.OrbULift.orbU_liftH | (intros; apply GlobalTheory.JR.Step.OrbULift.orbU_liftH <;> assumption)
end

