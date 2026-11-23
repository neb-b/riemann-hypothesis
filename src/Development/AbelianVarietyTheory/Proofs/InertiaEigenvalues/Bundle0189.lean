module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0064
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIde
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommutantMulIntegralConjugate
section
open Matrix Polynomial

namespace GlobalTheory.IntConj

section Krylov

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_krylov_of_semiconj {M M' x : Matrix n n A} (h : x * M' = M * x) (w : n → A) :
    x * GlobalTheory.RegSS.krylov M' w = GlobalTheory.RegSS.krylov M (x *ᵥ w) := by
  ext i j
  have hk : ∀ k : ℕ, x * M' ^ k = M ^ k * x := fun k => SemiconjBy.pow_right h k
  calc (x * GlobalTheory.RegSS.krylov M' w) i j
      = (x *ᵥ ((M' ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ w)) i := by
        simp [GlobalTheory.RegSS.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ (x *ᵥ w)) i := by
        rw [mulVec_mulVec, hk, ← mulVec_mulVec]
    _ = GlobalTheory.RegSS.krylov M (x *ᵥ w) i j := by simp [GlobalTheory.RegSS.krylov]

end Krylov

theorem mem_unitBall {E : Type} [NormedField E] [IsUltrametricDist E] (y : E) :
    y ∈ (NormedField.valuation (K := E)).valuationSubring ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem norm_eq_one_of_isUnit {E : Type} [NormedField E] [IsUltrametricDist E]
    {a : (NormedField.valuation (K := E)).valuationSubring} (ha : IsUnit a) : ‖(a : E)‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h := congrArg (fun y : (NormedField.valuation (K := E)).valuationSubring => ‖(y : E)‖) u.mul_inv
  simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h
  have h1 : ‖((u : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 (u : (NormedField.valuation (K := E)).valuationSubring).2
  have h2 : ‖(((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 ((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring).2
  nlinarith [norm_nonneg ((u : (NormedField.valuation (K := E)).valuationSubring) : E),
    norm_nonneg (((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)]

end GlobalTheory.IntConj

namespace GlobalTheory.IntConj

theorem exists_commuting_mul_integral (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N x : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hsep : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (hx : IsUnit x) (hN' : ∀ i j, ‖(x⁻¹ * N * x) i j‖ ≤ 1) :
    ∃ c : Matrix (Fin n) (Fin n) E, IsUnit c ∧ c * N = N * c ∧ (∀ i j, ‖(c⁻¹ * x) i j‖ ≤ 1) ∧
      ‖(c⁻¹ * x).det‖ = 1 := by
  classical
  let O := (NormedField.valuation (K := E)).valuationSubring
  let φ : O →+* E := O.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have lift : ∀ M : Matrix (Fin n) (Fin n) E, (∀ i j, ‖M i j‖ ≤ 1) →
      ∃ M₀ : Matrix (Fin n) (Fin n) O, M₀.map φ = M := fun M hM =>
    ⟨Matrix.of fun i j => ⟨M i j, (mem_unitBall _).2 (hM i j)⟩, by ext i j; rfl⟩
  have liftP : ∀ p : E[X], (∀ i, ‖p.coeff i‖ ≤ 1) → ∃ p₀ : O[X], p₀.map φ = p := by
    intro p hp
    have : p ∈ Polynomial.lifts φ :=
      (lifts_iff_coeff_lifts p).2 fun k => ⟨⟨_, (mem_unitBall _).2 (hp k)⟩, rfl⟩
    exact (mem_lifts p).1 this
  obtain ⟨u, v, hu, hv, huv⟩ := hsep
  obtain ⟨u₀, rfl⟩ := liftP u hu
  obtain ⟨v₀, rfl⟩ := liftP v hv
  have sep : ∀ M₀ : Matrix (Fin n) (Fin n) O, (M₀.map φ).charpoly = N.charpoly →
      M₀.charpoly.Separable := by
    intro M₀ hM
    refine ⟨u₀, v₀, ?_⟩
    apply Polynomial.map_injective φ hφ
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM, Polynomial.map_one]
    exact huv
  obtain ⟨X, rfl⟩ := hx
  have hXd : IsUnit (X : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 X.isUnit
  have hcp : ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)).charpoly = N.charpoly := by
    exact Matrix.charpoly_units_conj' X N
  obtain ⟨N₀, hN₀⟩ := lift N hN
  obtain ⟨N₀', hN₀'⟩ := lift _ hN'
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀ (sep N₀ (by rw [hN₀]))
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀' (sep N₀' (by rw [hN₀', hcp]))
  have hK : (GlobalTheory.RegSS.krylov N₀ v₁).map φ = GlobalTheory.RegSS.krylov N (φ ∘ v₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀]
  have hK' : (GlobalTheory.RegSS.krylov N₀' w₁).map φ =
      GlobalTheory.RegSS.krylov ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) (φ ∘ w₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀']
  have hKu := GlobalTheory.RegSS.isUnit_det_map φ hv₁
  have hKu' := GlobalTheory.RegSS.isUnit_det_map φ hw₁
  obtain ⟨-, -, hbij⟩ := GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N (φ ∘ v₁) (by rw [← hK]; exact hKu)
  obtain ⟨l, hl⟩ := hbij.2 ((X : Matrix (Fin n) (Fin n) E) *ᵥ (φ ∘ w₁))
  simp only at hl
  have hcN : N * (l : Matrix (Fin n) (Fin n) E) = l * N := GlobalTheory.RegSS.commute_of_mem_genAlg rfl l.2
  have hXN : (X : Matrix (Fin n) (Fin n) E) * ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) = N * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXd, Matrix.one_mul]
  have key : (l : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀ v₁).map φ =
      (X : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀' w₁).map φ := by
    rw [hK, hK', mul_krylov_of_semiconj hcN.symm, mul_krylov_of_semiconj hXN, hl]
  set Kv := (GlobalTheory.RegSS.krylov N₀ v₁).map φ with hKv
  set Kw := (GlobalTheory.RegSS.krylov N₀' w₁).map φ with hKw
  generalize (l : Matrix (Fin n) (Fin n) E) = c at key hcN
  have hcu : IsUnit c := by
    have : c = (X : Matrix (Fin n) (Fin n) E) * Kw * Kv⁻¹ := by
      rw [← key, Matrix.mul_nonsing_inv_cancel_right _ _ hKu]
    rw [this]
    exact (X.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hKu')).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hKu))
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det _).1 hcu
  have e2 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = Kv * Kw⁻¹ := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (c⁻¹ * (X : Matrix (Fin n) (Fin n) E)) hKu',
      Matrix.mul_assoc c⁻¹, ← key, Matrix.nonsing_inv_mul_cancel_left _ _ hcd]
  have hinv : Kw⁻¹ = ((GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hKw, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ hw₁, map_one]
  have e3 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) =
      (GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    rw [e2, hinv, hKv, Matrix.map_mul]
  refine ⟨c, hcu, hcN.symm, fun i j => ?_, ?_⟩
  · rw [e3]; exact (mem_unitBall _).1 ((GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹) i j).2
  · rw [e3, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact norm_eq_one_of_isUnit (by
      rw [Matrix.det_mul]; exact hv₁.mul (Matrix.isUnit_nonsing_inv_det _ hw₁))

end GlobalTheory.IntConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

open IsLocalRing

theorem modEq_of_pow_modEq_pow_sub_one (l n a b : ℕ) (hl : 2 ≤ l) (hn : 0 < n)
    (h : l ^ a ≡ l ^ b [MOD l ^ n - 1]) : a ≡ b [MOD n] := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have hpos : 1 ≤ l ^ n := Nat.one_le_pow _ _ (by omega)
    have hone : l ^ n ≡ 1 [MOD l ^ n - 1] :=
      ((Nat.modEq_iff_dvd' hpos).2 dvd_rfl).symm
    have hred : ∀ c : ℕ, l ^ c ≡ l ^ (c % n) [MOD l ^ n - 1] := by
      intro c
      conv_lhs => rw [← Nat.div_add_mod c n, pow_add, pow_mul]
      have := (hone.pow (c / n)).mul_right (l ^ (c % n))
      simpa using this
    have hlt : ∀ c : ℕ, l ^ (c % n) < l ^ n - 1 := by
      intro c
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h2 : l ^ (c % (k + 1)) ≤ l ^ k :=
        Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.1 (Nat.mod_lt _ hn))
      have h3 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : l ^ k * 2 ≤ l ^ k * l := Nat.mul_le_mul_left _ hl
      rw [pow_one] at h3
      rw [pow_succ]
      omega
    have h5 : l ^ (a % n) ≡ l ^ (b % n) [MOD l ^ n - 1] :=
      ((hred a).symm.trans h).trans (hred b)
    have h6 := Nat.ModEq.eq_of_lt_of_lt h5 (hlt a) (hlt b)
    exact Nat.pow_right_injective hl h6
  · obtain rfl : n = 1 := by omega
    exact Nat.modEq_one

theorem exists_frobenius_and_exponent_modEq (l : ℕ) [Fact l.Prime] :
    (∃ φ : GQ l, ∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → φ x = x ^ l) ∧
    ∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) →
      a ≡ b [MOD n] := by
  have hp : l.Prime := Fact.out
  have hgt : ∀ n : ℕ, 0 < n → 1 < l ^ n := fun n hn => Nat.one_lt_pow hn.ne' hp.one_lt
  constructor
  · have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
    have : NeZero l := ⟨hp.ne_zero⟩
    have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
      rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
    obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
      (Finite.of_equiv _ e.symm.toEquiv) (Om l)
    rw [hcard] at hφ
    refine ⟨φ, fun n hn x hx => ?_⟩
    by_cases h0 : x = 0
    · rw [h0, map_zero, zero_pow hp.ne_zero]
    have h1 := hgt n hn
    refine hφ x (l ^ n - 1) (fun h => ?_) ?_
    · rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
      have h2 : l ∣ l ^ n := dvd_pow_self l hn.ne'
      have h3 : l ∣ l ^ n - (l ^ n - 1) := Nat.dvd_sub h2 h
      have h4 : l ^ n - (l ^ n - 1) = 1 := by omega
      rw [h4] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
    · apply mul_right_cancel₀ h0
      rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]
  · intro n a b hn h
    have h1 := hgt n hn
    have : NeZero (l ^ n - 1) := ⟨by omega⟩
    have : NeZero ((l ^ n - 1 : ℕ) : Om l) := inferInstance
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
    have h2 : ζ ^ l ^ n = ζ := by
      conv_lhs => rw [← Nat.sub_add_cancel h1.le, pow_succ, hζ.pow_eq_one, one_mul]
    have h3 := h ζ h2
    apply modEq_of_pow_modEq_pow_sub_one l n a b hp.two_le hn
    have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by omega)
    rw [hζ.eq_orderOf]
    exact hfin.pow_eq_pow_iff_modEq.1 h3

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeri
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.PowKill

theorem exists_pow_smul_eq_zero {R : Type} [CommRing R] {x : R}
    (hx : ∀ I : Ideal R, I.IsMaximal → x ∈ I) {M : Type} [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ m : ℕ, ∀ q : M, (x ^ m) • q = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun q => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    refine ⟨m + 1, fun q => ?_⟩
    have h1 : x • q ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk q))
      rw [map_smul, ← hr, map_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      exact I.mul_mem_right r (hx I hI)
    have h2 := hm ⟨x • q, h1⟩
    rw [pow_succ, mul_smul]
    exact congrArg Subtype.val h2

section

variable {O : Type} [CommRing O] (l : ℕ) [Fact l.Prime]

theorem isUnit_l_mul_add_one (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (c : O) : IsUnit ((l : O) * c + 1) := by
  set u := algebraMap O K ((l : O) * c + 1) with hu
  have hlc : ‖(l : K) * algebraMap O K c‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c))
      (norm_l_lt_one (K := K) l)
  have hu1 : ‖u‖ = 1 := by
    have : u = (l : K) * algebraMap O K c + 1 := by simp [hu]
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlc.ne)]
    rw [norm_one]; exact max_eq_right hlc.le
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  obtain ⟨b, hb⟩ := (IsUnitBall.mem_range_iff (O := O) (u⁻¹)).2 (by rw [norm_inv, hu1, inv_one])
  refine isUnit_iff_exists_inv.2 ⟨b, IsUnitBall.inj (O := O) (K := K) ?_⟩
  rw [map_mul, hb, ← hu, mul_inv_cancel₀ hu0, map_one]

theorem l_mem_maximal {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (I : Ideal (A O K)) (hI : I.IsMaximal) : (l : A O K) ∈ I := by
  have hj : (l : A O K) ∈ Ideal.jacobson (⊥ : Ideal (A O K)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    have key : IsUnit ((equivA O K).symm ((l : A O K) * y + 1)) := by
      rw [map_add (f := _), map_mul, map_natCast, map_one, PowerSeries.isUnit_iff_constantCoeff, map_add (f := _),
        map_mul, map_natCast, map_one]
      exact isUnit_l_mul_add_one l K _
    simpa using key.map (equivA O K).toRingEquiv.toRingHom
  have hle : Ideal.jacobson (⊥ : Ideal (A O K)) ≤ I := by
    rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hI⟩
  exact hle hj

end

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo]
    [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 :=
  fun O K _ _ _ _ _ l _ _ _ _ _ h => exists_pow_smul_eq_zero (l_mem_maximal (K := K) l) h

end GlobalTheory.PowKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotientStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (T : Submodule O V), IsTopologicalRing O → CompactSpace O → IsAdic (IsLocalRing.maximalIdeal O) → IsLatticeIn T → ∀ ϖ : O, Irreducible ϖ → ∀ n : ℕ, Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  first | exact @GlobalTheory.LatTorsFinite.finite_ker_pow_smul | exact GlobalTheory.LatTorsFinite.finite_ker_pow_smul | (intros; apply GlobalTheory.LatTorsFinite.finite_ker_pow_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

theorem finite_semisimple (k R : Type) [Field k] [CharZero k] [IsAlgClosed k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : IsPsChar d (fun x => T x))
    (hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0) :
    Module.Finite k R ∧ IsSemisimpleRing R := by
  refine _root_.GlobalTheory.AlgRing.finite_and_isSemisimpleRing k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)
  · obtain ⟨p, hp, -, hT⟩ := cayleyHamilton k R d T h x
    exact ⟨p, hp, hnd _ hT⟩
  · refine hnd x fun y => ?_
    rw [show T (x * y) = T (y * x) from h.comm x y]
    exact GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)
  · have hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a := fun i => by
      obtain ⟨⟨a, -, ha⟩, h0⟩ := _root_.GlobalTheory.PsChar.isPsChar_idempotent k R d T h (e i) (he.idem i)
      refine ⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩
      rw [ha, h', Nat.cast_zero]
    choose a ha1 ha using hv
    obtain ⟨⟨s, hs, hsT⟩, -⟩ := _root_.GlobalTheory.PsChar.isPsChar_idempotent k R d T h (∑ i, e i) he.isIdempotentElem_sum
    have h1 : ((∑ i, a i : ℕ) : k) = s := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsT, map_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => (ha i).symm
    have h2 : ∑ i, a i = s := by exact_mod_cast h1
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = s := h2
      _ ≤ d := hs

def traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {x | ∀ y, T (x * y) = 0} (by simp)
    (fun {x y} hx hy z => by simp only [Set.mem_setOf_eq] at hx hy; simp [add_mul, hx z, hy z])
    (fun {x} hx z => by simp only [Set.mem_setOf_eq] at hx; simp [neg_mul, hx z])
    (fun {x y} hy z => by
      simp only [Set.mem_setOf_eq] at hy
      rw [mul_assoc, hc, mul_assoc, hy])
    (fun {x y} hx z => by simp only [Set.mem_setOf_eq] at hx; rw [mul_assoc, hx])

theorem mem_traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) (x : A) : x ∈ traceKer T hc ↔ ∀ y, T (x * y) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

theorem exists_descend {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (hf : Function.Surjective f) (T : A →ₗ[k] k)
    (h : ∀ a, f a = 0 → T a = 0) : ∃ S : B →ₗ[k] k, ∀ a, S (f a) = T a := by
  refine ⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun a => ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  exact Submodule.liftQ_apply _ _ _

theorem exists_ssRep (Γ k : Type) [Group Γ] [Field k] [CharZero k] [IsAlgClosed k] (d : ℕ)
    (T : Γ → k) (hT : IsPsChar d T) :
    ∃ r : Γ →* GL (Fin d) k, IsSSRep r ∧
      ∀ g, ((r g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).trace = T g := by
  obtain ⟨T', hT'g, hT'⟩ := exists_linear_extension Γ k d T hT
  have hc : ∀ x y, T' (x * y) = T' (y * x) := hT'.comm
  let I := traceKer T' hc
  let f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient := RingCon.mkₐ k I.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ I := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨S, hS⟩ := exists_descend f.toLinearMap hf T' fun a ha => by
    simpa using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1
  have hS1 : ∀ a, S (f a) = T' a := hS
  have hS' : IsPsChar d (fun x => S x) := by
    refine ⟨?_, ?_, ?_⟩
    · show S 1 = d
      rw [← map_one f, hS1]; exact hT'.one
    · intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      show S (f a * f b) = S (f b * f a)
      rw [← map_mul, ← map_mul, hS1, hS1]; exact hc a b
    · intro x
      choose a ha using fun i => hf (x i)
      have hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i) := funext fun i => (ha i).symm
      rw [hx, alt_comp_monoidHom]
      have he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g :=
        funext fun g => hS1 g
      rw [he]; exact hT'.alt_eq_zero a
  have hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hf x
    refine (hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)
    rw [← hS1, map_mul]; exact hx (f b)
  obtain ⟨hfin, hss⟩ := finite_semisimple k _ d S hS' hnd
  obtain ⟨N, n, hn, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient
  let τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k := S ∘ₗ e.symm.toLinearMap
  have hτ : ∀ x, τ x = S (e.symm x) := fun x => rfl
  obtain ⟨c, hcτ⟩ := _root_.GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace k N n τ fun x y => by
    rw [hτ, hτ, map_mul e.symm, map_mul e.symm]; exact hS'.comm _ _
  have hcn : ∀ i, ∃ m : ℕ, c i = m := by
    intro i
    haveI := hn i
    let E : Π j, Matrix (Fin (n j)) (Fin (n j)) k := Pi.single i (Matrix.single 0 0 1)
    have hE : IsIdempotentElem E := by
      unfold IsIdempotentElem
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [E, Matrix.single_mul_single_same]
      · simp [E, hj]
    have hτE : τ E = c i := by
      rw [hcτ, Finset.sum_eq_single i]
      · simp [E, Matrix.trace_single_eq_same]
      · intro j _ hj; simp [E, hj]
      · simp
    obtain ⟨⟨m, -, hm⟩, -⟩ := _root_.GlobalTheory.PsChar.isPsChar_idempotent k _ d S hS' (e.symm E) (hE.map e.symm)
    exact ⟨m, hτE.symm.trans hm⟩
  choose m hm using hcn
  have hsum : ∑ i, m i * n i = d := by
    have h1 : τ 1 = d := by rw [hτ, map_one]; exact hS'.one
    rw [hcτ] at h1
    simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1
    exact_mod_cast h1
  obtain ⟨ρ₀, hρ₀⟩ := _root_.GlobalTheory.exists_algHom_trace_eq_sum_mult_trace k N n m d hsum
  let g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k := ρ₀.comp e.toAlgHom
  let ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k := g.comp f
  have htr : ∀ a, (ρ a).trace = T' a := fun a => by
    show (ρ₀ (e (f a))).trace = _
    rw [hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]
    simp [hm]
  have hrange : IsSemisimpleRing ρ.range := by
    have : ρ.range = g.range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [this]
    exact RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  refine ⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, _root_.GlobalTheory.isSSRep_of_isSemisimpleRing_range Γ k d ρ hrange,
    fun x => ?_⟩
  show (ρ (MonoidAlgebra.of k Γ x)).trace = T x
  rw [htr, hT'g]

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerFurther
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem φc_tc (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l) : φc l (tc l y) = tc l (y ^ l) := by
  unfold φc tc
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem frob_teich : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l), φc l (tc l y) = tc l (y ^ l) :=
  fun l _ y => φc_tc l y

end GlobalTheory.PMon.Gauss
end

