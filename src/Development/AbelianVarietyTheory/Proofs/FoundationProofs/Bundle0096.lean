module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hn : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ i : ℕ, i.Coprime M ∧ s ζ = ζ ^ i ∧
      (i : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hcard : Nat.card (rootsOfUnity M Ω) = M := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω M
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  set c := modularCyclotomicCharacter Ω hcard s.toRingEquiv with hc
  have hsζ : s ζ = ζ ^ (c : ZMod M).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard s.toRingEquiv hζ.toRootsOfUnity.2
    simpa using h
  refine ⟨ζ, hζ, (c : ZMod M).val, ZMod.val_coe_unit_coprime c, hsζ, ?_⟩
  rw [cyclotomicCharacter.toZModPow]
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hcard' : Nat.card (rootsOfUnity (l ^ n) Ω) = l ^ n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)
  set c' := modularCyclotomicCharacter Ω hcard' s.toRingEquiv
  have hζ' : IsPrimitiveRoot (ζ ^ (M / l ^ n)) (l ^ n) :=
    hζ.pow hM (Nat.div_mul_cancel hn).symm
  have h1 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c : ZMod M).val := by
    rw [map_pow, hsζ, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c' : ZMod (l ^ n)).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard' s.toRingEquiv hζ'.toRootsOfUnity.2
    simpa using h
  have hfin : IsOfFinOrder (ζ ^ (M / l ^ n)) :=
    orderOf_pos_iff.1 (by rw [← hζ'.eq_orderOf]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h3 := hfin.pow_eq_pow_iff_modEq.1 (h1.symm.trans h2)
  rw [← hζ'.eq_orderOf] at h3
  rw [← ZMod.natCast_zmod_val (c' : ZMod (l ^ n))]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.exists_sl2_conj_diag_zmod (M i : ℕ) (hi : i.Coprime M) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), (_root_.GlobalTheory.KZ.en γ 0 0 : ZMod M) = _root_.GlobalTheory.KZ.en δ 0 0 ∧
      (_root_.GlobalTheory.KZ.en γ 0 1 : ZMod M) = (i : ZMod M) * _root_.GlobalTheory.KZ.en δ 0 1 ∧
      (i : ZMod M) * _root_.GlobalTheory.KZ.en γ 1 0 = _root_.GlobalTheory.KZ.en δ 1 0 ∧
      (_root_.GlobalTheory.KZ.en γ 1 1 : ZMod M) = _root_.GlobalTheory.KZ.en δ 1 1 := by
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime i hi
  have hu : (u : ZMod M) = i := rfl
  have hγdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hγdet
  set m : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod M),
      ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M);
      (i : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M),
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M)] with hm_def
  have hm : m.det = 1 := by
    rw [hm_def, Matrix.det_fin_two_of]
    have h1 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (i : ZMod M) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (Int.cast : ℤ → ZMod M) hγdet
    push_cast at h2
    linear_combination h2 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M) * h1
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M ⟨m, hm⟩
  have he : ∀ a b, (((δ : Matrix (Fin 2) (Fin 2) ℤ) a b : ℤ) : ZMod M) = m a b := fun a b => by
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) a b) hδ
    simpa using h
  refine ⟨δ, ?_, ?_, ?_, ?_⟩ <;> simp only [_root_.GlobalTheory.KZ.en, he, hm_def]
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
  · simp
  · simp

theorem exists_conj_level_exponent :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M →
      l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧
      ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧
        (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧
        (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  intro Ω _ _ _ N l n M _ hM hN hl hn s γ hγ
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hn s
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_sl2_conj_diag_zmod M i hi γ
  have red : ∀ {K : ℕ}, K ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod K) = y := fun {K} hK x y h => by
    simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h
  have h10' : (((i : ℤ) * en γ 1 0 : ℤ) : ZMod M) = en δ 1 0 := by push_cast; exact h10
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ1
  have a4 := CongruenceSubgroup.Gamma0_mem.1 hγ0
  refine ⟨δ, Subgroup.mem_inf.2 ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨?_, ?_, ?_⟩,
    CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ζ, hζ, i, by rw [zpow_natCast, hs], ⟨h00, ?_, ?_, h11⟩, ?_⟩
  · exact (red hN h00).symm.trans a1
  · exact (red hN h11).symm.trans a2
  · refine (red hN h10').symm.trans ?_
    have : (en γ 1 0 : ZMod N) = 0 := a3
    rw [Int.cast_mul, this, mul_zero]
  · refine (red hl h10').symm.trans ?_
    have : (en γ 1 0 : ZMod l) = 0 := a4
    rw [Int.cast_mul, this, mul_zero]
  · simpa only [Int.cast_natCast] using h01
  · simpa only [Int.cast_natCast] using h10
  · simpa only [Int.cast_natCast] using hχ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixGamSub
section
noncomputable section

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m n i : ℕ} (hm : 1 ≤ m)
    (hi : ¬ p ^ (n - m) ∣ i) :
    m < n ∧ ∃ K d u : ℕ, ¬ p ∣ d ∧ ¬ p ∣ u ∧ i * (1 + p ^ m) ^ K = i + u * d * p ^ (n - 1) ∧
      ∃ w, (1 + p ^ m) ^ K = 1 + p * w := by
  have hp : p.Prime := Fact.out
  have hi0 : i ≠ 0 := by rintro rfl; exact hi (dvd_zero _)
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.ne_one
  have hv : v < n - m := by
    by_contra h
    push_neg at h
    exact hi (Dvd.dvd.mul_right (pow_dvd_pow p h) _)
  refine ⟨by omega, ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpm : 0 < p ^ m := pow_pos hp.pos m
  have hlt : 1 < 1 + p ^ m := by omega
  have hnd : ¬ p ∣ 1 + p ^ m := fun h =>
    hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)
  have hval := padicValNat.pow_sub_pow (p := p) hodd (x := 1 + p ^ m) (y := 1) hlt
    (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self p (by omega)) hnd
    (n := p ^ (n - v - 1 - m)) (pow_ne_zero _ hp.ne_zero)
  rw [one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow, padicValNat.prime_pow] at hval
  have hK1 : 1 < (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) :=
    Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hlt
  obtain ⟨e, d, hd, hed⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.sub_ne_zero_of_lt hK1) p
    hp.ne_one
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  rw [hed, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hd0,
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hd, add_zero] at hval
  have hK : (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) = 1 + p ^ e * d := by omega
  refine ⟨p ^ (n - v - 1 - m), d, u, hd, hu, ?_, p ^ (e - 1) * d, ?_⟩
  · rw [hK, mul_add, mul_one, show n - 1 = v + e by omega, pow_add]
    ring
  · rw [hK, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog

end GlobalTheory.K5.MonX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMaps
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fraction_field_extension : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  intro Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA
  letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  have hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x) := fun _ => rfl
  let e0 : FractionRing R →+* L := IsFractionRing.lift he
  have he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a := fun a => IsFractionRing.lift_algebraMap he a
  have hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x := fun x => by
    rw [hΩ, he0, hce]
  let e' : FractionRing R →ₐ[Ω] L :=
    { e0 with commutes' := hcom }
  let s0 : G → FractionRing R ≃+* FractionRing R := fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)
  have hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a) :=
    fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a
  let sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R := fun g =>
    AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])
  let ga' : S → FractionRing R ≃+* FractionRing R := fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (A y) := fun y =>
    hA y (nonZeroDivisors.ne_zero y.2)
  let A' : FractionRing R →+* M := IsLocalization.lift (M := nonZeroDivisors R) hunit
  refine ⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A',
    IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
    refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    rw [← hxy, div_mul_cancel₀ _ hy']
  · intro g a
    exact hs0 g a
  · intro s a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a
  · intro a
    exact IsLocalization.lift_eq hunit a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegralStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∃ v : Valuation Ω ℝ≥0,
        (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧
        (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := _root_.GlobalTheory.K5.completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact _root_.GlobalTheory.K5.o0_isAdicComplete_span_p p
  have := h.alg
  have hvaluation :=
    _root_.GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  obtain ⟨v, hv⟩ := hvaluation
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, (Valuation.pos_iff v).2 hp0, ?_⟩
  have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
    have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    simpa [GlobalTheory.K5.IsInt] using this)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
  have hint : GlobalTheory.K5.IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
  exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
    ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHom
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNTwist

noncomputable def twistMap {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : HahnSeries ℚ Ω' where
  coeff r := χ r * s (h.coeff r)
  isPWO_support' := h.isPWO_support.mono (by
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro h0
    exact hr (by rw [h0, map_zero, mul_zero]))

lemma twistMap_coeff {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) (r : ℚ) : (twistMap s χ h).coeff r = χ r * s (h.coeff r) := rfl

lemma twistMap_support {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : (twistMap s χ h).support ⊆ h.support := by
  intro r hr
  simp only [HahnSeries.mem_support, twistMap_coeff, ne_eq] at hr ⊢
  intro h0
  exact hr (by rw [h0, map_zero, mul_zero])

noncomputable def twistHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h0 : χ 0 = 1) (hadd : ∀ r r', χ (r + r') = χ r * χ r') :
    HahnSeries ℚ Ω →+* HahnSeries ℚ Ω' where
  toFun := twistMap s χ
  map_one' := by
    ext r
    rw [twistMap_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs with hr
    · subst hr; simp [h0]
    · simp
  map_zero' := by
    ext r
    simp [twistMap_coeff]
  map_add' x y := by
    ext r
    simp [twistMap_coeff, mul_add]
  map_mul' x y := by
    ext a
    show (twistMap s χ (x * y)).coeff a = (twistMap s χ x * twistMap s χ y).coeff a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [twistMap_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    have hsub : Finset.antidiagonal (twistMap s χ x).isPWO_support (twistMap s χ y).isPWO_support a ⊆
        Finset.antidiagonal x.isPWO_support y.isPWO_support a :=
      fun ij hij => (Finset.antidiagonal_mono_right (twistMap_support s χ y))
        ((Finset.antidiagonal_mono_left (twistMap_support s χ x)) hij)
    rw [Finset.sum_subset hsub (fun ij hbig hij => ?_)]
    · refine Finset.sum_congr rfl (fun ij hij => ?_)
      have hsum : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hij).2.2
      rw [twistMap_coeff, twistMap_coeff, map_mul, ← hsum, hadd]
      ring
    · have hs : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hbig).2.2
      by_cases h1 : (twistMap s χ x).coeff ij.1 = 0
      · rw [h1, zero_mul]
      · by_cases h2 : (twistMap s χ y).coeff ij.2 = 0
        · rw [h2, mul_zero]
        · exact absurd (Finset.mem_antidiagonal.mpr ⟨h1, h2, hs⟩) hij

end GlobalTheory.FNTwist

theorem GlobalTheory.FNTwist.exists_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  intro Ω Ω' _ _ s l χ hl h0 hadd
  have hinj : Function.Injective (AddMonoidHom.mulRight l) := by
    intro a b hab
    simpa [AddMonoidHom.coe_mulRight, hl.ne'] using hab
  have hmono : ∀ g g' : ℚ, AddMonoidHom.mulRight l g ≤ AddMonoidHom.mulRight l g' ↔ g ≤ g' := by
    intro g g'
    simp only [AddMonoidHom.coe_mulRight]
    exact mul_le_mul_iff_of_pos_right hl
  refine ⟨(HahnSeries.embDomainRingHom (AddMonoidHom.mulRight l) hinj hmono).comp
    (GlobalTheory.FNTwist.twistHom s χ h0 hadd), fun h r => ?_⟩
  rw [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
  have := HahnSeries.embDomain_coeff (f := ⟨⟨AddMonoidHom.mulRight l, hinj⟩, hmono _ _⟩)
    (x := GlobalTheory.FNTwist.twistHom s χ h0 hadd h) (a := r)
  rw [show χ r * s (h.coeff r) = (GlobalTheory.FNTwist.twistHom s χ h0 hadd h).coeff r from rfl]
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCuspExpansionJInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FNExpJ

variable {Ω : Type} [Field Ω]

theorem ofPowerSeries_coeff_of_ne (P : PowerSeries Ω) {r : ℚ} (hr : ∀ n : ℕ, (n : ℚ) ≠ r) :
    (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, -, hn⟩
  exact hr n (by simpa using hn)

theorem expansion_j : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω,
    IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧
      ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  obtain ⟨c, hc⟩ := GlobalTheory.exists_hasSum_modularJ_sub_inv
  set P : PowerSeries Ω := PowerSeries.mk fun n => (c n : Ω) with hPdef
  have hP : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℚ Ω P).coeff (n : ℚ) = (c n : Ω) := fun n => by
    rw [HahnSeries.ofPowerSeries_apply_coeff, hPdef, PowerSeries.coeff_mk]
  have h0 : ∀ r : ℚ, (∀ n : ℕ, (n : ℚ) ≠ r) → (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 :=
    fun r hr => ofPowerSeries_coeff_of_ne P hr
  have hneg : ∀ r : ℚ, r < 0 → ∀ n : ℕ, (n : ℚ) ≠ r := fun r hr n hn => by
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  refine ⟨HahnSeries.single (-1 : ℚ) (1 : Ω) + HahnSeries.ofPowerSeries ℚ Ω P,
    ⟨?_, 0, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, fun r hr => ?_⟩
    by_cases h1 : r = -1
    · exact ⟨-1, by simp [h1]⟩
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      exact ⟨n, by simp⟩
    · push_neg at h2
      exfalso
      apply hr
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2, add_zero]
  · intro z hz
    set τ : ℍ := ⟨z, hz⟩ with hτ
    have hup : up jT z = GlobalTheory.modularJ τ := by
      simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rfl
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z) := by
      simp [Function.Periodic.qParam, hτ]
    have H1 : HasSum (fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ := by
      have := hasSum_single (f := fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (-1) (fun r hr => by
          simp [HahnSeries.coeff_single_of_ne hr])
      convert this using 1
      rw [hq, HahnSeries.coeff_single_same, map_one, one_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    have H2 : HasSum (fun r : ℚ => ε ((HahnSeries.ofPowerSeries ℚ Ω P).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z))
        (GlobalTheory.modularJ τ - (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) := by
      refine (Function.Injective.hasSum_iff (g := fun n : ℕ => (n : ℚ)) Nat.cast_injective
        (fun r hr => ?_)).mp ?_
      · rw [h0 r (fun n hn => hr ⟨n, hn⟩), map_zero, zero_mul]
      · convert hc τ using 1
        funext n
        simp only [Function.comp_apply, hP, map_intCast, hq, ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
    convert H1.add H2 using 1
    · funext r
      rw [HahnSeries.coeff_add, map_add (f := _), add_mul]
    · rw [hup]
      ring
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num)), add_zero]
  · intro r hr
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne hr.ne, h0 r (hneg r (by linarith)),
      add_zero]
  · intro r
    by_cases h1 : r = -1
    · subst h1
      refine ⟨1, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num))]
      simp
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨c n, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, hP, zero_add]
    · push_neg at h2
      exact ⟨0, by rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2]; simp⟩

end GlobalTheory.FNExpJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunitsStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) → (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1) → ∀ (Ψ : Polynomial (Polynomial V)) (ω : L), Ψ.Monic → (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0) → ∀ R : Polynomial (Polynomial F), R.natDegree < Ψ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
  first | exact @GlobalTheory.gaussExtension_coeff_mem_nonunits | exact GlobalTheory.gaussExtension_coeff_mem_nonunits | (intros; apply GlobalTheory.gaussExtension_coeff_mem_nonunits <;> assumption)
end

