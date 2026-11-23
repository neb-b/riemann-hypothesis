module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnit
section
open GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

open Polynomial

theorem exists_valuation_pow_eq (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f)
    (hnt : f.IsNontrivial) (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      (∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1) ∧
      ∀ x : Ω, (v x : ℝ) ^ (minpoly K x).natDegree = f ((minpoly K x).coeff 0) := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤
          max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  have hco : ∀ (x : Ω) (i : ℕ), ‖(minpoly (WithAbs f) x).coeff i‖ = f ((minpoly K x).coeff i) := by
    intro x i
    rw [hmin x, Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl
  refine ⟨v, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx)]
    exact forall_congr' fun i => by rw [hco]
  · have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hd : (minpoly (WithAbs f) x).natDegree = (minpoly K x).natDegree := by
      rw [hmin x, (minpoly.monic hx).natDegree_map]
    rw [hv, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (WithAbs f) Ω x, hco, hd, one_div]
    exact Real.rpow_inv_natCast_pow (f.nonneg _) (minpoly.natDegree_pos hx).ne'

theorem exists_pow_div_zpow_isIntegral (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsAlgebraic K Ω] (π : R) (hπ : Irreducible π) (x : Ω) (hx : x ≠ 0) :
    ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsIntegral R (x ^ b / (algebraMap R Ω π) ^ a) ∧
      IsIntegral R ((algebraMap R Ω π) ^ a / x ^ b) := by
  obtain ⟨f, hna, hnt, hball, hc⟩ :=
    GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing R K
  obtain ⟨v, hext, hle, hpow⟩ := exists_valuation_pow_eq K Ω f hna hnt hc
  have hint : ∀ z : Ω, v z ≤ 1 → IsIntegral R z := by
    intro z hz
    have hzK : IsIntegral K z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
    have hl : minpoly K z ∈ Polynomial.lifts (algebraMap R K) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun i => (hball _).1 ((hle z).1 hz i)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hzK)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]
  have hR : ∀ r : R, v (algebraMap R Ω r) ≤ 1 := by
    intro r
    rw [IsScalarTower.algebraMap_apply R K Ω, ← NNReal.coe_le_coe, hext]
    exact (hball _).2 ⟨r, rfl⟩
  have hU : ∀ u : Rˣ, v (algebraMap R Ω u) = 1 := by
    intro u
    have h1 : v (algebraMap R Ω u) * v (algebraMap R Ω (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm (hR _) ?_
    calc 1 = _ := h1.symm
      _ ≤ v (algebraMap R Ω u) * 1 := by gcongr; exact hR _
      _ = _ := mul_one _
  have hxK : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hπ0 : v (algebraMap R Ω π) ≠ 0 :=
    (map_ne_zero v).2 ((map_ne_zero_iff _ hinj).2 hπ.ne_zero)
  have hc0 : (minpoly K x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hxK hx
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) ((minpoly K x).coeff 0)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hrs]; simp)
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
  obtain ⟨j, w, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hπ
  have key : v (x ^ (minpoly K x).natDegree) = v (algebraMap R Ω π ^ ((i : ℤ) - j)) := by
    have h1 : v x ^ (minpoly K x).natDegree = v (algebraMap K Ω ((minpoly K x).coeff 0)) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_pow, hpow, hext]
    rw [map_pow, h1, ← hrs, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_zpow₀, zpow_sub₀ hπ0]
    simp [hU]
  have hx0 : v (x ^ (minpoly K x).natDegree) ≠ 0 := (map_ne_zero v).2 (pow_ne_zero _ hx)
  refine ⟨(i : ℤ) - j, (minpoly K x).natDegree, minpoly.natDegree_pos hxK, hint _ ?_, hint _ ?_⟩
  · rw [map_div₀, ← key, div_self hx0]
  · rw [map_div₀, ← key, div_self hx0]

theorem exists_pow_div_p_zpow_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
    IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]; exact o0_isAdicComplete_span_p p
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx
  rwa [map_natCast] at this

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.Cells

section Comb
variable {F : Type} [Field F]

def Good (k : ℕ) (d : ℕ → F) : Prop := d 0 ≠ 0 ∧ ∀ a, k ≤ a → d a = 1

def st (d : ℕ → F) (b : ℕ) : ℕ := Nat.findGreatest (fun a => d a ≠ 0) b

def en (d : ℕ → F) (b : ℕ) : ℕ := sInf {a | b < a ∧ d a ≠ 0}

def sg (k : ℕ) (d : ℕ → F) (b : ℕ) : ℕ := if b < k then k - en d b + (b - st d b) else b

lemma st_le (d : ℕ → F) (b : ℕ) : st d b ≤ b := Nat.findGreatest_le b

lemma st_ne {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : d (st d b) ≠ 0 :=
  Nat.findGreatest_spec (P := fun a => d a ≠ 0) (Nat.zero_le b) h.1

lemma le_st {d : ℕ → F} {a b : ℕ} (hab : a ≤ b) (ha : d a ≠ 0) : a ≤ st d b :=
  Nat.le_findGreatest (P := fun a => d a ≠ 0) hab ha

lemma en_spec {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : b < en d b ∧ d (en d b) ≠ 0 := by
  have : ({a | b < a ∧ d a ≠ 0} : Set ℕ).Nonempty :=
    ⟨b + k + 1, by omega, by rw [h.2 _ (by omega)]; exact one_ne_zero⟩
  exact Nat.sInf_mem this

lemma en_le {d : ℕ → F} {a b : ℕ} (hab : b < a) (ha : d a ≠ 0) : en d b ≤ a :=
  Nat.sInf_le (show a ∈ {a | b < a ∧ d a ≠ 0} from ⟨hab, ha⟩)

lemma en_le_k {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : en d b ≤ k :=
  en_le hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)

lemma dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) :
    (st d c = st d b ∧ en d c = en d b) ∨ en d c ≤ st d b := by
  by_cases h1 : en d c ≤ b
  · exact Or.inr (le_st h1 (en_spec h c).2)
  · left
    have h2 := en_le (d := d) (b := c) (a := en d b) (by have := (en_spec h b).1; omega) (en_spec h b).2
    have h3 := en_le (d := d) (b := b) (a := en d c) (by omega) (en_spec h c).2
    have h4 := le_st (d := d) (a := st d c) (b := b) (by have := st_le d c; omega) (st_ne h c)
    refine ⟨?_, by omega⟩
    by_cases h5 : st d b ≤ c
    · have := le_st h5 (st_ne h b); omega
    · have := en_le (d := d) (b := c) (a := st d b) (by omega) (st_ne h b)
      have := st_le d b; omega

lemma sg_lt {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : sg k d b < k := by
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  simp only [sg, if_pos hb]; omega

lemma sg_ge {k : ℕ} (d : ℕ → F) {b : ℕ} (hb : k ≤ b) : sg k d b = b := by
  simp only [sg, if_neg (not_lt.2 hb)]

lemma sg_dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) (hb : b < k) :
    (st d c = st d b ∧ sg k d c + b = sg k d b + c) ∨ (c < st d b ∧ sg k d b < sg k d c) := by
  have hc : c < k := by omega
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  have := en_spec h c; have := en_le_k h hc; have := st_le d c
  simp only [sg, if_pos hb, if_pos hc]
  rcases dich h hcb with h1 | h1 <;> omega

lemma sg_inj {k : ℕ} {d : ℕ → F} (h : Good k d) : Function.Injective (sg k d) := by
  intro c b hcb
  wlog hlt : c < b generalizing c b
  · rcases Nat.lt_or_ge b c with h1 | h1
    · exact (this hcb.symm h1).symm
    · omega
  by_cases hb : b < k
  · have := sg_dich h hlt hb; omega
  · rw [sg_ge d (not_lt.1 hb)] at hcb
    by_cases hc : c < k
    · have := sg_lt h hc; omega
    · rwa [sg_ge d (not_lt.1 hc)] at hcb

lemma st_ge {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : k ≤ b) : d (st d b) = 1 := by
  have := le_st (d := d) hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)
  exact h.2 _ this

lemma st_eq_iff {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : st d b = b ↔ d b ≠ 0 := by
  constructor
  · intro h1; have := st_ne h b; rwa [h1] at this
  · intro h1; exact le_antisymm (st_le d b) (le_st le_rfl h1)

lemma ext_of {k : ℕ} {d d' : ℕ → F} (h : Good k d) (h' : Good k d')
    (H : ∀ b < k, sg k d b = sg k d' b ∧ d (st d b) = d' (st d' b)) : d = d' := by
  funext b
  by_cases hb : b < k
  swap
  · rw [h.2 b (not_lt.1 hb), h'.2 b (not_lt.1 hb)]
  have key : st d b = b ↔ st d' b = b := by
    have := st_le d b; have := st_le d' b
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · omega
    · have := sg_dich h (c := b - 1) (b := b) (by omega) hb
      have := sg_dich h' (c := b - 1) (b := b) (by omega) hb
      have := (H b hb).1
      have := (H (b - 1) (by omega)).1
      have := st_le d (b - 1); have := st_le d' (b - 1)
      omega
  by_cases h1 : st d b = b
  · have := (H b hb).2
    rwa [h1, key.1 h1] at this
  · have h2 : ¬ st d' b = b := fun h2 => h1 (key.2 h2)
    rw [st_eq_iff h, not_not] at h1
    rw [st_eq_iff h', not_not] at h2
    rw [h1, h2]

def mono {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) : GL (Fin N) F where
  val := Matrix.of fun a b => if a = σ b then t b else 0
  inv := Matrix.of fun a b => if b = σ a then (t a)⁻¹ else 0
  val_inv := by
    ext a b
    obtain ⟨c, rfl⟩ := σ.surjective a
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · by_cases h : σ c = b
      · subst h; simp [ht]
      · simp [h, Ne.symm h]
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · by_cases h : a = b
      · subst h; simp [ht]
      · simp [h]
    · intro x _ hx; simp [hx]
    · simp

lemma mono_val {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (a b : Fin N) :
    (mono σ t ht).val a b = if a = σ b then t b else 0 := rfl

lemma mono_rel {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (u u' : GL (Fin N) F)
    (h : u * mono σ t ht = mono σ t ht * u') (c b : Fin N) : u.val (σ c) (σ b) * t b = t c * u'.val c b := by
  have := congrArg (fun x : GL (Fin N) F => x.val (σ c) b) h
  simpa [Units.val_mul, Matrix.mul_apply, mono_val] using this

def perm {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun b => ⟨sg k d b, by
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb; omega
      · rw [sg_ge d (not_lt.1 hb)]; exact b.2⟩)
    (Finite.injective_iff_bijective.1 fun a b hab => Fin.ext (sg_inj h (congrArg Fin.val hab)))

lemma perm_val {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) (b : Fin N) : (perm hk h b : ℕ) = sg k d b := rfl

def cell {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : GL (Fin N) F :=
  mono (perm hk h) (fun b => d (st d b)) fun b => st_ne h b

def dat (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) (a : ℕ) : F :=
  if k ≤ a then 1 else if a = 0 then (p.1 : F) else if h : a - 1 < k - 1 then p.2 ⟨a - 1, h⟩ else 1

lemma dat_good (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) : Good k (dat k p) := by
  refine ⟨?_, fun a ha => by simp [dat, ha]⟩
  unfold dat
  split_ifs <;> simp_all

lemma dat_inj {k : ℕ} (hk : 0 < k) : Function.Injective (dat (F := F) k) := by
  intro p q h
  ext i
  · have := congrFun h 0
    simpa [dat, hk.ne'] using this
  · have := congrFun h (i + 1)
    have hi := i.2
    have h1 : ¬ k ≤ i + 1 := by omega
    simpa [dat, h1] using this

lemma cell_inj {k N : ℕ} (hk : k < N) {d d' : ℕ → F} (h : Good k d) (h' : Good k d') (H : cell hk h = cell hk h') :
    d = d' := by
  refine ext_of h h' fun b hb => ?_
  have h1 := congrArg (fun x : GL (Fin N) F => x.val (perm hk h ⟨b, by omega⟩) ⟨b, by omega⟩) H
  simp only [cell, mono_val, if_true] at h1
  split_ifs at h1 with h2
  · exact ⟨congrArg Fin.val h2, h1⟩
  · exact absurd h1 (st_ne h b)

end Comb

theorem relevant_cells : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  intro g _ N L hs hco k hk0 hk
  refine ⟨Finset.univ.image fun p : (ZMod g)ˣ × (Fin (k - 1) → ZMod g) => cell hk (dat_good k p), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ fun p q h => dat_inj hk0 (cell_inj hk _ _ h)]
    simp [Nat.totient_prime (Fact.out : g.Prime)]
  · intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    refine ⟨fun a b hab => ?_, perm hk h, fun a b hab => ?_⟩
    · simp only [cell, mono_val, Fin.ext_iff, perm_val]
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb
        rw [if_neg (by omega), if_neg (by omega)]
      · rw [sg_ge _ (not_lt.1 hb), st_ge h (not_lt.1 hb)]
    · by_contra h1
      exact hab (by simp only [cell, mono_val]; exact if_neg h1)
  · intro w hw u u' hu hu' hb hb' H
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    set d := dat k p
    have rel := mono_rel _ _ _ u u' H
    unfold Lev.chi
    congr 1
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have r := rel c b
    simp only [Lev.Edge, hs, hco, Units.val_one, one_mul, Bool.false_eq_true, if_false, perm_val]
    have tb := st_ne h b
    have tc := st_ne h c
    have hσ : ∀ x : Fin N, (x : ℕ) < k → sg k d x < k := fun x hx => sg_lt h hx
    have hσ' : ∀ x : Fin N, k ≤ (x : ℕ) → sg k d x = x := fun x hx => sg_ge d hx
    have z : c ≠ b → (k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c) →
        u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := by
      intro hne hh
      have e1 : u'.val c b = 0 → u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := fun e =>
        ⟨by rw [e, mul_zero] at r; exact (mul_eq_zero.1 r).resolve_right tb, e⟩
      rcases hh with hh | hh | hh
      · exact e1 (by rw [hb' c b (Or.inr hh), if_neg hne])
      · exact e1 (hu'.2 _ _ hh)
      · have e : u.val (perm hk h c) (perm hk h b) = 0 := hu.2 _ _ hh
        exact ⟨e, by rw [e, zero_mul] at r; exact (mul_eq_zero.1 r.symm).resolve_left tc⟩
    by_cases hne : c = b
    · subst hne; simp
    by_cases hh : k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c
    · obtain ⟨z1, z2⟩ := z hne hh
      simp [z1, z2]
    · have hne' : (c : ℕ) ≠ b := fun e => hne (Fin.ext e)
      simp only [not_or, Fin.lt_def] at hh
      rcases sg_dich h (c := c) (b := b) (by omega) (by omega) with ⟨e1, e2⟩ | e
      · have e3 : u.val (perm hk h c) (perm hk h b) = u'.val c b := by
          rw [e1, mul_comm] at r
          exact mul_left_cancel₀ tb r
        rw [e3]
        exact if_congr (by omega) rfl rfl
      · omega

end GlobalTheory.BadShare.Cells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevel
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem intCast_eq_of_dvd_sub {k : ℕ} {x y : ℤ} (h : (k : ℤ) ∣ x - y) : (x : ZMod k) = (y : ZMod k) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y k).2 (by rw [← neg_sub]; exact dvd_neg.2 h)

theorem exists_scalar_mod_level : ∀ (N l a M : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → 0 < M → ¬ l ∣ M →
    ∃ c ∈ Gam N l, (∀ g : SL(2, ℤ), c * g * c⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma (M * N * l ^ a)) ∧
      ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (l ^ a)) = if i = j then -1 else 0 := by
  intro N l a M _ hl _ hlN _ hlM
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ((M * N : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = ((l ^ (a + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  have hcop : IsCoprime Q L := by
    rw [hQ, hL, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2
      (fun h => (hl.dvd_mul.1 h).elim hlM hlN)))
  obtain ⟨α, β, hab⟩ := hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = β * L - α * Q := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = Q * L := ⟨_, rfl⟩
  have e1 : t * t + m * (4 * α * β) = 1 := by
    rw [ht, hm]; linear_combination (α * Q + β * L + 1) * hab
  have hc : IsCoprime t (m ^ 2) := IsCoprime.pow_right ⟨t, 4 * α * β, by linear_combination e1⟩
  obtain ⟨u, v, e2⟩ := hc
  have hut : u - t = m * (4 * α * β * u - t * v * m) := by linear_combination (-u) * e1 + t * e2
  have ht1 : t - 1 = Q * (-2 * α) := by rw [ht]; linear_combination hab
  have ht2 : t - -1 = L * (2 * β) := by rw [ht]; linear_combination (-1 : ℤ) * hab
  obtain ⟨c, hcm⟩ : ∃ c : SL(2, ℤ), (c : Matrix (Fin 2) (Fin 2) ℤ) = !![t, -(m * v); m, u] :=
    ⟨⟨!![t, -(m * v); m, u], by rw [Matrix.det_fin_two_of]; linear_combination e2⟩, rfl⟩
  have h00 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = t := by rw [hcm]; rfl
  have h01 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(m * v) := by rw [hcm]; rfl
  have h10 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = m := by rw [hcm]; rfl
  have h11 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = u := by rw [hcm]; rfl
  have hNQ : (N : ℤ) ∣ Q := hQ ▸ Int.natCast_dvd_natCast.2 (dvd_mul_left N M)
  have hlaL : ((l ^ a : ℕ) : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (pow_dvd_pow l (Nat.le_succ a))
  have hlL : (l : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (dvd_pow_self l (Nat.succ_ne_zero a))
  have hKm : ((M * N * l ^ a : ℕ) : ℤ) ∣ m := by
    rw [hm, hQ, hL, ← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_left _ (pow_dvd_pow l (Nat.le_succ a)))
  have hNm : (N : ℤ) ∣ m := hm ▸ hNQ.mul_right L
  have hlm : (l : ℤ) ∣ m := hm ▸ hlL.mul_left Q
  have hlam : ((l ^ a : ℕ) : ℤ) ∣ m := hm ▸ hlaL.mul_left Q

  have tN : ((t : ℤ) : ZMod N) = 1 := by
    simpa using intCast_eq_of_dvd_sub (k := N) (y := 1) (hNQ.trans ⟨_, ht1⟩)
  have uN : ((u : ℤ) : ZMod N) = 1 := by
    have hd : (N : ℤ) ∣ u - 1 := by
      rw [show u - 1 = (u - t) + (t - 1) by ring]
      exact dvd_add (hNm.trans ⟨_, hut⟩) (hNQ.trans ⟨_, ht1⟩)
    simpa using intCast_eq_of_dvd_sub (k := N) hd
  have mN : ((m : ℤ) : ZMod N) = 0 := by simpa using intCast_eq_of_dvd_sub (k := N) (y := 0) (by simpa using hNm)
  have ml : ((m : ℤ) : ZMod l) = 0 := by simpa using intCast_eq_of_dvd_sub (k := l) (y := 0) (by simpa using hlm)

  have tla : ((t : ℤ) : ZMod (l ^ a)) = -1 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := -1) (hlaL.trans ⟨_, ht2⟩)
  have ula : ((u : ℤ) : ZMod (l ^ a)) = -1 := by
    have hd : ((l ^ a : ℕ) : ℤ) ∣ u - -1 := by
      rw [show u - -1 = (u - t) + (t - -1) by ring]
      exact dvd_add (hlam.trans ⟨_, hut⟩) (hlaL.trans ⟨_, ht2⟩)
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) hd
  have mla : ((m : ℤ) : ZMod (l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := 0) (by simpa using hlam)

  have mK : ((m : ℤ) : ZMod (M * N * l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := M * N * l ^ a) (y := 0) (by simpa using hKm)
  have uK : ((u : ℤ) : ZMod (M * N * l ^ a)) = t := intCast_eq_of_dvd_sub (hKm.trans ⟨_, hut⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [Gam, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
    simp only [h00, h11, h10, tN, uN, mN, ml, and_self]
  · intro g
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv]
    set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * N * l ^ a)))
    have hsc : (↑(φ c) : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) =
        ((t : ℤ) : ZMod (M * N * l ^ a)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [φ, Matrix.SpecialLinearGroup.map_apply_coe, h00, h01, h10, h11, mK, uK]
    have hcomm : φ c * φ g = φ g * φ c := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hsc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, tla, ula, mla]

end GlobalTheory.KZ
end

