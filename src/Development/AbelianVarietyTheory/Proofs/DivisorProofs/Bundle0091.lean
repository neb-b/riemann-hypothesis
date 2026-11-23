module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderProdSubProd
section
namespace GlobalTheory.OrderProductDifference

open MvPowerSeries

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (a i))
    (hb : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (b i))
    (hab : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) :
    ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  classical
  revert ha hb hab
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert j s hj ih =>
    intro ha hb hab
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have key : ∏ i ∈ insert j s, a i - ∏ i ∈ insert j s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hj, Finset.prod_insert hj]; ring
    have hbs : ∑ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, b i) :=
      le_trans (Finset.sum_le_sum fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (MvPowerSeries.le_order_prod _ _)
    rw [key, Finset.sum_insert hj]
    refine le_trans ?_ MvPowerSeries.min_order_le_add
    refine le_min ?_ ?_
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = (k j : ℕ∞) + (∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1) := by rw [add_assoc]
        _ ≤ MvPowerSeries.order (a j) + MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
          add_le_add (ha j (Finset.mem_insert_self _ _)) ih'
        _ ≤ _ := MvPowerSeries.le_order_mul
    · calc ((k j : ℕ) : ℕ∞) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + 1
          = ((k j : ℕ∞) + 1) + ∑ i ∈ s, ((k i : ℕ) : ℕ∞) := by rw [add_right_comm]
        _ ≤ MvPowerSeries.order (a j - b j) + MvPowerSeries.order (∏ i ∈ s, b i) :=
          add_le_add (hab j (Finset.mem_insert_self _ _)) hbs
        _ ≤ _ := MvPowerSeries.le_order_mul

theorem target : ∀ {R τ ι : Type} [inst : CommRing R] (s : Finset ι) (a b : ι → MvPowerSeries τ R) (k : ι → ℕ), (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (a i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (b i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) → ∑ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
  fun s a b k ha hb hab => order_prod_sub_prod s a b k ha hb hab

end GlobalTheory.OrderProductDifference
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactor
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_of_mono_factor {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A K : C} [GrpObj A] (i : K ⟶ A) [Mono i] (m : K ⊗ K ⟶ K) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[A])
    (e : 𝟙_ C ⟶ K) (he : e ≫ i = η[A]) (v : K ⟶ K) (hv : v ≫ i = i ≫ ι[A]) :
    ∃ _ : GrpObj K, IsMonHom i := by
  letI M : MonObj K :=
    { one := e, mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : e ▷ K ≫ (i ⊗ₘ i) = 𝟙_ C ◁ i ≫ η[A] ▷ A := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, he, tensorHom_def']
        rw [reassoc_of% h1, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : K ◁ e ≫ (i ⊗ₘ i) = i ▷ 𝟙_ C ≫ A ◁ η[A] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, he, MonoidalCategory.tensorHom_def]
        rw [reassoc_of% h1, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        have h1 : m ▷ K ≫ m ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[A] ▷ A ≫ μ[A] := by
          simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        have h2 : K ◁ m ≫ m ≫ i = (i ⊗ₘ (i ⊗ₘ i)) ≫ A ◁ μ[A] ≫ μ[A] := by
          simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        simp only [Category.assoc]
        rw [h1, h2, MonObj.mul_assoc (X := A), associator_naturality_assoc] }
  letI G : GrpObj K :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift v (𝟙 K) ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift (i ≫ ι[A]) i = i ≫ lift ι[A] (𝟙 A) := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.left_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)]
      right_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift (𝟙 K) v ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift i (i ≫ ι[A]) = i ≫ lift (𝟙 A) ι[A] := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.right_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)] }
  exact ⟨G, { one_hom := he, mul_hom := hm }⟩

theorem overScheme_grpObj_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A),
    Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) →
    (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  intro T A K _ i hi ⟨m, hm⟩ ⟨e, he⟩ ⟨v, hv⟩
  exact grpObj_of_mono_factor i m hm e he v hv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntExistsLevelNotDvdMulLift
section
namespace GlobalTheory

theorem padicInt_toZModPow_not_dvd_mul :
    ∀ (l : ℕ) [Fact l.Prime] (c : ℤ_[l]), c ≠ 0 → ∀ e : ℕ, 0 < e →
      ∃ N : ℕ, ∀ m : ℤ, PadicInt.toZModPow N c = (m : ZMod (l ^ N)) →
        ¬ ((l : ℤ) ^ N ∣ e * m) := by
  intro l _ c hc e he
  have hl : l.Prime := Fact.out
  refine ⟨c.valuation + e.factorization l + 1, ?_⟩
  intro m hm hdvd
  set v := c.valuation with hv
  set a := e.factorization l with ha
  have hm1 : (l : ℤ) ^ (v + 1) ∣ m := by
    have he' : (e : ℤ) = (l : ℤ) ^ a * ((e / l ^ a : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self e l).symm
    have hcop : IsCoprime ((l : ℤ) ^ (v + 1)) ((e / l ^ a : ℕ) : ℤ) := by
      have h := (Nat.coprime_ordCompl hl he.ne').pow_left (v + 1)
      have := Nat.isCoprime_iff_coprime.mpr h
      simpa [Nat.cast_pow] using this
    rw [he', show v + a + 1 = a + (v + 1) by ring, pow_add, mul_assoc] at hdvd
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero a (by exact_mod_cast hl.ne_zero : (l : ℤ) ≠ 0))).mp hdvd
    exact hcop.dvd_of_dvd_mul_left h2
  have h0 : PadicInt.toZModPow (v + 1) c = 0 := by
    rw [← PadicInt.cast_toZModPow (v + 1) (v + a + 1) (by omega) c, hm,
      ZMod.cast_intCast (pow_dvd_pow l (by omega))]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm1
  have hmem : c ∈ (Ideal.span {(l : ℤ_[l]) ^ (v + 1)} : Ideal ℤ_[l]) := by
    rw [← PadicInt.ker_toZModPow]
    exact h0
  have := (PadicInt.mem_span_pow_iff_le_valuation c hc (v + 1)).mp hmem
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
section
open IsLocalRing

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem norm_lt_one_of_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {v : V} (hv : v ∈ maximalIdeal V) : ‖κ (algebraMap V (FractionRing V) v)‖ < 1 := by
  have hle : ‖κ (algebraMap V (FractionRing V) v)‖ ≤ 1 := (hV _).2 ⟨v, rfl⟩
  refine lt_of_le_of_ne hle fun h1 => ?_
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at h1
  have hι : algebraMap V (FractionRing V) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hv0
  have hinv : ‖κ (algebraMap V (FractionRing V) v)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, norm_inv, h1, inv_one]
  obtain ⟨w, hw⟩ := (hV _).1 hinv
  have hvw : v * w = 1 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hι]
  exact (mem_maximalIdeal _).1 hv ⟨⟨v, w, hvw, by rw [mul_comm]; exact hvw⟩, rfl⟩

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    rw [map_natCast]
  rw [this, PadicAlgCl.norm_extends, Padic.norm_p]

theorem p_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ((p : ℕ) : V) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ ≤ 1 := (hV _).2 ⟨_, rfl⟩
  have h2 : κ (algebraMap V (FractionRing V) ((p : ℕ) : V)) *
      κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) = 1 := by
    rw [← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one, map_natCast, map_natCast, norm_natCast_p] at h3
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ)⁻¹ * ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) h1) (inv_lt_one_of_one_lt₀ hp)
  linarith

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem exists_norm_le_pow
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∀ x ∈ maximalIdeal V ^ n,
      ‖κ (algebraMap V (FractionRing V) x)‖ ≤ r ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨‖κ (algebraMap V (FractionRing V) ϖ)‖, norm_nonneg _,
    norm_lt_one_of_mem_maximalIdeal hV (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ),
    fun n x hx => ?_⟩
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨w, rfl⟩ := hx
  rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow]
  have hw : ‖κ (algebraMap V (FractionRing V) w)‖ ≤ 1 := (hV _).2 ⟨w, rfl⟩
  exact mul_le_of_le_one_right (by positivity) hw

theorem smul_top_eq (I : Ideal V) : (I • ⊤ : Submodule V V) = I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem padicInt_mem_range
    (hc : IsAdicComplete (maximalIdeal V) V)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) (z : ℤ_[p]) :
    ∃ L : V, κ (algebraMap V (FractionRing V) L) = algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) := by
  set f : ℕ → V := fun n => ((z.appr n : ℕ) : V) with hf
  have hpm := p_mem_maximalIdeal hV
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (maximalIdeal V) ^ m • (⊤ : Submodule V V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_top_eq]
    obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr z m n hmn
    have hmono : z.appr m ≤ z.appr n := PadicInt.appr_mono z hmn
    have heq : z.appr n = z.appr m + p ^ m * c := by
      generalize p ^ m * c = k at hc; omega
    have : f m - f n = ((p : ℕ) : V) ^ m * (-(c : V)) := by
      simp only [hf, heq]; push_cast; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm m)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcauchy
  refine ⟨L, ?_⟩
  obtain ⟨r, hr0, hr1, hr⟩ := exists_norm_le_pow hV
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbound : ∀ n : ℕ, ‖κ (algebraMap V (FractionRing V) L) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖
      ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
    intro n
    have h1 : f n - L ∈ maximalIdeal V ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_top_eq] at this
    have h1' := hr n _ h1
    have hfn : κ (algebraMap V (FractionRing V) (f n)) =
        algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      simp only [hf, map_natCast, PadicInt.coe_natCast]
    have h2 : ‖z - ((z.appr n : ℕ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n z)
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    have h2' : ‖algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) -
        algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, PadicInt.norm_def.symm, norm_sub_rev]
      exact h2
    calc _ = ‖(κ (algebraMap V (FractionRing V) L) - κ (algebraMap V (FractionRing V) (f n))) +
          (κ (algebraMap V (FractionRing V) (f n)) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]))‖ := by
            congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
        gcongr
        · rw [norm_sub_rev, ← map_sub, ← map_sub]; exact h1'
        · rw [hfn]; exact h2'
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n + ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp))
    simpa using this
  have h0 := ge_of_tendsto' ht hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

theorem padic_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (κ : FractionRing V →+* PadicAlgCl p),
    (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
    ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  intro p _ V _ _ _ _ hc κ hV q
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hp
  have hz : ‖q * (p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact hk.le
  obtain ⟨L, hL⟩ := padicInt_mem_range hc hV (⟨q * (p : ℚ_[p]) ^ k, hz⟩ : ℤ_[p])
  have hpne : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨algebraMap V (FractionRing V) L * (((p : ℕ) : FractionRing V) ^ k)⁻¹, ?_⟩
  rw [map_mul, hL, map_inv₀, map_pow, map_natCast]
  show algebraMap ℚ_[p] (PadicAlgCl p) (q * (p : ℚ_[p]) ^ k) * _ = _
  simp only [map_mul, map_pow, map_natCast]
  field_simp

end GlobalTheory.PadicUnitBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilOptionEquivLeftRenameSome
section
open MvPolynomial

namespace GlobalTheory

theorem pencil_optionEquivLeft_rename_some {τ : Type} (a : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.optionEquivLeft_C]
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p x hp => simp [map_mul, hp, MvPolynomial.optionEquivLeft_X_some]

theorem pencil_natDegree_det_le_rowSum {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial R)) (d : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro g _
  calc (Equiv.Perm.sign g • ∏ i, M (g i) i).natDegree ≤ (∏ i, M (g i) i).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
        · rw [sg, one_smul]
        · rw [sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (M (g i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, d (g i) := Finset.sum_le_sum fun i _ => h _ _
    _ = ∑ i, d i := Equiv.sum_comp g d

theorem pencil_map_entry {τ : Type} (a b : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ
      (MvPolynomial.X none * MvPolynomial.rename some a + MvPolynomial.rename some b) =
      Polynomial.X * Polynomial.C a + Polynomial.C b := by
  simp [map_add (f := _), map_mul, MvPolynomial.optionEquivLeft_X_none, pencil_optionEquivLeft_rename_some]

theorem pencil_det_adjugate_coeff :
    ∀ {τ : Type} {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι (MvPolynomial τ ℂ)),
      let Z : Matrix ι ι (MvPolynomial (Option τ) ℂ) := fun i j =>
        MvPolynomial.X none * MvPolynomial.rename some (A i j) + MvPolynomial.rename some (B i j);
      (∀ k, Fintype.card ι < k → (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff k = 0) ∧
      (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff (Fintype.card ι) = A.det ∧
      ∀ k i j, Fintype.card ι ≤ k →
        (MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i)).coeff k = 0 := by
  intro τ ι _ _ A B Z
  set e : MvPolynomial (Option τ) ℂ →+* Polynomial (MvPolynomial τ ℂ) :=
    (MvPolynomial.optionEquivLeft ℂ τ).toRingEquiv.toRingHom with he
  have hZ : e.mapMatrix Z = (Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
      B.map Polynomial.C := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Z, he]
    exact pencil_map_entry (A i j) (B i j)
  have hdet : MvPolynomial.optionEquivLeft ℂ τ Z.det =
      ((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C).det := by
    rw [← hZ, ← RingHom.map_det]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hdet]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((Polynomial.natDegree_det_X_add_C_le A B).trans_lt hk)
  · rw [hdet, Polynomial.coeff_det_X_add_C_card]
  · intro k i j hk
    have hadj : MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i) =
        (((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
          B.map Polynomial.C).updateRow i (Pi.single j 1)).det := by
      have := congrFun (congrFun (RingHom.map_adjugate e Z) j) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
      change e (Z.adjugate j i) = _
      rw [this, hZ, Matrix.adjugate_apply]
    rw [hadj]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    refine lt_of_le_of_lt (pencil_natDegree_det_le_rowSum _ (fun r => if r = i then 0 else 1) ?_) ?_
    · intro r c
      by_cases hr : r = i
      · subst hr
        simp only [Matrix.updateRow_self, if_true]
        by_cases hc : c = j
        · subst hc; simp
        · simp [Pi.single_apply, hc]
      · simp only [Matrix.updateRow_ne hr, if_neg hr, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul]
        compute_degree
    · have : (∑ r, if r = i then 0 else 1 : ℕ) = Fintype.card ι - 1 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionIsUnitOfCoeffZero
section
namespace GlobalTheory

open IsLocalRing

open IsLocalRing in
theorem _root_.GlobalTheory.preTilt_isLocalRing : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Fact ¬IsUnit (p : O)], IsLocalRing (PreTilt O p) := by
  intro p _ O _ _ _
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by
    refine ⟨fun x hx => ?_⟩
    have hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x) := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [← Perfection.coeff_pow_p' x n] at ih
        exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih
    let y : Perfection (ModP O p) p := ⟨fun n => ↑(hunit n).unit⁻¹, fun n => by
      have key : (hunit (n + 1)).unit ^ p = (hunit n).unit :=
        Units.ext (by simpa using Perfection.coeff_pow_p' x n)
      rw [← Units.val_pow_eq_pow_val, inv_pow, key]⟩
    have hxy : x * y = 1 := Perfection.ext fun n => by
      rw [map_mul, map_one]
      show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1
      exact (hunit n).mul_val_inv
    exact ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  exact (Perfection.coeff (ModP O p) p 0).domain_isLocalRing

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMulGaussianBounded
section
namespace GlobalTheory.PolynomialGaussianBounded

theorem poly_mul_gaussian_bounded :
    ∀ (c : ℝ), (0 : ℝ) < c → ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r →
      ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : ((1 : ℝ) + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    calc ((1 : ℝ) + r) ^ N ≤ (Real.exp r) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp ((N : ℝ) * r) := by rw [← Real.exp_nat_mul]
  calc ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ)))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ (2 : ℕ))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * c * r - N)]

end GlobalTheory.PolynomialGaussianBounded
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdOfFnEqSingle
section
universe u_1

namespace GlobalTheory.ProductOfFnSingle

theorem prod_ofFn_eq_single {M : Type u_1} [inst : Monoid M] {d : ℕ} (g : Fin d → M) (j : Fin d)
    (h : ∀ (i : Fin d), i ≠ j → g i = (1 : M)) : List.prod (List.ofFn g) = g j := by
  induction d with
  | zero => exact j.elim0
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have hrest : List.prod (List.ofFn fun i : Fin d => g i.succ) = 1 := by
        apply List.prod_eq_one
        intro x hx
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero i)
      rw [hrest, mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      rw [h 0 (fun e => hj e.symm), one_mul]
      exact ih (fun i => g i.succ) j' (fun i hi => h _ (fun e => hi (Fin.succ_injective _ e)))

end GlobalTheory.ProductOfFnSingle
end

