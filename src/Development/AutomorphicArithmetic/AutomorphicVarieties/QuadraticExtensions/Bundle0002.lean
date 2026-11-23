module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.HasMuQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem root_of_hasMu (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L] (hA : A.HasMu l)
    (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨hl, hker⟩ := hA
  obtain ⟨k, hk⟩ := hl.trans h1
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    @IsCyclotomicExtension.isGalois {N} ℚ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ)
  have hη : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ∀ b : ℕ, (ζ ^ k) ^ b = (ζ ^ k) ^ (b % l) := fun b => by
    conv_lhs => rw [← Nat.mod_add_div b l]
    rw [pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]
  have hmem : ζ ^ k ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hfix : ∀ x : L, τ (j x) = j x := fun x => hτ _ ⟨x, rfl⟩
    have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, h2.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one hτN
    have hmod : a ≡ 1 [MOD l] := hker a ((h3 τ a ha.symm).1 hfix)
    have hpow : (ζ ^ k) ^ a = (ζ ^ k) ^ 1 := by
      rw [key a, key 1, show a % l = 1 % l from hmod]
    rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, IsPrimitiveRoot.of_map_of_injective (f := (j : L →+* CyclotomicField N ℚ)) ?_ j.toRingHom.injective⟩
  rw [show (j : L →+* CyclotomicField N ℚ) x = ζ ^ k from hx]
  exact hη

private theorem unitsMap_nat {m n a : ℕ} (h : m ∣ n) (u : (ZMod n)ˣ) (e : (u : ZMod n) = (a : ZMod n)) :
    ((ZMod.unitsMap h u : (ZMod m)ˣ) : ZMod m) = (a : ZMod m) := by
  rw [ZMod.unitsMap_def]
  simp [Units.coe_map, ZMod.castHom_apply, e, ZMod.cast_natCast h]

private theorem ker_sup {A B : AbF} {a : ℕ} (h : (A.sup B).ker a) : A.ker a ∧ B.ker a := by
  obtain ⟨u, ⟨hu1, hu2⟩, e⟩ := h
  exact ⟨⟨_, hu1, unitsMap_nat _ _ e⟩, ⟨_, hu2, unitsMap_nat _ _ e⟩⟩

private theorem hasMu_sup_left {A : AbF} (B : AbF) {l : ℕ} (h : A.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_left h.1 _, fun a ha => h.2 a (ker_sup ha).1⟩

private theorem hasMu_sup_right (A : AbF) {B : AbF} {l : ℕ} (h : B.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_right h.1 _, fun a ha => h.2 a (ker_sup ha).2⟩

private theorem hasMu_withI (M : AbF) : (withI M).HasMu 4 :=
  hasMu_sup_right M (AbF.hasMu_cyc (l := 4) (q := 1) (by norm_num) (by norm_num))

theorem UpperTheory.V.Two.hasMuQ :
    (∀ (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L], A.HasMu l → IsAbField A L → ∃ ζ : L, IsPrimitiveRoot ζ l) ∧
      (∀ (M : AbF) (L : Type) [Field L] [NumberField L], IsAbField (withI M) L → ∃ ζ : L, IsPrimitiveRoot ζ 4) ∧
      ∀ (M : AbF) (q d : ℕ) (L : Type) [Field L] [NumberField L], IsAbField (base2 M q d) L → ∃ ζ : L, IsPrimitiveRoot ζ 4 := by
  refine ⟨fun l A L _ _ hA hL => root_of_hasMu l A L hA hL,
    fun M L _ _ hL => root_of_hasMu 4 _ L (hasMu_withI M) hL,
    fun M q d L _ _ hL => root_of_hasMu 4 _ L ?_ hL⟩
  exact hasMu_sup_left _ (hasMu_sup_left _ (hasMu_withI M))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxAdic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem two_pow_dvd_intCast_padic_iff (k : ℤ) (n : ℕ) : (2 : ℤ_[2]) ^ n ∣ (k : ℤ_[2]) ↔ (2 : ℤ) ^ n ∣ k := by
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (k : ℤ_[2]) n).symm.trans
    (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := k) (n := n))
  rw [Ideal.mem_span_singleton] at h
  exact_mod_cast h

private theorem index_closed_dyadic_subgroup (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p a : ℕ) (hH : IsClosed (H : Set ℤ_[2]ˣ))
    (hu : u ∈ H) (hp : (u : ℤ_[2]) = p) (ha : 2 ≤ a) (h1 : (2 : ℤ) ^ a ∣ (p : ℤ) ^ 2 - 1)
    (h2 : ¬ (2 : ℤ) ^ (a + 1) ∣ (p : ℤ) ^ 2 - 1) (h3 : ¬ (2 : ℤ) ^ a ∣ (p : ℤ) - 1) :
    H.index ≠ 0 ∧ 2 * H.index ≤ Nat.totient (2 ^ a) := by
  have hu2 : ((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = (((p : ℤ) ^ 2 - 1 : ℤ) : ℤ_[2]) := by
    push_cast [Units.val_pow_eq_pow_val, hp]
    ring
  have hem : emultiplicity ((2 : ℕ) : ℤ_[2]) (((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1) = (a : ℕ∞) := by
    rw [emultiplicity_eq_coe, hu2]
    simp only [Nat.cast_ofNat, two_pow_dvd_intCast_padic_iff]
    exact ⟨h1, h2⟩
  have hle : KStar.TotallyRealRoots.princ 2 a ≤ H :=
    KStar.TotallyRealRoots.princ_le_of_isClosed (by omega) (fun _ => ha) hH (H.pow_mem hu 2) hem
  have hnot : u ∉ KStar.TotallyRealRoots.princ 2 a := by
    rw [KStar.TotallyRealRoots.mem_princ, hp]
    intro h
    apply h3
    rw [← two_pow_dvd_intCast_padic_iff]
    exact_mod_cast h
  have hidx : (KStar.TotallyRealRoots.princ 2 a).index ≤ Nat.totient (2 ^ a) := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_le_card_group _
  have hpos : 0 < (KStar.TotallyRealRoots.princ 2 a).index := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker]
    exact Nat.card_pos
  have hr := Subgroup.relIndex_mul_index hle
  have hr1 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h hu)
  have hr0 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 0 := by
    intro h
    rw [h, zero_mul] at hr
    omega
  refine ⟨?_, ?_⟩
  · intro h
    rw [h, mul_zero] at hr
    omega
  · calc 2 * H.index ≤ (KStar.TotallyRealRoots.princ 2 a).relIndex H * H.index :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (KStar.TotallyRealRoots.princ 2 a).index := hr
      _ ≤ Nat.totient (2 ^ a) := hidx

theorem UpperTheory.V.Two.idxAdic :
    ∀ (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p c : ℕ), IsClosed (H : Set ℤ_[2]ˣ) → u ∈ H → (u : ℤ_[2]) = p → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → H.index ≠ 0 ∧ H.index ≤ c := by
  intro H u p c hH hu hp hpc
  rcases hpc with ⟨hp8, rfl⟩ | ⟨hp16, rfl⟩
  · have hk : p = 8 * (p / 8) + 3 := by omega
    generalize p / 8 = k at hk
    subst hk
    have e : ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 = 16 * (4 * (k : ℤ) ^ 2 + 3 * k) + 8 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (3 + 1) ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (8 * k + 3) 3 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 3) = 4 := by decide
    omega
  · have hk : p = 16 * (p / 16) + 7 := by omega
    generalize p / 16 = k at hk
    subst hk
    have e : ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 = 32 * (8 * (k : ℤ) ^ 2 + 7 * k + 1) + 16 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (4 + 1) ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (16 * k + 7) 4 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 4) = 8 := by decide
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hv := congrArg A.valuation h
  rw [map_pow, map_one] at hv
  exact (pow_eq_one_iff.mp hv).resolve_right hm

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff]
    refine Subring.sum_mem A.toSubring (fun j _ => ?_)
    have hj : η ^ j ∈ A := by
      rw [← ValuationSubring.valuation_le_one_iff, map_pow, h1, one_pow]
    exact hj
  rw [← mul_neg_geom_sum, map_mul, Valuation.map_sub_swap]
  exact mul_lt_one_of_lt_of_le h hS

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  have hS : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have hg := mul_neg_geom_sum η m
    rw [hη, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have h1 : A.valuation η = 1 := aux_one A hm hη
  have hlt : A.valuation ((m : Ω) - ∑ i ∈ Finset.range m, η ^ i) < 1 := by
    have he : (m : Ω) - ∑ i ∈ Finset.range m, η ^ i = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [he]
    exact Valuation.map_sum_lt _ one_ne_zero (fun i _ => power_bounds_of_between A h1 h i)
  rw [hS, sub_zero] at hlt
  exact hv hlt

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hI : g ∈ Inertia (F := ℚ) A := hg
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have hv1 := aux_one A hm hζ
  have key := hI.2 ζ hv1.le
  have hη : (g ζ * ζ⁻¹) ^ m = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : A.valuation (g ζ * ζ⁻¹ - 1) < 1 := by
    have he : g ζ * ζ⁻¹ - 1 = (g ζ - ζ) * ζ⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, map_mul, map_inv₀, hv1, inv_one, mul_one]
    exact key
  have hfin := root_of_unity_eq_one_of_close_residue A hm hA hη hlt
  rwa [mul_inv_eq_one₀ hζ0] at hfin

theorem UpperTheory.V.Two.ineChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] (A : ValuationSubring Ω), ¬ A.valuation (m : Ω) < 1 → Ine (F := ℚ) A ≤ (galChar Ω m).ker := by
  intro Ω _ _ _ m _ A hA g hg
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hfix := inertia_fixes_prime_to_roots A (NeZero.ne m) hA hg hz.pow_eq_one
  rw [galChar_spec m g z hz.pow_eq_one] at hfix
  obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne m)
  have hu : IsPrimitiveRoot u m := IsPrimitiveRoot.coe_units_iff.mp hz
  have heq : u ^ ((galChar Ω m g : ZMod m).val) = u ^ 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_one]
    exact hfix
  have hmod := pow_eq_pow_iff_modEq.mp heq
  rw [← hu.eq_orderOf] at hmod
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((galChar Ω m g : ZMod m)), ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.ineConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : G F Ω), (∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B) ∧
      (∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1) ∧ ∀ (N : ℕ), ∀ s ∈ ineOff F Ω N, v⁻¹ * s * v ∈ ineOff F Ω N := by
  intro F Ω _ _ _ _ _ v
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), y ≠ 0 → (A.valuation y < 1 ↔ y⁻¹ ∉ A) := by
    intro A y hy
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
  have hL : ∀ (w : G F Ω) (B : ValuationSubring Ω) (x : Ω), (w • B).valuation x < 1 ↔ B.valuation (w⁻¹ • x) < 1 := by
    intro w B x
    by_cases hx : x = 0
    · subst hx
      simp
    have hx' : w⁻¹ • x ≠ 0 := by simpa using hx
    rw [hlt _ _ hx, hlt _ _ hx', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'']
  have p1 : ∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B := by
    intro B g hg
    obtain ⟨hd, hi⟩ := hg
    refine ⟨?_, ?_⟩
    · have hd' : g • (v • B) = v • B := hd
      show (v⁻¹ * g * v) • B = B
      rw [mul_smul, mul_smul, hd', inv_smul_smul]
    · intro x hx
      have hvx : (v • B).valuation (v x) ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ← ValuationSubring.valuation_le_one_iff]
        simpa [AlgEquiv.smul_def] using hx
      have h2 := hi (v x) hvx
      rw [hL] at h2
      convert h2 using 2
      simp [AlgEquiv.smul_def, map_sub, AlgEquiv.mul_apply]
  have p2 : ∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1 := by
    intro B N
    rw [hL]
    simp [AlgEquiv.smul_def]
  refine ⟨p1, p2, ?_⟩
  rintro N s ⟨A, hA, hs⟩
  have hA' : v • (v⁻¹ • A) = A := smul_inv_smul v A
  refine ⟨v⁻¹ • A, ?_, ?_⟩
  · rw [← p2, hA']
    exact hA
  · apply p1
    rw [hA']
    exact hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LayerFn
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.layerFn :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), (∃ ζ : F, IsPrimitiveRoot ζ l) → ∃ m, m ≤ n ∧ IsLayer l m F (Fn F Ω l n) := by
  intro F Ω _ _ _ _ _ l _ n hz
  obtain ⟨ζ0, hζ0⟩ := hz
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hl : l ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hl⟩
  haveI : NeZero (l ^ n) := ⟨hl⟩
  have key : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ k ∈ ({l ^ n} : Set ℕ), k ≠ 0 ∧ b ^ k = 1} := by
    unfold Fn
    congr 1
    ext x
    simp only [Polynomial.mem_rootSet, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_eq_left]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero, ne_eq, hl, not_false_eq_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun h0 => ?_, h⟩
      have := congrArg Polynomial.natDegree h0
      simp at this
      exact hp.ne_zero this.1
  haveI hcyc : IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) := by
    rw [key]
    apply IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
    rintro k rfl -
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  haveI : FiniteDimensional F (Fn F Ω l n) := IsCyclotomicExtension.finiteDimensional {l ^ n} F _
  haveI : IsGalois F (Fn F Ω l n) := IsCyclotomicExtension.isGalois {l ^ n} F _
  obtain ⟨μ, hμ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F (Fn F Ω l n) (Set.mem_singleton (l ^ n)) hl
  set f := hμ.autToPow F with hf
  have hinj : Function.Injective f := hμ.autToPow_injective F
  have hcardG : Nat.card Gal((Fn F Ω l n)/F) = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h0 := hζ0.map_of_injective (algebraMap F (Fn F Ω l n)).injective
  have hdvd : Nat.card Gal((Fn F Ω l n)/F) ∣ l ^ n := by
    rcases n with _ | k
    · rw [hcardG]
      have : Nat.card f.range ∣ Nat.card (ZMod (l ^ 0))ˣ := Subgroup.card_subgroup_dvd_card _
      have h1 : Nat.card (ZMod (l ^ 0))ˣ = 1 := by
        rw [pow_zero]
        exact Nat.card_unique
      exact (this.trans h1.dvd).trans (one_dvd _)
    · have hd : l ∣ l ^ (k + 1) := dvd_pow_self l (Nat.succ_ne_zero k)
      set g := ZMod.unitsMap hd with hg
      have hle : f.range ≤ g.ker := by
        rintro _ ⟨σ, rfl⟩
        rw [MonoidHom.mem_ker]
        have hω := hμ.pow_of_dvd (pow_ne_zero k hp.ne_zero) (pow_dvd_pow l (Nat.le_succ k))
        have hlk : l ^ (k + 1) / l ^ k = l := by
          rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
        rw [hlk] at hω
        haveI : NeZero l := ⟨hp.ne_zero⟩
        obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one hω.pow_eq_one
        have hfix : σ (μ ^ l ^ k) = μ ^ l ^ k := by
          rw [← hi, map_pow, AlgEquiv.commutes]
        rw [map_pow, ← IsPrimitiveRoot.autToPow_spec F hμ σ, ← pow_mul, mul_comm, pow_mul] at hfix
        rw [← hf] at hfix
        generalize f σ = u at hfix ⊢
        obtain ⟨ω, hωd⟩ : ∃ ω, ω = μ ^ l ^ k := ⟨_, rfl⟩
        rw [← hωd] at hfix hω
        have hmod : (u : ZMod (l ^ (k + 1))).val ≡ 1 [MOD l] := by
          generalize (u : ZMod (l ^ (k + 1))).val = v at hfix ⊢
          rcases Nat.eq_zero_or_pos v with rfl | hv
          · exfalso
            rw [pow_zero] at hfix
            exact hω.ne_one hp.one_lt hfix.symm
          · have hω0 : ω ≠ 0 := hω.ne_zero hp.ne_zero
            have h3 : ω ^ (v - 1) = 1 := by
              have h4 := hfix
              rw [← Nat.sub_add_cancel hv, pow_succ] at h4
              exact mul_right_cancel₀ hω0 (h4.trans (one_mul ω).symm)
            exact ((Nat.modEq_iff_dvd' hv).mpr ((hω.pow_eq_one_iff_dvd _).mp h3)).symm
        have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
        ext
        rw [hg, ZMod.unitsMap_def]
        simp only [Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_one]
        rw [← ZMod.natCast_val]
        simpa using hc
      have hsurj : Function.Surjective g := ZMod.unitsMap_surjective hd
      have hidx : g.ker.index = l - 1 := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
          Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
      have hker : Nat.card g.ker = l ^ k := by
        have h1 := Subgroup.card_mul_index g.ker
        rw [hidx, Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1)))ˣ), ZMod.card_units_eq_totient,
          Nat.totient_prime_pow hp (Nat.succ_pos k)] at h1
        try simp only [Nat.add_sub_cancel] at h1
        exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) h1
      rw [hcardG]
      calc Nat.card f.range ∣ Nat.card g.ker := Subgroup.card_dvd_of_le hle
        _ = l ^ k := hker
        _ ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨m, hm, ⟨n, hcyc⟩, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank, hmeq]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.MuIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.muIff :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] (n : ℕ) [NeZero n], (∃ ζ : L, IsPrimitiveRoot ζ n) ↔ galOf ℚ L Ω ≤ (galChar Ω n).ker := by
  intro Ω _ _ _ L _ _ _ n _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  have key : ∀ g : G ℚ Ω, ∀ z : Ω, IsPrimitiveRoot z n → (g z = z ↔ galChar Ω n g = 1) := by
    intro g z hz
    rw [galChar_spec n g z hz.pow_eq_one]
    have hiff : z ^ ((galChar Ω n g : ZMod n).val) = z ↔
        (((galChar Ω n g : ZMod n).val : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne n)
      have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp hz
      nth_rewrite 2 [← pow_one (u : Ω)]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
        pow_eq_pow_iff_modEq, ← hu.eq_orderOf, ZMod.natCast_eq_natCast_iff]
    rw [hiff, ZMod.natCast_zmod_val, Nat.cast_one, ← Units.val_one, Units.val_inj]
  constructor
  · rintro ⟨ζ, hζ⟩ g hg
    rw [MonoidHom.mem_ker, ← key g _ (hζ.map_of_injective (algebraMap L Ω).injective)]
    exact hg ζ
  · intro hle
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
    haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    obtain ⟨ζ, hζ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) z).mpr (fun f => by
      have hf := hle (galEmb_mem ℚ L Ω f)
      rw [MonoidHom.mem_ker, ← key _ z hz, galEmb_apply] at hf
      exact hf)
    refine ⟨ζ, ?_⟩
    rw [← hζ] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective (algebraMap L Ω).injective).mp hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SqZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.sqZero :
    ∀ (P : Type) [AddCommGroup P] (f : P →+ P) (n : ℕ), (∀ x, f (f x) = 0) → CardLe f.ker n → CardLe P (n ^ 2) := by
  intro P _ f n hff hk
  obtain ⟨hkf, hkn⟩ := hk
  have hrange : CardLe f.range n := by
    refine CardLe.of_injective ⟨hkf, hkn⟩ (fun y => (⟨y.1, ?_⟩ : f.ker)) ?_
    · obtain ⟨x, hx⟩ := y.2
      rw [AddMonoidHom.mem_ker, ← hx]
      exact hff x
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext h
  obtain ⟨hrf, hrn⟩ := hrange
  have e := QuotientAddGroup.quotientKerEquivRange f
  have hqf : Finite (P ⧸ f.ker) := Finite.of_equiv _ e.toEquiv.symm
  have hq : Nat.card (P ⧸ f.ker) ≤ n := by
    rw [Nat.card_congr e.toEquiv]; exact hrn
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hpos1 : 0 < Nat.card (P ⧸ f.ker) := Nat.card_pos
  have hpos2 : 0 < Nat.card f.ker := Nat.card_pos
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine ⟨hfin, ?_⟩
  rw [hcard, sq]
  exact Nat.mul_le_mul hq hkn
end

