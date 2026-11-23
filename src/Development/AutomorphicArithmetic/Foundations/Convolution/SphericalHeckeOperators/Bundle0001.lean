module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ConstTerm
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem ct_conj (σ : Equiv.Perm (Fin n)) {z : GL (Fin n) F} (hz : z ∈ iwahori F n)
    (hz' : ∀ i j, i < j → (z : Matrix (Fin n) (Fin n) F) i j = 0) :
    (permGL F σ)⁻¹ * z * permGL F σ ∈ iwahori F n := by
  have hent : ∀ i j, (((permGL F σ)⁻¹ * z * permGL F σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (z : Matrix (Fin n) (Fin n) F) (σ i) (σ j) := by
    intro i j
    rw [← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply, inv_inv]
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hz
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [hent]; exact h1 _ _
  · rw [hent]
    rcases lt_trichotomy (σ i) (σ j) with h | h | h
    · rw [hz' _ _ h, map_zero]; exact zero_lt_one
    · exact absurd (σ.injective h) hij.ne'
    · exact h2 _ _ h
  · rw [hent]; exact h3 _

private theorem ct_move (l : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) {x : GL (Fin n) F} (hx : x ∈ iwahori F n) :
    ∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n,
      torusPow F n l * x * permGL F σ = u * torusPow F n l * permGL F σ * y := by
  obtain ⟨u, hu, t, ht, z, hz, rfl⟩ := Parabolic.iwahoriFactorization_symm
    (Parabolic.iwahori_iwahoriFactorization (F := F) (β := (id : Fin n → Fin n)) monotone_id) x hx
  have hu' : u ∈ unipotent F n := by
    have h := Parabolic.mem_unipotentRadical.1 hu.2
    exact ⟨h.1, fun i => by simpa using h.2 i i rfl⟩
  have ht' : ∀ i j, i < j → (t : Matrix (Fin n) (Fin n) F) i j = 0 :=
    fun i j h => Parabolic.mem_levi.1 ht.2 i j h.ne
  have hz' : ∀ i j, i < j → (z : Matrix (Fin n) (Fin n) F) i j = 0 :=
    fun i j h => (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j h
  refine ⟨torusPow F n l * u * (torusPow F n l)⁻¹, diagGL_mul_mul_inv_mem_unipotent F n hu' _,
    ((permGL F σ)⁻¹ * t * permGL F σ) * ((permGL F σ)⁻¹ * z * permGL F σ),
    mul_mem (ct_conj σ ht.1 ht') (ct_conj σ hz.1 hz'), by group⟩

private theorem ct_borel {b : GL (Fin n) F} (hb : b ∈ borel F n) :
    ∃ u ∈ unipotent F n, ∃ l, ∃ x ∈ iwahori F n, b = u * torusPow F n l * x := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n b
  generalize iwasawaExponent F n b = l at h
  refine ⟨u, hu, l, k, ?_, h⟩
  have hkb : k ∈ borel F n := by
    have e : k = (torusPow F n l)⁻¹ * u⁻¹ * b := by rw [h]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (torusPow_mem_borel F n l)) (inv_mem (unipotent_le_borel F n hu))) hb
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff F n).1 hk
  have hA : ∀ i j, ValuativeRel.valuation F ((k : Matrix (Fin n) (Fin n) F) i j) ≤ 1 :=
    fun i j => (Valuation.mem_integer_iff _ _).mp (h1 i j)
  have hB : ∀ i j, ValuativeRel.valuation F (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤ 1 :=
    fun i j => (Valuation.mem_integer_iff _ _).mp (h2 i j)
  rw [mem_iwahori_iff]
  refine ⟨hA, fun i j hij => ?_, fun i => ?_⟩
  · rw [hkb hij, map_zero]; exact zero_lt_one
  · have e := mul_apply_self_of_mem_borel F n ((borel F n).inv_mem hkb) hkb i
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq] at e
    have e' := congrArg (ValuativeRel.valuation F) e
    rw [map_one, map_mul] at e'
    refine le_antisymm (hA i i) ?_
    calc (1 : _) = _ := e'
      _ ≤ 1 * _ := mul_le_mul_left (hB i i) _
      _ = _ := one_mul _

private def ctCell (l : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : Set (GL (Fin n) F) :=
  {g | ∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n, g = u * torusPow F n l * permGL F σ * y}

private def ctBig (σ : Equiv.Perm (Fin n)) : Set (GL (Fin n) F) := {g | ∃ l, g ∈ ctCell l σ}

private theorem ct_normal (g : GL (Fin n) F) : ∃ l, ∃ σ : Equiv.Perm (Fin n), g ∈ ctCell l σ := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  generalize iwasawaExponent F n g = l at h
  have hk' : k ∈ (integralGL F n : Set (GL (Fin n) F)) := hk
  rw [integralGL_eq_iUnion_doubleCoset_permGL] at hk'
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 hk'
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hσ
  obtain ⟨v, hv, y', hy', e⟩ := ct_move l σ hx
  refine ⟨l, σ, u * v, mul_mem hu hv, y' * y, mul_mem hy' hy, ?_⟩
  calc g = u * (torusPow F n l * x * permGL F σ) * y := by rw [h]; group
    _ = _ := by rw [e]; group

private theorem ct_left {p g : GL (Fin n) F} {σ : Equiv.Perm (Fin n)} (hp : p ∈ borel F n)
    (hg : g ∈ ctBig σ) : p * g ∈ ctBig σ := by
  obtain ⟨l, u, hu, y, hy, rfl⟩ := hg
  obtain ⟨u', hu', l', x, hx, e⟩ := ct_borel (b := p * u * torusPow F n l)
    (mul_mem (mul_mem hp (unipotent_le_borel F n hu)) (torusPow_mem_borel F n l))
  obtain ⟨v, hv, y', hy', e'⟩ := ct_move l' σ hx
  refine ⟨l', u' * v, mul_mem hu' hv, y' * y, mul_mem hy' hy, ?_⟩
  calc p * (u * torusPow F n l * permGL F σ * y) = (p * u * torusPow F n l) * permGL F σ * y := by group
    _ = u' * (torusPow F n l' * x * permGL F σ) * y := by rw [e]; group
    _ = _ := by rw [e']; group

private theorem ct_right {g y : GL (Fin n) F} {σ : Equiv.Perm (Fin n)} (hg : g ∈ ctBig σ)
    (hy : y ∈ iwahori F n) : g * y ∈ ctBig σ := by
  obtain ⟨l, u, hu, y', hy', rfl⟩ := hg
  exact ⟨l, u, hu, y' * y, mul_mem hy' hy, by group⟩

private theorem ct_exp {g : GL (Fin n) F} {l : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} (hg : g ∈ ctCell l σ) :
    iwasawaExponent F n g = l := by
  obtain ⟨u, hu, y, hy, rfl⟩ := hg
  rw [mul_assoc (u * torusPow F n l)]
  exact iwasawaExponent_eq F n hu (mul_mem (permGL_mem_integralGL F n σ) (iwahori_le_integralGL F n hy))

private theorem ct_set {g₀ : GL (Fin n) F} {l : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} (hg : g₀ ∈ ctCell l σ) :
    {g | ∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n, g = u * g₀ * y} = ctCell l σ := by
  obtain ⟨u₀, hu₀, y₀, hy₀, rfl⟩ := hg
  ext g
  constructor
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact ⟨u * u₀, mul_mem hu hu₀, y₀ * y, mul_mem hy₀ hy, by group⟩
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact ⟨u * u₀⁻¹, mul_mem hu (inv_mem hu₀), y₀⁻¹ * y, mul_mem (inv_mem hy₀) hy, by group⟩

private theorem ct_open (l : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : IsOpen (ctCell (F := F) l σ) := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (iwahori F n : Set (GL (Fin n) F)), ?_,
    (isOpen_iwahori F n).preimage (by fun_prop), by simp [one_mem]⟩
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := hg
  exact ⟨u, hu, y * (u * torusPow F n l * permGL F σ * y)⁻¹ * x, by rw [mul_assoc]; exact mul_mem hy hx, by group⟩

private noncomputable def ctFun (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂˣ) : GL (Fin n) F → ℂ :=
  (ctBig σ).indicator (sphericalFun (paramChar F z))

private theorem ctFun_right (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂˣ) (g : GL (Fin n) F)
    {y : GL (Fin n) F} (hy : y ∈ iwahori F n) : ctFun σ z (g * y) = ctFun σ z g := by
  by_cases hg : g ∈ ctBig σ
  · rw [ctFun, Set.indicator_of_mem hg, Set.indicator_of_mem (ct_right hg hy)]
    exact sphericalFun_mul_right (isUnramified_paramChar z) g (iwahori_le_integralGL F n hy)
  · have hg' : g * y ∉ ctBig σ := fun h => hg (by
      simpa using ct_right h (inv_mem hy))
    rw [ctFun, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg']

private theorem ctFun_mem (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂˣ) : ctFun (F := F) σ z ∈ psI F z := by
  change ctFun σ z ∈ principalSeriesSpace F n (paramChar F z) ∧ ∀ g, ∀ y ∈ iwahori F n, ctFun σ z (g * y) = ctFun σ z g
  refine ⟨mem_principalSeriesSpace.2 ⟨fun p g => ?_, iwahori F n, isOpen_iwahori F n, fun k hk g => ctFun_right σ z g hk⟩,
    fun g y hy => ctFun_right σ z g hy⟩
  have hφ := (mem_principalSeriesSpace.1 (sphericalFun_mem (isUnramified_paramChar (F := F) z))).1 p g
  have hpb : ∀ q : blockUpper F n (id : Fin n → Fin n), (q : GL (Fin n) F) ∈ borel F n := fun q => q.2
  by_cases hg : g ∈ ctBig σ
  · rw [ctFun, Set.indicator_of_mem hg, Set.indicator_of_mem (ct_left (hpb p) hg)]
    exact hφ
  · have hg' : (p : GL (Fin n) F) * g ∉ ctBig σ := fun h => hg (by
      simpa using ct_left ((borel F n).inv_mem (hpb p)) h)
    rw [ctFun, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg', mul_zero]

private theorem ct_val (z : Fin n → ℂˣ) (g : GL (Fin n) F) :
    sphericalFun (paramChar F z) g =
      monomialChar (iwasawaExponent F n g) z * monomialChar (iwasawaExponent F n g) (halfPoint F n) := by
  change sphericalFun (unramifiedChar (z * halfPoint F n)) g = _
  rw [sphericalFun_unramifiedChar, map_mul]

private theorem ct_cont : Continuous (iwasawaExponent F n) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (integralGL F n : Set (GL (Fin n) F)),
    (isOpen_integralGL F n).preimage (by fun_prop), by simp [one_mem], fun x hx => ?_⟩
  have := iwasawaExponent_mul_of_mem_integralGL F n g hx
  simpa using this

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]

private theorem ct_int {T : GL (Fin n) F → ℂ} (hT : T ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ)
    (Λ : Finset (Fin n → ℤ)) (hΛ : ∀ g, T g ≠ 0 → iwasawaExponent F n g ∈ Λ)
    (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂˣ) :
    ∫ g, T g * ctFun σ z g ∂μ =
      ∑ l ∈ Λ, monomialChar l z * monomialChar l (halfPoint F n) * ∫ g in ctCell l σ, T g ∂μ := by
  have hTi : Integrable T μ := hT.1.continuous.integrable_of_hasCompactSupport hT.2
  have hm : ∀ l, MeasurableSet (ctCell (F := F) l σ) := fun l => (ct_open l σ).measurableSet
  have hpt : ∀ g, T g * ctFun σ z g =
      ∑ l ∈ Λ, monomialChar l z * monomialChar l (halfPoint F n) * (ctCell l σ).indicator T g := by
    intro g
    by_cases h0 : T g = 0
    · rw [h0, zero_mul]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases h : g ∈ ctCell l σ
      · rw [Set.indicator_of_mem h, h0, mul_zero]
      · rw [Set.indicator_of_notMem h, mul_zero]
    · by_cases hc : g ∈ ctBig σ
      · obtain ⟨l, hl⟩ := id hc
        have hlg := ct_exp hl
        have hlΛ : l ∈ Λ := hlg ▸ hΛ g h0
        rw [Finset.sum_eq_single l (fun l' _ hne => ?_) (fun h => absurd hlΛ h),
          Set.indicator_of_mem hl, ctFun, Set.indicator_of_mem hc, ct_val, hlg]
        · ring
        · rw [Set.indicator_of_notMem (fun h => hne ((ct_exp h).symm.trans hlg)), mul_zero]
      · rw [ctFun, Set.indicator_of_notMem hc, mul_zero]
        refine (Finset.sum_eq_zero fun l _ => ?_).symm
        rw [Set.indicator_of_notMem (fun h => hc ⟨l, h⟩), mul_zero]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun l _ => (hTi.indicator (hm l)).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_indicator (hm l)]

end

theorem UpperTheory.ConvolutionTheory.H.constTerm :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (T : GL (Fin n) F → ℂ), T ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ → BiI F T →
      ∀ D : LaurentRing n, D ≠ 0 → (∀ z : Fin n → ℂˣ, evalAt z D ≠ 0 → ∀ f ∈ psI F z, ∫ g, T g * f g ∂μ = 0) →
      ∀ g₀ : GL (Fin n) F, ∫ g in {g | ∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n, g = u * g₀ * y}, T g ∂μ = 0 := by
  intro F _ _ _ _ n _ _ μ _ T hT _ D hD hz g₀
  classical
  obtain ⟨l₀, σ, hg₀⟩ := ct_normal g₀
  rw [ct_set hg₀]
  have hfin : (iwasawaExponent F n '' tsupport T).Finite :=
    (IsCompact.image hT.2 ct_cont).finite_of_discrete
  let Λ : Finset (Fin n → ℤ) := insert l₀ hfin.toFinset
  have hΛ : ∀ g, T g ≠ 0 → iwasawaExponent F n g ∈ Λ := fun g hg =>
    Finset.mem_insert_of_mem (hfin.mem_toFinset.2 ⟨g, subset_tsupport _ hg, rfl⟩)
  let c : (Fin n → ℤ) → ℂ := fun l => monomialChar l (halfPoint F n) * ∫ g in ctCell l σ, T g ∂μ
  let P : LaurentRing n := ∑ l ∈ Λ, AddMonoidAlgebra.single l (c l)
  have hev : ∀ z, evalAt z P = ∫ g, T g * ctFun σ z g ∂μ := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ct_int μ hT Λ hΛ σ z, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [evalAt_single]
    simp only [c]
    ring
  have hDP : D * P = 0 := eq_zero_of_forall_evalAt fun z => by
    rw [map_mul]
    by_cases h : evalAt z D = 0
    · rw [h, zero_mul]
    · rw [hev, hz z h _ (ctFun_mem σ z), mul_zero]
  have hP : P = 0 := (mul_eq_zero.1 hDP).resolve_left hD
  have hc : c l₀ = 0 := by
    have := congrArg (fun r : LaurentRing n => r.coeff l₀) hP
    simpa [P, Λ, AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, Finset.sum_ite_eq'] using this
  have hne : monomialChar l₀ (halfPoint F n) ≠ 0 := by
    rw [monomialChar_apply]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _
  exact (mul_eq_zero.1 hc).resolve_left hne
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open scoped Pointwise

private theorem conj_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (a : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, a i < a j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    torusPow F n a * g * (torusPow F n a)⁻¹ ∈ iwahori F n := by
  have he : ∀ i j, ((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) F) i j := by
    intro i j
    rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
    ring
  have hle : ∀ i j, ValuativeRel.valuation F
      (((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) := by
    intro i j
    rw [he]
    rcases lt_or_ge (a i) (a j) with hij | hij
    · rw [h i j hij, mul_zero]
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, a i - a j = d := ⟨(a i - a j).toNat, by omega⟩
      rw [hd, zpow_natCast, map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' (valuation_uniformizer_lt_one F).le d)
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  refine (mem_iwahori_iff F n).2 ⟨fun i j => (hle i j).trans (h1 i j),
    fun i j hij => (hle i j).trans_lt (h2 i j hij), fun i => ?_⟩
  rw [he, sub_self, zpow_zero, one_mul, h3]

private theorem fact {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    {k : GL (Fin n) F} (hk : k ∈ iwahori F n) :
    ∃ u ∈ unipotent F n, u ∈ iwahori F n ∧ ∃ w, k = u * w ∧
      ∀ b : Fin n → ℤ, Antitone b → (torusPow F n b)⁻¹ * w * torusPow F n b ∈ iwahori F n := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id k hk
  have hx' := Parabolic.mem_unipotentRadical.1 hx.2
  refine ⟨x, (mem_unipotent F n).2 ⟨hx'.1, fun i => by simpa using hx'.2 i i rfl⟩, hx.1, y * z, mul_assoc _ _ _,
    fun b hb => ?_⟩
  have h1 := conj_mem (-b) hz.1 fun i j hij =>
    (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j
      (lt_of_not_ge fun h => (hb h).not_gt (neg_lt_neg_iff.1 hij))
  have h2 := conj_mem (-b) hy.1 fun i j hij =>
    Parabolic.mem_levi.1 hy.2 i j (fun h => by
      have h' : i = j := h
      subst h'; exact lt_irrefl _ hij)
  rw [torusPow_neg, inv_inv] at h1 h2
  have := mul_mem h2 h1
  simpa [mul_assoc] using this

theorem UpperTheory.ConvolutionTheory.H.dcoShape :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (a : Fin n → ℤ), Antitone a →
      (∀ g, g ∈ dco F a ↔ ∃ u ∈ unipotent F n ⊓ integralGL F n, ∃ y ∈ iwahori F n, g = u * torusPow F n a * y) ∧
      (∀ b, Antitone b → ∀ g ∈ dco F a, ∀ g' ∈ dco F b, g * g' ∈ dco F (a + b)) ∧
      uFn F a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (uFn F a) := by
  intro F _ _ _ _ n a ha
  have hbi : ∀ g, ∀ y ∈ iwahori F n, (y * g ∈ dco F a ↔ g ∈ dco F a) ∧ (g * y ∈ dco F a ↔ g ∈ dco F a) := by
    have hl : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → y * g ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨y * x, mul_mem hy hx, x', hx', by group⟩
    have hr : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → g * y ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨x, hx, x' * y, mul_mem hx' hy, by group⟩
    intro g y hy
    exact ⟨⟨fun h => by simpa using hl _ _ (inv_mem hy) h, hl g y hy⟩,
      ⟨fun h => by simpa using hr _ _ (inv_mem hy) h, hr g y hy⟩⟩
  refine ⟨fun g => ⟨?_, ?_⟩, ?_, ?_, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk, y, hy, rfl⟩
    obtain ⟨u, hu, huI, w, rfl, hw⟩ := fact hk
    exact ⟨u, ⟨hu, iwahori_le_integralGL F n huI⟩, _, mul_mem (hw a ha) hy, by group⟩
  · rintro ⟨u, ⟨hu, hu'⟩, y, hy, rfl⟩
    refine ⟨u, ?_, y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_unipotent F n).1 hu
    refine (mem_iwahori_iff F n).2 ⟨fun i j => ((mem_integralGL_iff F n).1 hu').1 i j, fun i j hij => ?_, fun i => ?_⟩
    · rw [h1 hij, map_zero]; exact zero_lt_one
    · rw [h2, map_one]
  · rintro b hb g ⟨x, hx, y, hy, rfl⟩ g' ⟨x', hx', y', hy', rfl⟩
    obtain ⟨u, hu, huI, w, e, hw⟩ := fact (mul_mem hy hx')
    have h1 := conj_mem a huI fun i j hij =>
      ((mem_unipotent F n).1 hu).1 (lt_of_not_ge fun h => (ha h).not_gt hij)
    refine ⟨_, mul_mem hx h1, _, mul_mem (hw b hb) hy', ?_⟩
    rw [torusPow_add]
    calc x * torusPow F n a * y * (x' * torusPow F n b * y')
        = x * torusPow F n a * (y * x') * torusPow F n b * y' := by group
      _ = _ := by rw [e]; group
  · have e : dco F a = (iwahori F n : Set (GL (Fin n) F)) * {torusPow F n a} * (iwahori F n : Set (GL (Fin n) F)) := by
      ext g
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact Set.mul_mem_mul (Set.mul_mem_mul hx rfl) hy
      · rintro ⟨_, ⟨x, hx, _, rfl, rfl⟩, y, hy, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    refine indicator_mem_locallyConstantCompactSupport (R := ℂ) (U := dco F a) ?_ ?_ (1 : ℂ)
    · rw [e]; exact ((isCompact_iwahori F n).mul isCompact_singleton).mul (isCompact_iwahori F n)
    · rw [e]; exact (isOpen_iwahori F n).mul_left
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).1]
    · simp [uFn, h, (hbi g y hy).1]
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).2]
    · simp [uFn, h, (hbi g y hy).2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.EigBasis
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private def eigCone (n : ℕ) : AddSubmonoid (Fin n → ℤ) where
  carrier := {a | Antitone a}
  add_mem' ha hb := Antitone.add ha hb
  zero_mem' := fun _ _ _ => le_rfl

private noncomputable def eigChar {n : ℕ} (w : Fin n → ℂˣ) : Multiplicative (eigCone n) →* ℂ where
  toFun a := monomialChar (a.toAdd : Fin n → ℤ) w
  map_one' := by simp [monomialChar_zero]
  map_mul' a b := by simp [monomialChar_add]

private lemma eig_mc_ne {n : ℕ} (a : Fin n → ℤ) (w : Fin n → ℂˣ) : monomialChar a w ≠ 0 := by
  have h := monomialChar_add a (-a) w
  rw [add_neg_cancel, monomialChar_zero] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

private lemma eig_mc_single {n : ℕ} (i : Fin n) (w : Fin n → ℂˣ) :
    monomialChar (Pi.single i 1) w = w i := by
  change ∏ j, (((w j) ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) j) : ℂˣ) : ℂ) = w i
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private lemma eigChar_inj {n : ℕ} : Function.Injective (eigChar (n := n)) := by
  intro w w' h
  have H : ∀ a, Antitone a → monomialChar a w = monomialChar a w' := fun a ha =>
    DFunLike.congr_fun h (Multiplicative.ofAdd ⟨a, ha⟩)
  funext i
  let p : Fin n → ℤ := fun j => if j < i then 1 else 0
  have hp : Antitone p := by
    intro j k hjk
    simp only [p]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (lt_of_le_of_lt hjk h1) h2
    · exact zero_le_one
    · exact le_rfl
  have hq : Antitone (Pi.single i 1 + p) := by
    intro j k hjk
    simp only [p, Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  have h1 := H _ hq
  rw [monomialChar_add, monomialChar_add, H p hp, eig_mc_single, eig_mc_single] at h1
  exact Units.ext (mul_right_cancel₀ (eig_mc_ne _ _) h1)

theorem UpperTheory.ConvolutionTheory.H.eigBasis :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V], Module.finrank ℂ V ≤ n.factorial →
      ∀ θ : (Fin n → ℤ) → Module.End ℂ V, θ 0 = 1 → (∀ a b, Antitone a → Antitone b → θ (a + b) = θ a * θ b) →
      ∀ (u : V) (ℓ : Module.Dual ℂ V) (z : Fin n → ℂˣ) (c : Equiv.Perm (Fin n) → ℂ), Function.Injective z → (∀ σ, c σ ≠ 0) →
      (∀ a, Antitone a → ℓ (θ a u) = ∑ σ, c σ * monomialChar a (z ∘ σ)) →
      ∃ v : Module.Basis (Equiv.Perm (Fin n)) ℂ V, (∀ σ a, Antitone a → θ a (v σ) = monomialChar a (z ∘ σ) • v σ) ∧ (∀ σ, ℓ (v σ) = 1) ∧
        u = ∑ σ, c σ • v σ := by
  intro n V _ _ _ hdim θ h0 hadd u ℓ z c hz hc hu
  classical
  let χ : Equiv.Perm (Fin n) → Multiplicative (eigCone n) → ℂ := fun σ => eigChar (z ∘ σ)
  have hχ : ∀ σ a, χ σ a = monomialChar (a.toAdd : Fin n → ℤ) (z ∘ σ) := fun _ _ => rfl
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin n) => eigChar (z ∘ σ)) := by
    intro σ τ h
    have := eigChar_inj h
    exact Equiv.ext fun i => hz (congrFun this i)
  have hli : LinearIndependent ℂ χ :=
    (linearIndependent_monoidHom (Multiplicative (eigCone n)) ℂ).comp _ hinj
  let Φ : V →ₗ[ℂ] (Multiplicative (eigCone n) → ℂ) :=
    LinearMap.pi fun a => ℓ ∘ₗ θ (a.toAdd : Fin n → ℤ)
  have hΦ : ∀ x a, Φ x a = ℓ (θ (a.toAdd : Fin n → ℤ) x) := fun _ _ => rfl
  let L : (Equiv.Perm (Fin n) → ℂ) →ₗ[ℂ] (Multiplicative (eigCone n) → ℂ) :=
    Fintype.linearCombination ℂ (fun σ => c σ • χ σ)
  have hL : ∀ w a, L w a = ∑ σ, w σ * (c σ * χ σ a) := by
    intro w a
    simp [L, Fintype.linearCombination_apply, Finset.sum_apply]
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  have hle : Submodule.span ℂ (Set.range (flip χ)) ≤ (LinearMap.range Φ).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    refine ⟨θ (b.toAdd : Fin n → ℤ) u, ?_⟩
    funext a
    rw [hΦ, hL, ← Module.End.mul_apply, ← hadd _ _ a.toAdd.2 b.toAdd.2,
      hu (_ + _) (a.toAdd + b.toAdd).2]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [monomialChar_add]
    simp only [flip, hχ]
    ring
  have hex : ∀ σ, ∃ x, Φ x = χ σ := by
    intro σ
    have h1 : (Pi.single σ (c σ)⁻¹ : Equiv.Perm (Fin n) → ℂ) ∈ (LinearMap.range Φ).comap L :=
      hle (hspan ▸ Submodule.mem_top)
    obtain ⟨x, hx⟩ := h1
    refine ⟨x, hx.trans ?_⟩
    funext a
    rw [hL, Finset.sum_eq_single σ]
    · rw [Pi.single_eq_same, ← mul_assoc, inv_mul_cancel₀ (hc σ), one_mul]
    · intro τ _ hτ
      simp [Pi.single_eq_of_ne hτ]
    · simp
  choose v hv using hex
  have hlc : LinearIndependent ℂ (Φ ∘ v) := by
    have : Φ ∘ v = χ := funext hv
    rw [this]; exact hli
  have hlv : LinearIndependent ℂ v := LinearIndependent.of_comp Φ hlc
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Module.finrank ℂ V := by
    refine le_antisymm hlv.fintype_card_le_finrank ?_
    rw [Fintype.card_perm, Fintype.card_fin]
    exact hdim
  let B := basisOfLinearIndependentOfCardEqFinrank hlv hcard
  have hB : ∀ σ, B σ = v σ := fun σ => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hΦinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← B.sum_repr x] at hx ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hB] at hx
    have := Fintype.linearIndependent_iff.1 hlc (fun σ => B.repr x σ) hx
    simp [this]
  refine ⟨B, fun σ a ha => ?_, fun σ => ?_, ?_⟩
  · apply hΦinj
    funext b
    rw [hB, map_smul, hv, hΦ, ← Module.End.mul_apply, ← hadd _ _ b.toAdd.2 ha]
    have := congrFun (hv σ) (Multiplicative.ofAdd ⟨_, Antitone.add b.toAdd.2 ha⟩)
    rw [hΦ, hχ] at this
    refine this.trans ?_
    change monomialChar (_ + a) _ = _
    rw [monomialChar_add, Pi.smul_apply, hχ, smul_eq_mul, mul_comm]
  · have := congrFun (hv σ) 1
    rw [hΦ, hχ] at this
    simpa [h0, monomialChar_zero, hB] using this
  · apply hΦinj
    funext a
    rw [hΦ, hu _ a.toAdd.2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hB, hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hχ]
end

