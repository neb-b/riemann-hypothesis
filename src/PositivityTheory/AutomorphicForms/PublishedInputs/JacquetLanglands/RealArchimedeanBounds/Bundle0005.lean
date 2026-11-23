module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.MapScalarCenter
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalarMap

theorem central_of_map {K L : Type} [Field K] [Field L] (f : K →+* L) {g : GL (Fin 2) K}
    (h : Matrix.GeneralLinearGroup.map f g ∈ Subgroup.center (GL (Fin 2) L)) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro δ
  have e := h (Matrix.GeneralLinearGroup.map f δ)
  rw [← map_mul, ← map_mul] at e
  apply Units.ext
  exact Matrix.map_injective f.injective (congrArg Units.val e)

theorem map_scalar_center {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∈ Subgroup.center (GL (Fin 2) S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end UpperTheory.Esk.CentralScalarMap

namespace UpperTheory.Esk

open CentralScalarMap in
theorem dTwo : AMem → DTwo := by
  intro hA F _ _ _ c χ ⟨u, hu, hu2⟩ ω S hS hfin
  obtain ⟨-, -, -, hH, -⟩ := hA F
  have hc0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hc0 (p := 2) ?_⟩
  intro p hp hd
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := S) p hd
  set g : GL (Fin 2) F := (γ : PG F).out with hg
  have hmk : ((g : PG F)) = (γ : PG F) := QuotientGroup.out_eq' _
  have hgp : g ^ p ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← Subgroup.coe_pow, ← hγ, pow_orderOf_eq_one,
      Subgroup.coe_one]
  have hst : (γ : PG F) • ω = ω := hS γ.2
  obtain ⟨x, hx⟩ : ∃ x : GF F, ((x : GF F ⧸ Hc c) : (mkDat c χ).Om) = ω := QuotientGroup.mk_surjective ω
  have h1 : ((jF F g * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := by
    rw [← hmk, ← hx] at hst
    exact hst
  have h2 : x⁻¹ * (jF F g * x) ∈ Hc c := QuotientGroup.eq.1 h1.symm
  obtain ⟨k, hk, z, hkz⟩ := (hH c _).1 h2
  obtain ⟨z0, hz0⟩ := jF_center hgp
  have hzc : ∀ z, zc F z ∈ Subgroup.center (GF F) := zc_center
  have hyp : (x⁻¹ * (jF F g * x)) ^ p = zc F z0 := by
    have := conj_pow (a := x⁻¹) (b := jF F g) (i := p)
    rw [inv_inv] at this
    rw [← mul_assoc, this, ← map_pow, hz0, Subgroup.mem_center_iff.1 (hzc _) x⁻¹, inv_mul_cancel_right]
  have hkp : k ^ p = zc F (z0 * (z ^ p)⁻¹) := by
    have e1 : (k * zc F z) ^ p = k ^ p * zc F z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.1 (hzc z) k) p
    rw [map_mul, map_inv, map_pow, ← hyp, hkz, e1, mul_inv_cancel_right]
  set P := Matrix.GeneralLinearGroup.map (n := Fin 2) (pLoc F u) with hP
  have hPz : ∀ z, P (zc F z) ∈ Subgroup.center _ := fun z => map_scalar_center _ z
  have hku : P k ∈ K1 u (c u) := Subgroup.mem_iInf.1 hk u
  have hkc := locTwo F u (c u) hu hu2 _ hku p (hp.odd_of_ne_two hne) (by rw [← map_pow, hkp]; exact hPz _)
  have hc2 : P (x⁻¹ * (jF F g * x)) ∈ Subgroup.center _ := by
    rw [hkz, map_mul]; exact mul_mem hkc (hPz z)
  have hc3 : P (jF F g) ∈ Subgroup.center _ := by
    have := (Subgroup.normal_of_characteristic _).conj_mem _ hc2 (P x)
    simpa [mul_assoc] using this
  have hcen : g ∈ Subgroup.center (GL (Fin 2) F) :=
    central_of_map ((pLoc F u).comp (algebraMap F (Af F))) hc3
  have h1' : (γ : PG F) = 1 := by
    rw [← hmk]; exact (QuotientGroup.eq_one_iff _).2 hcen
  have : γ = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hγ
  exact hp.one_lt.ne hγ

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.PlaceEq
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.BoxMapsToLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.norm_embedding_of_isReal _ t).symm

lemma injOn (R : ℝ) : Set.InjOn (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R} := by
  intro t ht t' ht' h
  by_contra hne
  let a : 𝓞 F := ⟨t - t', ht.1.sub ht'.1⟩
  have ha : a ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((a : 𝓞 F) : F) = 0 := by rw [h0]; rfl
    exact sub_eq_zero.1 h1
  have hlt : ∀ v : InfinitePlace F, v (a : F) < 1 := by
    intro v
    have hv := congrFun h v
    simp only at hv
    rw [place_eq]
    show |sg v (t - t')| < 1
    rw [map_sub]
    exact Int.abs_sub_lt_one_of_floor_eq_floor hv
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

open Classical in
lemma mapsTo (R : ℝ) : Set.MapsTo (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R}
    ((Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ : Finset _) : Set _) := by
  intro t ht
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro v
  have h1 := ht.2 v
  rw [place_eq, abs_le] at h1
  have hc : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [h1.1]
  · have h2 : ((⌊sg v t⌋ : ℤ) : ℝ) ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.floor_le (sg v t), h1.2]
    exact_mod_cast h2

end UpperTheory.Esk.BoxMapsToLemmas

open Classical in
theorem UpperTheory.Esk.dBox : UpperTheory.Esk.DBox := by
  intro F _ _ _
  refine ⟨5 ^ Fintype.card (InfinitePlace F), fun R hR => ?_⟩
  set d := Fintype.card (InfinitePlace F)
  set T := (Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊)
  refine ⟨Set.Finite.of_injOn (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : T.card = (2 * ⌈R⌉₊ + 1) ^ d := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  have h3 : ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * max 1 R := by
    have := Nat.ceil_lt_add_one hR
    have hm1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
    have hmR : R ≤ max 1 R := le_max_right _ _
    push_cast
    linarith
  have h4 : (max 1 R) ^ d ≤ 1 + R ^ d := by
    rcases le_total R 1 with h | h
    · rw [max_eq_left h, one_pow]
      linarith [pow_nonneg hR d]
    · rw [max_eq_right h]
      linarith [zero_le_one' ℝ]
  calc (_ : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h1
    _ = ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ^ d := by rw [h2]; push_cast; ring
    _ ≤ (5 * max 1 R) ^ d := pow_le_pow_left₀ (by positivity) h3 _
    _ = 5 ^ d * (max 1 R) ^ d := mul_pow _ _ _
    _ ≤ 5 ^ d * (1 + R ^ d) := mul_le_mul_of_nonneg_left h4 (by positivity)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFMul
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightMultiplicativityAlt

theorem rowF_mul {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x y : GF F) :
    rowF s (x * y) = rowF s x ᵥ* y.val := by
  simp only [rowF, Units.val_mul, Matrix.vecMul_vecMul]

theorem row_mul {F : Type} [Field F] [NumberField F] (t : Af F) (k : GF F) (M : Matrix (Fin 2) (Fin 2) (Af F)) :
    (fun i => t * k.val 1 i) ᵥ* M = fun i => t * (k.val * M) 1 i := by
  ext i
  simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_assoc]

theorem zc_val {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    (zc F z).val = Matrix.scalar (Fin 2) (z : Af F) := rfl

theorem det_zc {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    Matrix.GeneralLinearGroup.det (zc F z) = z * z := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, zc_val, pow_two]

theorem part1 (hM : AMem) (hR : ARow) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ)
    (s : Fin 2 → F) (hs : s ≠ 0) (x h : GF F) (hh : h ∈ Hc c) :
    absF (Matrix.GeneralLinearGroup.det (x * h)) / nF s (x * h) ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 := by
  obtain ⟨-, -, hKc, hH, hdet, -⟩ := hM F
  obtain ⟨hA1, hA2, hA3, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨k', hk', z, rfl⟩ := (hH c h).1 hh
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  have hk'0 : k' ∈ K0 F := hKc c hk'
  have e1 : nF s x = absF t := (hR F s x).2 t k hk ht
  have hx : rowF s x = fun i => (t : Af F) * k.val 1 i := funext ht
  have e2 : nF s (x * (k' * zc F z)) = absF (t * z) := by
    refine (hR F s _).2 (t * z) (k * k') (mul_mem hk hk'0) fun i => ?_
    rw [rowF_mul, hx, row_mul]
    simp only [Units.val_mul, zc_val, ← Matrix.mul_assoc, Matrix.scalar_apply, Matrix.mul_diagonal]
    ring
  have e3 : absF (Matrix.GeneralLinearGroup.det k') = 1 := hA3 _ fun w => (hdet k' hk'0 w).1
  rw [e1, e2, map_mul, map_mul, det_zc]
  simp only [hA2, e3]
  have := (hA1 t).ne'
  have := (hA1 z).ne'
  field_simp

theorem part2 (hM : AMem) (hR : ARow) (hMo : AMono) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (a : GF F) : ∃ C : ℝ, ∀ s : Fin 2 → F, s ≠ 0 → ∀ x : GF F,
      absF (Matrix.GeneralLinearGroup.det (x * a)) / nF s (x * a) ^ 2 ≤
        C * (absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2) := by
  obtain ⟨hK, hO, -, -, hdet, -, hN, -⟩ := hM F
  obtain ⟨hA1, hA2, -, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨N, hN0, hNa⟩ := hN a⁻¹
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨n, hn⟩ : ∃ n : (Af F)ˣ, (n : Af F) = (N : Af F) :=
    ⟨ratU F (Units.mk0 (N : F) hNF), by simp [ratU]⟩
  refine ⟨absF (Matrix.GeneralLinearGroup.det a) / absF n ^ 2, fun s hs x => ?_⟩
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s (x * a)).1 hs
  rw [(hR F s x).2 t k hk ht, (hR F s (x * a)).2 t' k' hk' ht']
  have key : absF (n * t) ≤ absF t' := by
    refine hMo F _ _ fun w => ?_
    have hrow : rowF s x = rowF s (x * a) ᵥ* (a⁻¹ : GF F).val := by
      rw [← rowF_mul, mul_inv_cancel_right]
    have hint : ∀ i j, Valued.v (pLoc F w (k'.val i j)) ≤ 1 := fun i j =>
      (hO _).1 (((hK k').1 hk').1 i j) w
    have hint2 : ∀ i j, Valued.v (pLoc F w ((N : Af F) * (a⁻¹ : GF F).val i j)) ≤ 1 := fun i j =>
      (hO _).1 (hNa i j) w
    have heq : ∀ i, (n : Af F) * ((t : Af F) * k.val 1 i) = (t' : Af F) * (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i)) := by
      intro i
      have h1 := congrFun hrow i
      rw [← ht i, hn, h1]
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ht']
      ring
    have hS : ∀ i, Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) ≤ 1 := by
      intro i
      rw [map_add (f := _)]
      refine Valuation.map_add_le _ ?_ ?_ <;> rw [map_mul, map_mul] <;> exact mul_le_one' (hint _ _) (hint2 _ _)
    have hmax := (hdet k hk w).2
    obtain ⟨i, hi⟩ : ∃ i, Valued.v (pLoc F w (k.val 1 i)) = 1 := by
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h
      · exact ⟨0, h.symm.trans hmax⟩
      · exact ⟨1, h.symm.trans hmax⟩
    calc Valued.v (pLoc F w ((n * t : (Af F)ˣ) : Af F))
        = Valued.v (pLoc F w ((n : Af F) * ((t : Af F) * k.val 1 i))) := by
          simp only [Units.val_mul, map_mul, hi, mul_one]
      _ = Valued.v (pLoc F w (t' : Af F)) * Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
          k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) := by
          rw [heq i, map_mul (pLoc F w), map_mul Valued.v]
      _ ≤ Valued.v (pLoc F w (t' : Af F)) * 1 := mul_le_mul' le_rfl (hS i)
      _ = _ := mul_one _
  rw [map_mul, hA2]
  have key2 : absF n * absF t ≤ absF t' := by rw [← hA2]; exact key
  have p1 := hA1 n
  have p2 := hA1 t
  have p3 := hA1 t'
  have p4 := hA1 (Matrix.GeneralLinearGroup.det x)
  have p5 := hA1 (Matrix.GeneralLinearGroup.det a)
  calc absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / absF t' ^ 2
      ≤ absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / (absF n * absF t) ^ 2 :=
        div_le_div_of_nonneg_left (mul_pos p4 p5).le (pow_pos (mul_pos p1 p2) 2)
          (pow_le_pow_left₀ (mul_pos p1 p2).le key2 2)
    _ = _ := by
      field_simp

end UpperTheory.Esk.HeightMultiplicativityAlt

theorem UpperTheory.Esk.dMul : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.DMul := by
  intro hM _ hMo hR F _ _ _ c _ χ
  exact ⟨fun s hs x h hh => UpperTheory.Esk.HeightMultiplicativityAlt.part1 hM hR F c s hs x h hh,
    fun a => UpperTheory.Esk.HeightMultiplicativityAlt.part2 hM hR hMo F a⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFSmul
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightFunctionLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nF_eq (s : Fin 2 → F) (x : GF F) :
    nF s x = ∏ᶠ w : Pl F, max ‖pLoc F w (rowF s x 0)‖ ‖pLoc F w (rowF s x 1)‖ := rfl

theorem rowF_jF (s : Fin 2 → F) (γ : GL (Fin 2) F) (x : GF F) :
    rowF s (jF F γ * x) = rowF (s ᵥ* γ.val) x := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((s ᵥ* γ.val) i)) =
      (fun i => algebraMap F (Af F) (s i)) ᵥ* (jF F γ).val := by
    funext i
    exact RingHom.map_vecMul (algebraMap F (Af F)) γ.val s i
  rw [h, Units.val_mul, Matrix.vecMul_vecMul]

theorem rowF_smul (s : Fin 2 → F) (a : F) (x : GF F) (i : Fin 2) :
    rowF (a • s) x i = algebraMap F (Af F) a * rowF s x i := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((a • s) i)) = algebraMap F (Af F) a • (fun i => algebraMap F (Af F) (s i)) := by
    funext i
    simp [map_mul]
  rw [h, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]

theorem det_jF (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F γ) = ratU F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  change (γ.val.map (algebraMap F (Af F))).det = algebraMap F (Af F) γ.val.det
  exact (RingHom.map_det (algebraMap F (Af F)) γ.val).symm

variable [IsTotallyReal F]

theorem nF_pos (hR : ARow) {s : Fin 2 → F} (hs : s ≠ 0) (x : GF F) : 0 < nF s x := by
  obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
  rw [(hR F s x).2 t k hk h]
  exact (Hm.absf F).1 t

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem prod_rat (a : Fˣ) : (∏ v, |sg v (a : F)|) * absF (ratU F a) = 1 := by
  have := (Hm.absf F).2.2.2 a
  simp only [reAt_eq] at this
  exact this

end UpperTheory.Esk.HeightFunctionLemmas

open UpperTheory.Esk.HeightFunctionLemmas in
theorem UpperTheory.Esk.dHt : UpperTheory.Esk.ARow → UpperTheory.Esk.DHt := by
  intro hR F _ _ _ c _ χ
  refine ⟨fun s hs x => ?_, fun s hs γ x => ?_, fun s hs a ha x => ?_⟩
  · change 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2
    exact div_pos ((Hm.absf F).1 _) (pow_pos (nF_pos hR hs x) 2)
  · change absF (Matrix.GeneralLinearGroup.det (jF F γ * x)) / nF s (jF F γ * x) ^ 2 * ∏ v, |sg v γ.val.det| =
      absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2
    have hP := prod_rat (Matrix.GeneralLinearGroup.det γ)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hP
    rw [map_mul, det_jF, (Hm.absf F).2.1, nF_eq s, rowF_jF, ← nF_eq]
    calc absF (ratU F (Matrix.GeneralLinearGroup.det γ)) * absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2 *
          ∏ v, |sg v γ.val.det|
        = ((∏ v, |sg v γ.val.det|) * absF (ratU F (Matrix.GeneralLinearGroup.det γ))) *
          (absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2) := by ring
      _ = _ := by rw [hP, one_mul]
  · change absF (Matrix.GeneralLinearGroup.det x) / nF (a • s) x ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * ∏ v, sg v a ^ 2
    obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
    have h1 := (hR F s x).2 t k hk h
    have h2 : nF (a • s) x = absF (ratU F (Units.mk0 a ha)) * nF s x := by
      rw [(hR F (a • s) x).2 (ratU F (Units.mk0 a ha) * t) k hk (fun i => by
        rw [rowF_smul, h i, Units.val_mul, mul_assoc]; rfl), (Hm.absf F).2.1, h1]
    have hP := prod_rat (Units.mk0 a ha)
    simp only [Units.val_mk0] at hP
    have hA := (Hm.absf F).1 (ratU F (Units.mk0 a ha))
    have hN := nF_pos hR hs x
    have hsq : ∏ v, sg v a ^ 2 = (∏ v, |sg v a|) ^ 2 := by
      rw [← Finset.prod_pow]; simp [sq_abs]
    rw [h2, hsq, eq_inv_of_mul_eq_one_left hP]
    field_simp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowMul
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.PrimitiveVectorLemmas

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem exists_row (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL (Fin 2) F, ∀ j, γ.val 1 j = s j := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := by
      intro h1; apply hs; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro j; fin_cases j <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro j; fin_cases j <;> rfl

theorem row_mul (s : Fin 2 → F) (γ : GL (Fin 2) F) (hγ : ∀ j, γ.val 1 j = s j) (x : GF F) (i : Fin 2) :
    rowF s x i = (jF F γ * x).val 1 i := by
  simp [rowF, jF, Matrix.mul_apply, Matrix.vecMul, dotProduct, hγ]

theorem row_zak (d a : (Af F)ˣ) (u : Af F) (k : GF F) (i : Fin 2) :
    (zc F d * aff a u * k).val 1 i = (d : Af F) * k.val 1 i := by
  simp [zc, aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply]

end UpperTheory.Esk.PrimitiveVectorLemmas

theorem UpperTheory.Esk.aRow : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ARow := by
  intro hM hI F _ _ s x
  refine ⟨fun hs => ?_, fun t k hk hrow => ?_⟩
  · obtain ⟨γ, hγ⟩ := UpperTheory.Esk.PrimitiveVectorLemmas.exists_row s hs
    obtain ⟨d, a, u, k, hk, he⟩ := hI F (UpperTheory.Esk.jF F γ * x)
    refine ⟨d, k, hk, fun i => ?_⟩
    rw [UpperTheory.Esk.PrimitiveVectorLemmas.row_mul s γ hγ x i, he, UpperTheory.Esk.PrimitiveVectorLemmas.row_zak]
  · obtain ⟨-, -, -, -, h5, -⟩ := hM F
    have key : ∀ w : Pl F, max ‖pLoc F w (k.val 1 0)‖ ‖pLoc F w (k.val 1 1)‖ = 1 := by
      intro w
      have h := (h5 k hk w).2
      refine le_antisymm (max_le (Valued.toNormedField.norm_le_one_iff.2 ((le_max_left _ _).trans h.le))
        (Valued.toNormedField.norm_le_one_iff.2 ((le_max_right _ _).trans h.le))) ?_
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with hh | hh <;> rw [hh] at h
      · exact le_max_of_le_left (Valued.toNormedField.one_le_norm_iff.2 h.ge)
      · exact le_max_of_le_right (Valued.toNormedField.one_le_norm_iff.2 h.ge)
    have hw : ∀ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ =
        ‖pLoc F w (t : Af F)‖ := by
      intro w
      rw [hrow 0, hrow 1, map_mul, map_mul, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg _), key w, mul_one]
    show ∏ᶠ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ = ∏ᶠ w : Pl F, ‖pLoc F w (t : Af F)‖
    exact finprod_congr hw
end
end

