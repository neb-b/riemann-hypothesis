module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
public import Development.AutomorphicArithmetic.QuadraticCharacters.GaussRoot

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ConductorBoundsOfIsChiField
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem lcm_le_mul' {a b c d : ℕ} (hc : a ≤ c) (hd : b ≤ d) (ha : 0 < a) (hb : 0 < b) :
    Nat.lcm a b ≤ c * d := by
  exact (Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))).trans
    (Nat.mul_le_mul hc hd)

private theorem descend {E : Type} [Field E] [NumberField E] {N L : ℕ} [NeZero N]
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N) (hL : L ∣ N)
    (H : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      a ≡ 1 [MOD L] → ∀ x : E, τ (j x) = j x) :
    Nonempty (E →ₐ[ℚ] CyclotomicField L ℚ) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact hN0 (Nat.eq_zero_of_zero_dvd hL)
  haveI : NeZero L := ⟨hL0⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN0⟩
  haveI : NeZero ((L : ℕ) : ℚ) := ⟨by exact_mod_cast hL0⟩
  obtain ⟨M, hNLM⟩ := hL
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [hNLM, mul_zero])
  have hMdvd : M ∣ N := ⟨L, by rw [hNLM, mul_comm]⟩
  have hk : N / M = L := by
    rw [hNLM, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM0)]
  have hη : IsPrimitiveRoot (ζ ^ M) L := by
    have := hζ.pow_of_dvd hM0 hMdvd
    rwa [hk] at this
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsCyclotomicExtension {L} ℚ (CyclotomicField L ℚ) :=
    CyclotomicField.isCyclotomicExtension L ℚ
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.finiteDimensional {N} ℚ _
  let F : IntermediateField ℚ (CyclotomicField N ℚ) := IntermediateField.adjoin ℚ {ζ ^ M}
  haveI : IsCyclotomicExtension {L} ℚ F := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hmem : ∀ x : E, j x ∈ F := by
    intro x
    rw [← IsGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hτη : τ (ζ ^ M) = ζ ^ M := hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    have hpow : (τ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, hζa⟩ := hζ.eq_pow_of_pow_eq_one hpow
    apply H τ a hζa.symm
    have h1 : ζ ^ (a * M) = ζ ^ (1 * M) := by
      rw [pow_mul, hζa, ← map_pow, hτη, one_mul]
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have h2 : a * M ≡ 1 * M [MOD N] := by
      unfold Nat.ModEq
      apply hζ.pow_inj (Nat.mod_lt _ hNpos) (Nat.mod_lt _ hNpos)
      have e1 := pow_mod_orderOf ζ (a * M)
      have e2 := pow_mod_orderOf ζ (1 * M)
      rw [← hζ.eq_orderOf] at e1 e2
      rw [e1, e2, h1]
    rw [hNLM] at h2
    exact Nat.ModEq.mul_right_cancel' hM0 h2
  exact ⟨(IsCyclotomicExtension.algEquiv {L} ℚ F (CyclotomicField L ℚ)).toAlgHom.comp
    (j.codRestrict F.toSubalgebra hmem)⟩

private theorem finrank_le {E : Type} [Field E] [NumberField E] {c : ℕ} (hc : 0 < c)
    (j : E →ₐ[ℚ] CyclotomicField c ℚ) : Module.finrank ℚ E ≤ c := by
  haveI : NeZero c := ⟨hc.ne'⟩
  haveI : NeZero ((c : ℕ) : ℚ) := ⟨by exact_mod_cast hc.ne'⟩
  haveI : IsCyclotomicExtension {c} ℚ (CyclotomicField c ℚ) := CyclotomicField.isCyclotomicExtension c ℚ
  haveI : FiniteDimensional ℚ (CyclotomicField c ℚ) := IsCyclotomicExtension.finiteDimensional {c} ℚ _
  calc Module.finrank ℚ E ≤ Module.finrank ℚ (CyclotomicField c ℚ) :=
        LinearMap.finrank_le_finrank_of_injective (f := j.toLinearMap) j.toRingHom.injective
    _ = c.totient := IsCyclotomicExtension.finrank _ (Polynomial.cyclotomic.irreducible_rat hc)
    _ ≤ c := Nat.totient_le c

theorem UpperTheory.V.conductor_bounds_of_isChiField :
    ∀ (ψ : PChar) (e q d : ℕ), 0 < q → 0 < d → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
      1 ≤ condF E ∧ condF E ≤ 2 ^ (e + 2) * ψ.N * q * d ∧ Module.finrank ℚ E ≤ condF E := by
  intro ψ e q d hq hd E _ _ hE
  obtain ⟨N, hNZ, j, ζ, h2, hψ, hqN, hdN, hζ, hτ⟩ := hE
  haveI := hNZ
  haveI := ψ.ne
  have hψpos : 0 < ψ.N := NeZero.pos ψ.N
  have hApos : 0 < 2 ^ (e + 2) := pow_pos two_pos _
  have hLN : Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d ∣ N :=
    Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h2 hψ) hqN) hdN
  have d1 : 2 ^ (e + 2) ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  have dψ : ψ.N ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  have dq : q ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)
  have dd : d ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d := Nat.dvd_lcm_right _ _
  have jac : ∀ (a m : ℕ), a ≡ 1 [MOD m] → jacobiSym (a : ℤ) m = 1 := by
    intro a m h
    have hm : (a : ℤ) % (m : ℤ) = 1 % (m : ℤ) := by
      unfold Nat.ModEq at h
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) h
    rw [jacobiSym.mod_left, hm, ← jacobiSym.mod_left, jacobiSym.one_left]
  have hemb := descend j hζ hLN (by
    intro τ a hτa ha x
    refine ((hτ τ a hτa).mpr ⟨Or.inl (ha.of_dvd d1), ?_, jac a q (ha.of_dvd dq), jac a d (ha.of_dvd dd)⟩) x
    show ψ.χ (a : ZMod ψ.N) = 1
    have h' : ((a : ℕ) : ZMod ψ.N) = ((1 : ℕ) : ZMod ψ.N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (ha.of_dvd dψ)
    rw [h', Nat.cast_one, MulChar.map_one])
  have hLpos : 0 < Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    Nat.pos_of_dvd_of_pos hLN (NeZero.pos N)
  unfold condF
  have hset : Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d ∈
      {N | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} := ⟨hLpos, hemb⟩
  have hmem := Nat.sInf_mem ⟨_, hset⟩
  refine ⟨hmem.1, (Nat.sInf_le hset).trans ?_, ?_⟩
  · have hY := lcm_le_mul' (le_refl (2 ^ (e + 2))) (le_refl ψ.N) hApos hψpos
    have hX := lcm_le_mul' hY (le_refl q) (Nat.lcm_pos hApos hψpos) hq
    exact lcm_le_mul' hX (le_refl d) (Nat.lcm_pos (Nat.lcm_pos hApos hψpos) hq) hd
  · obtain ⟨hpos, ⟨j'⟩⟩ := hmem
    exact finrank_le hpos j'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ErrorTermsLeSqrtExpRpow
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.error_terms_le_sqrt_exp_rpow :
    ∀ eps K C : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ u : ℝ, 1 ≤ u → Real.log u ≤ 2 * x ^ (eps / 4) →
      Real.exp (x ^ (4 * eps / 5)) * Real.log 2 + K * Real.exp (8 * x ^ (eps / 4)) + (u ^ C + C * Real.exp (x ^ (4 * eps / 5))) ≤
        Real.sqrt (Real.exp (x ^ eps)) := by
  intro eps K C heps
  set N : ℝ := Real.log 2 + |C| + |K| + 1 with hN
  set D : ℝ := 9 + 2 * |C| with hD
  set T : ℝ := 2 * (D + Real.log N + 1) with hTdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : 1 ≤ N := by
    have := abs_nonneg C
    have := abs_nonneg K
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hD0 : 9 ≤ D := by
    have := abs_nonneg C
    linarith
  have hT : 0 ≤ T := by linarith
  refine ⟨max 1 (T ^ (5 / eps)), fun x hx u hu hlog => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  set a := x ^ (eps / 4) with ha
  set b := x ^ (4 * eps / 5) with hb
  set s := x ^ (eps / 5) with hs
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb1 : 1 ≤ b := Real.one_le_rpow hx1 (by positivity)
  have ha0 : 0 ≤ a := by positivity
  have hc : x ^ eps = b * s := by
    rw [hb, hs, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hsT : T ≤ s := by
    have h1 : T = (T ^ (5 / eps)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hT]
      have : 5 / eps * (eps / 5) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [h1, hs]
    exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) (by positivity)
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hupos : 0 < u := by linarith
  have huC : u ^ C ≤ Real.exp (D * b) := by
    rw [Real.rpow_def_of_pos hupos]
    apply Real.exp_le_exp.mpr
    have e1 : Real.log u * C ≤ Real.log u * |C| :=
      mul_le_mul_of_nonneg_left (le_abs_self C) hlogu
    have e2 : Real.log u * |C| ≤ (2 * a) * |C| :=
      mul_le_mul_of_nonneg_right hlog (abs_nonneg C)
    have e3 : (2 * a) * |C| ≤ (2 * b) * |C| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg C)
    have e4 : (2 * b) * |C| ≤ D * b := by
      rw [hD]
      nlinarith [abs_nonneg C]
    linarith
  have hK : K * Real.exp (8 * a) ≤ |K| * Real.exp (D * b) := by
    have : K * Real.exp (8 * a) ≤ |K| * Real.exp (8 * a) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
    have h2 : Real.exp (8 * a) ≤ Real.exp (D * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    linarith
  have hE : Real.exp b ≤ Real.exp (D * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hCE : C * Real.exp b ≤ |C| * Real.exp (D * b) := by
    have : C * Real.exp b ≤ |C| * Real.exp b :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    have h3 := mul_le_mul_of_nonneg_left hE (abs_nonneg C)
    linarith
  have hL2 : Real.exp b * Real.log 2 ≤ Real.exp (D * b) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hE hl2.le
  have hsum : Real.exp b * Real.log 2 + K * Real.exp (8 * a) + (u ^ C + C * Real.exp b)
      ≤ N * Real.exp (D * b) := by
    rw [hN]
    nlinarith
  have hfin : N * Real.exp (D * b) ≤ Real.exp (x ^ eps / 2) := by
    rw [← Real.exp_log (by linarith : (0:ℝ) < N), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hc]
    have : b * (D + Real.log N + 1) ≤ b * s / 2 := by
      have := mul_le_mul_of_nonneg_left hsT (by linarith : (0:ℝ) ≤ b)
      rw [hTdef] at this
      linarith
    nlinarith
  rw [Real.exp_half] at hfin
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ExistsNumberFieldIsAbFieldFinrankEqDeg
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.exists_numberField_isAbField_finrank_eq_deg :
    ∀ A : AbF, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsAbField A L ∧ Module.finrank ℚ L = A.deg := by
  intro A
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : NeZero ((A.m : ℚ)) := ⟨by exact_mod_cast A.pos.ne'⟩
  haveI hcyc : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
    CyclotomicField.isCyclotomicExtension A.m ℚ
  haveI : IsGalois ℚ (CyclotomicField A.m ℚ) :=
    IsCyclotomicExtension.isGalois {A.m} ℚ (CyclotomicField A.m ℚ)
  have hirr := Polynomial.cyclotomic.irreducible_rat A.pos
  let e := IsCyclotomicExtension.autEquivPow (CyclotomicField A.m ℚ) hirr
  let G : Subgroup Gal(CyclotomicField A.m ℚ/ℚ) := A.H.comap e.toMonoidHom
  let F := IntermediateField.fixedField G
  refine ⟨F, inferInstance, inferInstance, ?_, ?_⟩
  · have hζ := IsCyclotomicExtension.zeta_spec A.m ℚ (CyclotomicField A.m ℚ)
    refine ⟨A.m, inferInstance, F.val, IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ),
      dvd_rfl, hζ, ?_⟩
    intro τ a hτ
    have hspec := IsPrimitiveRoot.autToPow_spec ℚ hζ τ
    have he : ((e τ : (ZMod A.m)ˣ) : ZMod A.m) = a := by
      have h1 : IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ) ^ ((e τ : (ZMod A.m)ˣ) : ZMod A.m).val
          = IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ) ^ a := by
        rw [← hτ, ← hspec]
        rfl
      have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζ.pow_eq_one⟩
      rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
      rw [← ZMod.natCast_zmod_val ((e τ : (ZMod A.m)ˣ) : ZMod A.m)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    have hfix : (∀ x : F, τ (F.val x) = F.val x) ↔ τ ∈ G := by
      rw [← IntermediateField.fixingSubgroup_fixedField G, IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hker : τ ∈ G ↔ A.ker a := by
      rw [Subgroup.mem_comap]
      constructor
      · intro h
        exact ⟨e τ, h, he⟩
      · rintro ⟨u, hu, hua⟩
        have hue : u = e τ := Units.ext (hua.trans he.symm)
        have hmem : e τ ∈ A.H := hue ▸ hu
        exact hmem
    exact hfix.trans hker
  · have h1 := Module.finrank_mul_finrank ℚ F (CyclotomicField A.m ℚ)
    rw [IntermediateField.finrank_fixedField_eq_card,
      ← IsGalois.card_aut_eq_finrank ℚ (CyclotomicField A.m ℚ),
      ← Subgroup.index_mul_card G] at h1
    have hpos : 0 < Nat.card G := Nat.card_pos
    have h2 : Module.finrank ℚ F = G.index := Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h2]
    exact Subgroup.index_comap_of_surjective _ e.surjective
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.IsCMFieldOfIsChiField
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.isCMField_of_isChiField :
    ∀ (ψ : PChar) (e q d : ℕ), q.Prime → q % 4 = 3 → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E → IsCMField E := by
  intro ψ e q d hq hq4 E _ _ hE
  obtain ⟨N, hN, j, ζ, -, -, hqN, -, hζ, hτ⟩ := hE
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.out⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.of_algHom j
  have hζq : IsPrimitiveRoot (ζ ^ (N / q)) q :=
    hζ.pow (NeZero.pos N) (Nat.div_mul_cancel hqN).symm
  obtain ⟨G, hG2, hGσ⟩ := HostParam.SlopeTestRemainingChoices.GaussRoot.exists_gauss hq4 hζq
  have hGL : G ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτL
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτL
    have hfix : ∀ x : E, τ (j x) = j x := fun x => hτL _ (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    obtain ⟨-, -, hjq, -⟩ := (hτ τ a ha.symm).1 hfix
    have hprim : IsPrimitiveRoot (ζ ^ a) N := by
      rw [ha]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime q :=
      Nat.Coprime.coprime_dvd_right hqN ((hζ.pow_iff_coprime (NeZero.pos N) a).1 hprim)
    have hquad : quadraticChar (ZMod q) (a : ZMod q) = 1 := by
      have h := jacobiSym.legendreSym.to_jacobiSym q (a : ℤ)
      rw [hjq] at h
      unfold legendreSym at h
      rw [Int.cast_natCast] at h
      exact h
    have h := hGσ (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ) a hcop (by
      rw [RingHom.coe_coe, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm])
    rw [hquad] at h
    simpa using h
  obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hGL
  have hx2 : x ^ 2 = -(q : E) := by
    apply j.injective
    change j (x ^ 2) = j (-(q : E))
    rw [map_pow, hx, hG2, map_neg, map_natCast]
  haveI : IsTotallyComplex E := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
      ComplexEmbedding.isReal_iff]
    intro hr
    have hc := RingHom.congr_fun hr x
    rw [ComplexEmbedding.conjugate_coe_eq] at hc
    have him : (w.embedding x).im = 0 := Complex.conj_eq_iff_im.1 hc
    have hz2 : (w.embedding x) ^ 2 = -(q : ℂ) := by
      rw [← map_pow, hx2, map_neg, map_natCast]
    have hre := congrArg Complex.re hz2
    simp [sq, him] at hre
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq.pos
    nlinarith [mul_self_nonneg (w.embedding x).re]⟩
  exact NumberField.IsCMField.of_isAbelianGalois E
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.LogConductorMulHeightLeOfPageN
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.log_conductor_mul_height_le_of_pageN :
    ∀ (eps Ct : ℝ) (m : ℕ), 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ N t e q d : ℕ, 1 ≤ N → N ≤ 2 ^ (e + 2) * m * q * d →
      PageN eps x e → 1 ≤ t → (t : ℝ) ≤ x ^ Ct → Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) → Real.log ((N : ℝ) * t) ≤ 2 * x ^ (eps / 4) := by
  intro eps Ct m heps heps1
  have hr : 0 < eps / 4 := by positivity
  have hK0 : 0 < 3 + |Ct| := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound (by positivity : (0:ℝ) < 1 / (2 * (3 + |Ct|)))
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (3 * Real.log 2 + Real.log m))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx N t e q d hN hNle hP ht htx hqd => ?_⟩
  obtain ⟨⟨hl, hg⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hX : 0 < x ^ (eps / 4) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hX] at hl
  have hKl : (3 + |Ct|) * Real.log x ≤ x ^ (eps / 4) / 2 := by
    calc (3 + |Ct|) * Real.log x ≤ (3 + |Ct|) * (1 / (2 * (3 + |Ct|)) * x ^ (eps / 4)) :=
          mul_le_mul_of_nonneg_left hl hK0.le
      _ = x ^ (eps / 4) / 2 := by
          field_simp
  have hprod : 1 ≤ 2 ^ (e + 2) * m * q * d := le_trans hN hNle
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have htr : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hNle' : (N:ℝ) ≤ 2 ^ (e + 2) * m * (q * d) := by
    rw [← mul_assoc]
    exact_mod_cast hNle
  rw [Real.log_mul (by linarith) (by linarith)]
  have hlogN : Real.log N ≤ ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d) := by
    calc Real.log N ≤ Real.log (2 ^ (e + 2) * m * ((q:ℝ) * d)) :=
          Real.log_le_log (by linarith) hNle'
      _ = ((e:ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q:ℝ) * d) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by linarith),
            Real.log_pow]
          push_cast
          ring
  have hlogt : Real.log t ≤ Ct * Real.log x := by
    calc Real.log t ≤ Real.log (x ^ Ct) := Real.log_le_log (by linarith) htx
      _ = Ct * Real.log x := Real.log_rpow hxpos _
  have hE : (e:ℝ) * Real.log 2 ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have h := Real.log_le_log (by positivity) hP.2
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne',
      Real.log_rpow hxpos] at h
    exact h
  have hC : Ct * Real.log x ≤ |Ct| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlogx
  nlinarith [mul_nonneg hlogx (by linarith : (0:ℝ) ≤ 1 - 8 * eps)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.bigpair
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.eventually_winPair_gt_power :
    ∀ eps J Ct P : ℝ, 0 < eps → 0 < J → ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      2 * X ^ Ct + 1 < (q : ℝ) ∧ 2 * X ^ Ct + 1 < (d : ℝ) ∧ P < (q : ℝ) ∧ P < (d : ℝ) := by
  intro eps J Ct P heps hJ
  set δ : ℝ := 1 / J * (eps / 5) with hδ
  have hδpos : 0 < δ := by positivity
  set mC : ℝ := max Ct 0 with hmC
  set n : ℕ := ⌈(mC + 1) / δ⌉₊ with hn_def
  have hn : mC + 1 ≤ δ * n := by
    have h := Nat.le_ceil ((mC + 1) / δ)
    rw [div_le_iff₀ hδpos] at h
    linarith
  set M : ℝ := 2 ^ n * (n.factorial : ℝ) with hM_def
  have hM : 0 < M := by positivity
  refine ⟨max (Real.exp J) (M * (|P| + 3) + 1), fun X hX q d hw => ?_⟩
  have hXe : Real.exp J ≤ X := le_trans (le_max_left _ _) hX
  have hXM : M * (|P| + 3) + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by
    have := Real.add_one_le_exp J
    linarith
  have hX0 : 0 < X := by linarith
  have hY : (X ^ (1 / J)) ^ (eps / 5) = X ^ δ := by
    rw [← Real.rpow_mul hX0.le]
  have hlogY : 1 ≤ Real.log (X ^ (1 / J)) := by
    rw [Real.log_rpow hX0]
    have hJl : J ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hXe
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hJ]
    linarith
  set y : ℝ := X ^ δ / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hfac := Real.pow_div_factorial_le_exp y hy0 n
  have hyn : y ^ n = X ^ (δ * n) / 2 ^ n := by
    rw [hy_def, div_pow, ← Real.rpow_natCast (X ^ δ), ← Real.rpow_mul hX0.le]
  have hlow : X ^ (δ * n) / M ≤ Real.exp y := by
    rw [hyn, div_div] at hfac
    exact hfac
  have hpow : X ^ mC * X ≤ X ^ (δ * n) := by
    rw [← Real.rpow_add_one hX0.ne']
    exact Real.rpow_le_rpow_of_exponent_le hX1 hn
  have hCt : X ^ Ct ≤ X ^ mC := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
  have hmC1 : 1 ≤ X ^ mC := Real.one_le_rpow hX1 (le_max_right _ _)
  have hXdiv : |P| + 3 < X / M := by
    rw [lt_div_iff₀ hM]
    linarith
  have hmain : X ^ mC * (|P| + 3) < Real.exp y := by
    have h1 : X ^ mC * (|P| + 3) < X ^ mC * (X / M) :=
      mul_lt_mul_of_pos_left hXdiv (by linarith)
    have h2 : X ^ mC * (X / M) = X ^ mC * X / M := by ring
    have h3 : X ^ mC * X / M ≤ X ^ (δ * n) / M := div_le_div_of_nonneg_right hpow hM.le
    linarith
  have hP0 : 0 ≤ |P| := abs_nonneg P
  have hB1 : 2 * X ^ Ct + 1 < Real.exp y := by nlinarith
  have hB2 : P < Real.exp y := by
    have := le_abs_self P
    nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  have hqlo := hw.q_lo
  have hdlo := hw.d_lo
  rw [hY] at hqlo hdlo
  have hq : Real.exp y < q := by
    rw [← Real.exp_log hq0]
    exact Real.exp_lt_exp.2 (by rw [hy_def]; exact hqlo)
  have hd : Real.exp y < d := by
    rw [← Real.exp_log hd0]
    apply Real.exp_lt_exp.2
    have hXd : 0 ≤ X ^ δ := by positivity
    have hl2 : 1 ≤ Real.log (X ^ (1 / J)) ^ 2 := by nlinarith
    have : X ^ δ / 2 ≤ X ^ δ * Real.log (X ^ (1 / J)) ^ 2 / 2 := by nlinarith
    rw [hy_def]
    linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end

