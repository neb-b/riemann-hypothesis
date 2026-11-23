module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ClassicalFormsLevelMonotoneAndUpStable
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_step {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω) (φ : X.I.T →* Ωˣ) (U : Subgroup X.Ub) (c : ℕ)
    (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) :
    ∀ F ∈ X.Cl τ W.ξ U (c + 1) φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Cl τ W.ξ U c φ := by
  classical
  intro F hF
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z X.I.z_mem
  have hsum : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F =
      (((W.χ ⟨X.I.z, X.I.P_le _ X.I.z_mem⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * X.I.z) F := by
    rw [← (h2 s hs hu).2 F hF.2.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
    · change F i (X.glob γ * g * (1, u * X.I.z)) = _ *ᵥ F i (g * (1, u * X.I.z))
      rw [mul_assoc]
      exact hF.1.1 i trivial γ _
    · rw [(ctrlEq Γ Ga Gp X O Ω W m τ).2.2, hF.1.2 w hw]
  · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ hφ).2 F hF.2)

theorem UpperTheory.classicalForms_level_monotone_and_Up_stable :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type)
      [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ)
      (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ),
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ) ∧
      (∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ) ∧
      ∀ e n : ℕ, e ≤ n → ∀ F ∈ X.ClO W τ U (c + e) φ,
        (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F ∈ X.ClO W τ U c φ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hφ
  have mono : ∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ := by
    intro c' hc F hF
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hF
    refine Submodule.mem_inf.2 ⟨h1, ?_⟩
    exact ⟨h2.1, fun y hy => h2.2.1 y (X.I.Nm_anti hc hy), h2.2.2⟩
  have step : ∀ e, ∀ F ∈ X.ClO W τ U (c + e + 1) φ,
      X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U (c + e) φ := by
    intro e F hF
    exact lower_step X W _ _ U (c + e)
      (fun t ht => by simp [hφ t (X.I.Tc_anti (Nat.le_add_right c e) ht)]) F hF
  have down : ∀ e, ∀ F ∈ X.ClO W τ U (c + e) φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ e) F ∈ X.ClO W τ U c φ := by
    intro e
    induction e with
    | zero =>
      intro F hF
      simpa using hF
    | succ e ih =>
      intro F hF
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (step e F hF)
  have stay : ∀ k, ∀ F ∈ X.ClO W τ U c φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ k) F ∈ X.ClO W τ U c φ := by
    intro k
    induction k with
    | zero =>
      intro F hF
      simpa using hF
    | succ k ih =>
      intro F hF
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (step 0 F (mono _ (Nat.le_succ c) hF))
  refine ⟨mono, fun F hF => step 0 F (mono _ (Nat.le_succ c) hF), ?_⟩
  intro e n hen F hF
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hen
  rw [add_comm e k, pow_add, mul_apply_eq_comp]
  exact stay k _ (down e F hF)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompactTorusUnitsEqTopOfNonsplit
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem int_of_norm_one {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] {Δ τ : K} (h : IsLoc O Δ) (hτ : ¬ IsSquare (τ ^ 2 - 4)) (e : Etau K τ)
    (hn : QuadraticAlgebra.norm e = 1) : IsIntegral O e := by
  classical
  haveI := h.frac
  have hN : e.re * e.re + τ * e.re * e.im - (-1) * e.im * e.im = 1 := by
    have h' := hn
    rw [QuadraticAlgebra.norm_def] at h'
    exact h'
  by_cases hq : e.im = 0
  · have hp : (e.re - 1) * (e.re + 1) = 0 := by
      rw [hq] at hN
      linear_combination hN
    rcases mul_eq_zero.mp hp with h1 | h1
    · have he : e = 1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one
    · have he : e = -1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one.neg
  · have h2K : (2 : K) ≠ 0 := by
      have h2 := h.two.map (algebraMap O K)
      rw [map_ofNat] at h2
      exact h2.ne_zero
    have nz : ∀ x y : K, y ≠ 0 → x * x + τ * x * y + y * y ≠ 0 := by
      intro x y hy hxy
      apply hτ
      refine ⟨2 * x / y + τ, ?_⟩
      field_simp
      linear_combination (-4) * hxy
    obtain ⟨t, ht⟩ : ∃ t : O, algebraMap O K t = QuadraticAlgebra.trace e := by
      by_contra hne
      push_neg at hne
      have hTd : QuadraticAlgebra.trace e = 2 * e.re + τ * e.im := QuadraticAlgebra.trace_def e
      set T := QuadraticAlgebra.trace e with hTdef
      have hT0 : T ≠ 0 := fun h0 => hne 0 (by rw [map_zero, h0])
      rcases ValuationRing.isInteger_or_isInteger O T with ⟨t, ht⟩ | ⟨s, hs⟩
      · exact hne t ht
      · have hsm : s ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          obtain ⟨u, rfl⟩ := hu
          apply hne (↑u⁻¹)
          rw [map_units_inv, hs, inv_inv]
        obtain ⟨r, hr, -⟩ := sqrtO O K Δ h (1 - 4 * s ^ 2) 1 isUnit_one (by
          have e' : (1 - 4 * s ^ 2) - 1 ^ 2 = s * (-(4 * s)) := by ring
          rw [e']
          exact Ideal.mul_mem_right _ _ hsm)
        have hTS : T * algebraMap O K s = 1 := by
          rw [hs]
          exact mul_inv_cancel₀ hT0
        have hR : (algebraMap O K r) ^ 2 = 1 - 4 * (algebraMap O K s) ^ 2 := by
          rw [← map_pow, hr, map_sub, map_one, map_mul, map_pow, map_ofNat]
        apply nz (-τ * e.im - T * algebraMap O K r) (2 * e.im) (mul_ne_zero h2K hq)
        linear_combination T ^ 2 * hR - 4 * (T * algebraMap O K s + 1) * hTS + 4 * hN +
          (T + 2 * e.re + τ * e.im) * hTd
    exact isIntegral_of_trace_norm t 1 ht.symm (by rw [hn, map_one])

private theorem norm_quo {K : Type} [Field K] {τ : K} (z : (Etau K τ)ˣ) : QuadraticAlgebra.norm (quo z) = 1 := by
  simp only [quo, map_mul, QuadraticAlgebra.norm_star]
  rw [← map_mul, Units.mul_inv, map_one]

theorem UpperTheory.compactTorusUnits_eq_top_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → Cint O τ = ⊤ := by
  intro O K _ _ _ _ _ Δ τ h _ hτ
  rw [eq_top_iff]
  intro z _
  exact ⟨int_of_norm_one h hτ _ (norm_quo z), int_of_norm_one h hτ _ (norm_quo z⁻¹)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EvenValuationNormCompactUnitsOfSplit
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {τ r r' : K}

private def phiK (τ r : K) (h : r * r = -1 + τ * r) : Etau K τ →ₐ[K] K where
  toFun x := x.re + x.im * r
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (-(x.im * y.im)) * h
  map_zero' := by simp
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
  commutes' a := by
    simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, zero_mul,
      add_zero, Algebra.algebraMap_self_apply]

private lemma phiK_apply (h : r * r = -1 + τ * r) (x : Etau K τ) : phiK τ r h x = x.re + x.im * r := rfl

private lemma phiK_star (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : Etau K τ) :
    phiK τ r h (star x) = phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private lemma phiK_norm (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (hp : r * r' = 1)
    (x : Etau K τ) : QuadraticAlgebra.norm x = phiK τ r h x * phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.norm_def]
  linear_combination (-(x.re * x.im)) * hs - x.im ^ 2 * hp

private lemma phiK_ne (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) : phiK τ r h (x : Etau K τ) ≠ 0 :=
  (x.isUnit.map (phiK τ r h)).ne_zero

private lemma phiK_inv (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) :
    phiK τ r h ((x⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (phiK τ r h (x : Etau K τ))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, Units.inv_mul, map_one]

private lemma phiK_quo (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : (Etau K τ)ˣ) :
    phiK τ r h (quo x) = phiK τ r h (x : Etau K τ) * (phiK τ r' h' (x : Etau K τ))⁻¹ := by
  rw [quo, map_mul, phiK_star h h' hs, phiK_inv]

private lemma phiK_inj (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') :
    Function.Injective ((phiK τ r h).prod (phiK τ r' h')) := by
  intro x y hxy
  have h1 : x.re + x.im * r = y.re + y.im * r := congrArg Prod.fst hxy
  have h2 : x.re + x.im * r' = y.re + y.im * r' := congrArg Prod.snd hxy
  have h3 : x.im = y.im := by
    have : (x.im - y.im) * (r - r') = 0 := by linear_combination h1 - h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne))
  ext
  · rw [h3] at h1; exact add_right_cancel h1
  · exact h3

private lemma phiK_surj (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (a b : K) :
    ∃ x : Etau K τ, phiK τ r h x = a ∧ phiK τ r' h' x = b := by
  have := sub_ne_zero.2 hne
  refine ⟨⟨a - (a - b) / (r - r') * r, (a - b) / (r - r')⟩, ?_, ?_⟩
  · simp [phiK_apply]
  · simp only [phiK_apply]; field_simp; ring

private lemma phiK_surjU (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : (Etau K τ)ˣ, phiK τ r h x = a ∧ phiK τ r' h' x = b := by
  obtain ⟨x, hx1, hx2⟩ := phiK_surj h h' hne a b
  obtain ⟨y, hy1, hy2⟩ := phiK_surj h h' hne a⁻¹ b⁻¹
  have hxy : x * y = 1 := by
    apply phiK_inj h h' hne
    refine Prod.ext ?_ ?_
    · simp only [AlgHom.prod_apply, map_mul, map_one, hx1, hy1]
      exact mul_inv_cancel₀ ha
    · simp only [AlgHom.prod_apply, map_mul, map_one, hx2, hy2]
      exact mul_inv_cancel₀ hb
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, hx1, hx2⟩

private lemma phiK_int (O : Type) [CommRing O] [Algebra O K]
    (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (x : Etau K τ) :
    IsIntegral O x ↔ IsIntegral O (phiK τ r h x) ∧ IsIntegral O (phiK τ r' h' x) := by
  constructor
  · intro hx
    exact ⟨hx.map ((phiK τ r h).restrictScalars O), hx.map ((phiK τ r' h').restrictScalars O)⟩
  · rintro ⟨ha, hb⟩
    set a := phiK τ r h x
    set b := phiK τ r' h' x
    let f : K →ₐ[O] Etau K τ := IsScalarTower.toAlgHom O K (Etau K τ)
    have ha' : IsIntegral O (algebraMap K (Etau K τ) a) := ha.map f
    have hb' : IsIntegral O (algebraMap K (Etau K τ) b) := hb.map f
    have hroot : (x - algebraMap K (Etau K τ) a) * (x - algebraMap K (Etau K τ) b) = 0 := by
      apply phiK_inj h h' hne
      refine Prod.ext ?_ ?_
      · simp only [AlgHom.prod_apply, map_mul, map_sub, AlgHom.commutes, map_zero, Prod.fst_zero]
        simp [a]
      · simp only [AlgHom.prod_apply, map_mul, map_sub, AlgHom.commutes, map_zero, Prod.snd_zero]
        simp [b]
    let C := integralClosure O (Etau K τ)
    have hxC : IsIntegral C x := by
      refine ⟨(Polynomial.X - Polynomial.C (⟨_, ha'⟩ : C)) * (Polynomial.X - Polynomial.C (⟨_, hb'⟩ : C)),
        (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact hroot
    exact isIntegral_trans x hxC

end SlopeTestRemainingChoices

theorem UpperTheory.evenValuation_norm_compactUnits_of_split :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → IsSquare (τ ^ 2 - 4) → (∀ c ∈ Cint O τ, EvenVal O (QuadraticAlgebra.norm ((c : (Etau K τ)ˣ) : Etau K τ))) ∧ ∀ y : (Etau K τ)ˣ, EvenVal O (QuadraticAlgebra.norm (y : Etau K τ)) → ∃ z : (Etau K τ)ˣ, ∃ c ∈ Cint O τ, y = c * z ^ 2 := by
  intro O K _ _ _ _ _ Δ τ hL hτ hsq
  haveI := hL.frac
  have h2 : (2 : K) ≠ 0 := by
    have e := (hL.two).map (algebraMap O K)
    rw [map_ofNat] at e
    exact e.ne_zero
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs, mul_zero]
  set r : K := (τ + s) / 2 with hrE
  set r' : K := (τ - s) / 2 with hr'E
  have hr : r * r = -1 + τ * r := by
    rw [hrE]
    field_simp
    linear_combination (-1 : K) * hs
  have hr' : r' * r' = -1 + τ * r' := by
    rw [hr'E]
    field_simp
    linear_combination (-1 : K) * hs
  have hsum : r + r' = τ := by
    rw [hrE, hr'E]
    field_simp
    ring
  have hsum' : r' + r = τ := by rw [add_comm]; exact hsum
  have hprod : r * r' = 1 := by
    rw [hrE, hr'E]
    field_simp
    linear_combination hs
  have hne : r ≠ r' := by
    intro e
    apply hs0
    have e2 : r - r' = s := by
      rw [hrE, hr'E]
      field_simp
      ring
    rw [← e2, e, sub_self]
  have hint : ∀ v : K, (∃ w : O, algebraMap O K w = v) → IsIntegral O v := by
    rintro v ⟨w, rfl⟩
    exact isIntegral_algebraMap
  have huv : ∀ (u : Oˣ) (v : K), v = algebraMap O K (u : O) → IsIntegral O v ∧ IsIntegral O v⁻¹ := by
    intro u v hv
    refine ⟨hint v ⟨u, hv.symm⟩, hint v⁻¹ ⟨(u⁻¹ : Oˣ), ?_⟩⟩
    rw [hv, map_units_inv]
  have hcint : ∀ (c : (Etau K τ)ˣ) (u : Oˣ),
      phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹ = algebraMap O K (u : O) →
      c ∈ Cint O τ := by
    intro c u hu
    obtain ⟨i1, i2⟩ := huv u _ hu
    have e2 : phiK τ r' hr' (c : Etau K τ) * (phiK τ r hr (c : Etau K τ))⁻¹
        = (phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm]
    refine ⟨?_, ?_⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', e2]
      exact ⟨i1, i2⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', phiK_inv, phiK_inv,
        inv_inv, inv_inv]
      refine ⟨?_, ?_⟩
      · rw [mul_comm, e2]
        exact i2
      · rw [mul_comm]
        exact i1
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, -⟩ := hc
    rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum'] at hc1
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.1
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.2
    have hA := phiK_ne hr c
    have hB := phiK_ne hr' c
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, phiK τ r' hr' (c : Etau K τ), hB, ?_⟩
    rw [phiK_norm hr hr' hsum hprod, Units.val_mk, ha]
    field_simp
  · rintro y ⟨u, t, ht, hy⟩
    have hA := phiK_ne hr y
    have hB := phiK_ne hr' y
    obtain ⟨z, hz1, hz2⟩ := phiK_surjU hr hr' hne 1 (phiK τ r' hr' (y : Etau K τ) / t) one_ne_zero
      (div_ne_zero hB ht)
    refine ⟨z, y * (z ^ 2)⁻¹, ?_, (inv_mul_cancel_right y (z ^ 2)).symm⟩
    apply hcint _ u
    rw [Units.val_mul, map_mul, map_mul, phiK_inv, phiK_inv, Units.val_pow_eq_pow_val, map_pow,
      map_pow, hz1, hz2]
    have hn := phiK_norm hr hr' hsum hprod (y : Etau K τ)
    rw [hy] at hn
    field_simp
    linear_combination (-1 : K) * hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralFormLiftingControlMap
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem control_map_translate_trace {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type} [CommRing O]
    [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (F : Fin m → X.Fn Ω (W.d + 1))
    (g : Ga × Gp) (b : Gp) (i : Fin m) :
    X.ctrl m W F (g * (1, b)) i =
      ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ (X.rpF Ω (W.d + 1) m b F i g)) j := by
  rw [Frame.ctrl_apply, Frame.unt_apply]
  show _ = ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ F i (g * (1, b))) j
  rw [Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, map_inv]
  rfl

theorem UpperTheory.exists_integral_form_lifting_controlMap :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ), Function.Injective (algebraMap O Ω) → (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) → ∀ F ∈ X.ClO W τ U c φ, F ∈ X.Lat m W (mIm O Ω 0) → ∃ f ∈ X.Sp τ θ U, X.mapFn (B := Ω) f = X.ctrl m W F ∧ ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c θ hinj hθ F hF hL
  have hL' : ∀ i g k, X.unt m W F i g k ∈ mIm O Ω 0 := fun i g k => hL i g k
  have hv : ∀ i g k, ∃ a : O, algebraMap O Ω a = X.unt m W F i g k := by
    intro i g k
    obtain ⟨a, -, ha⟩ := mem_mIm.1 (hL' i g k)
    exact ⟨a, ha⟩
  choose v hv0 using hv
  have hu : ∀ i g j, ((W.ξ g.2)⁻¹.val *ᵥ F i g) j = algebraMap O Ω (v i g j) := by
    intro i g j
    rw [hv0, Frame.unt_apply]
  obtain ⟨f, hf⟩ : ∃ f : X.Fn O m, ∀ g i, algebraMap O Ω (f g i) = X.ctrl m W F g i :=
    ⟨fun g i => v i g 0, fun g i => by rw [Frame.ctrl_apply, hv0]⟩
  have hf0 : ∀ g i, algebraMap O Ω (f g i) = algebraMap O Ω (v i g 0) := by
    intro g i
    rw [hf, Frame.ctrl_apply, hv0]
  have hs : ∀ (b : Gp) (a : Ω), X.rpF Ω (W.d + 1) m b F = a • F → ∀ g i,
      algebraMap O Ω (f (g * (1, b)) i) = a * ∑ j, (W.ξ b⁻¹).val 0 j * algebraMap O Ω (v i g j) := by
    intro b a hb g i
    rw [hf, control_map_translate_trace, hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul, hu]
    ring
  have hE := hF.2
  have hUF := hF.1.2
  have hA : ∀ i (γ : Γ) (g : Ga × Gp), F i (X.glob γ * g) = (W.ξ (X.glob γ).2).val *ᵥ F i g :=
    fun i γ g => hF.1.1 i (Set.mem_univ i) γ g
  have key : ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
    intro k c' hc hξ y hy g _ i _
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hc hy
    choose a ha hae using fun j => hξ y⁻¹ (inv_mem hy) 0 j
    have h1 : f (g * (1, y)) i - f g i = ∑ j, a j * v i g j := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hs y 1 (by rw [one_smul]; exact hE.2.1 y hyc) g i, hf0, one_mul, map_sum]
      simp only [hae, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
      ring
    show f (g * (1, y)) i - f g i ∈ maximalIdeal O ^ k
    rw [h1]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (ha j)
  refine ⟨f, ?_, ?_, key⟩
  · refine Submodule.mem_inf.2 ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro γ g
      funext i
      apply hinj
      rw [hf, hf, Frame.ctrl_apply, Frame.ctrl_apply, Frame.unt_apply, Frame.unt_apply, hA, Prod.snd_mul, map_mul,
        Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    · intro u hu'
      funext g i
      apply hinj
      show algebraMap O Ω (f (g * (1, u)) i) = algebraMap O Ω (f g i)
      rw [hs u 1 (by rw [one_smul]; exact hE.1 u hu') g i, hf0, one_mul]
      simp only [W.row_N _ (X.I.N_le (inv_mem hu')), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · intro t
      funext g i
      apply hinj
      show algebraMap O Ω (f (g * (1, (t : Gp))) i) = algebraMap O Ω (((θ t)⁻¹ : Oˣ) * f g i)
      rw [hs (t : Gp) _ (hE.2.2 t) g i, map_mul, hf0]
      have hr : ∀ j, (W.ξ (t : Gp)⁻¹).val 0 j = if j = 0 then (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) else 0 :=
        fun j => W.torusAction ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ j
      have hχ : (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) = (W.χ ⟨t, X.I.T_le t.2⟩ : Ω)⁻¹ := by
        rw [← Units.val_inv_eq_inv_val, ← map_inv]
        rfl
      have hθ' : algebraMap O Ω (((θ t)⁻¹ : Oˣ) : O) = (algebraMap O Ω (θ t))⁻¹ := map_units_inv (algebraMap O Ω) (θ t)
      simp only [hr, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hχ, hθ', hθ t]
      simp only [MonoidHom.comp_apply, Units.coe_map, Units.val_inv_eq_inv_val, MonoidHom.coe_coe]
      rw [mul_inv, mul_assoc]
      rfl
    · intro k
      obtain ⟨c1, hc1⟩ := W.cont_Nm k
      refine ⟨max c c1, fun y hy g i => ?_⟩
      have h := key k (max c c1) (le_max_left _ _)
        (fun y hy => hc1 y (X.I.Nm_anti (le_max_right _ _) hy)) y hy g (Set.mem_univ _) i (Set.mem_univ _)
      exact h
    · intro u hu'
      funext g i
      apply hinj
      rw [Frame.ra_apply, hf, ← hUF u hu',
        (ctrlEq Γ Ga Gp X O Ω W m ((GeneralLinearGroup.map (algebraMap O Ω)).comp τ)).1 u F, Frame.ra_apply]
      simp [Matrix.mulVec, dotProduct, hf]
  · funext g i
    exact hf g i
end

