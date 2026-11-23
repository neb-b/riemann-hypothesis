module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisRest
section
theorem UpperTheory.Reformulated.B.DYlb6.main :
    ∀ {R W T : Type} [inst : CommRing R] [inst_1 : AddCommGroup W] [inst_2 : AddCommGroup T] [inst_3 : _root_.Module R T]
      (j : TensorProduct ℤ R W ≃ₗ[R] T),
      Submodule.span R (Set.range fun (a : W) ↦ (j : TensorProduct ℤ R W → T) ((1 : R) ⊗ₜ[ℤ] a)) = ⊤ := by
  intro R W T _ _ _ _ j
  rw [Submodule.eq_top_iff']
  intro t
  obtain ⟨x, rfl⟩ := j.surjective t
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r w =>
    have h : r ⊗ₜ[ℤ] w = r • ((1 : R) ⊗ₜ[ℤ] w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨w, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisTail
section
open CategoryTheory

theorem UpperTheory.Reformulated.B.DYra4.main.{u} :
    ∀ (S : ℕ → Type u) [∀ (a : ℕ), Finite (S a)] [∀ (a : ℕ), Nonempty (S a)] (t : (a : ℕ) → S (a + (1 : ℕ)) → S a),
      ∃ (s : (a : ℕ) → S a), ∀ (a : ℕ), t a (s (a + (1 : ℕ))) = s a := by
  intro S _ _ t
  let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (X := S) (fun n => TypeCat.ofHom (t n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (S j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (S j.unop))
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun a => x (Opposite.op a), fun a => ?_⟩
  have h := hx (homOfLE (Nat.le_succ a)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisTer
section
theorem UpperTheory.Reformulated.B.DYhd3.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
      (∀ (u u' : V), (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u') = ((B : V → V →ₗ[ℂ] ℂ) u' : V → ℂ) u) →
        (∀ (u : V), (0 : ℝ) ≤ (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u).re) →
          ∀ (x y : V),
            ‖((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
              (((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ B hsymm hpos x y
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun u v => B u v
      conj_inner_symm := fun u v => hsymm v u
      re_inner_nonneg := fun u => hpos u
      add_left := fun u v w => by simp
      smul_left := fun u v r => by simp }
  have h : ‖B x y‖ * ‖B y x‖ ≤ (B x x).re * (B y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  have h2 : ‖B y x‖ = ‖B x y‖ := by
    rw [← hsymm x y]; exact RCLike.norm_conj _
  rw [h2] at h
  rw [sq]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtra
section
theorem UpperTheory.Reformulated.B.DYga2.main.{u_1} :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [inst_3 : MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {A : ℕ},
      Module.finrank ℝ E < A →
        (0 : ℕ) < Module.finrank ℝ E →
          ∃ (c : ℝ),
            (0 : ℝ) ≤ c ∧
              ∀ (η : ℝ),
                (0 : ℝ) < η →
                  ∀ (F : Finset E),
                    (∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → η ≤ ‖y - y'‖ ^ Module.finrank ℝ E) →
                      ∑ y ∈ F, (((1 : ℝ) + ‖y‖) ^ A)⁻¹ ≤ c * ((1 : ℝ) + η⁻¹) := by
  intro E _ _ _ _ _ μ _ A hA hd
  set d := Module.finrank ℝ E with hd_def

  set w : E → ℝ := fun x => ((1 + ‖x‖) ^ A)⁻¹ with hw
  have hwpos : ∀ x, 0 < w x := fun x => by
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]; positivity
  have hint : MeasureTheory.Integrable w μ := by
    have h := integrable_one_add_norm (E := E) (μ := μ) (r := (A:ℝ)) (by exact_mod_cast hA)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]
    rw [Real.rpow_neg this.le, Real.rpow_natCast]
  set I : ℝ := ∫ x, w x ∂μ with hI
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun x => (hwpos x).le
  set V : ℝ := μ.real (Metric.ball (0:E) 1) with hV
  have hVpos : 0 < V := by
    refine ENNReal.toReal_pos ?_ ?_
    · exact (Metric.measure_ball_pos μ 0 one_pos).ne'
    · exact MeasureTheory.measure_ball_lt_top.ne
  refine ⟨2 ^ A * I / V * 2 ^ d, by positivity, ?_⟩
  intro η hη F hF
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set r : ℝ := η ^ ((d:ℝ)⁻¹) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hη _
  have hrd : r ^ d = η := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hη.le, inv_mul_cancel₀ hdR, Real.rpow_one]
  set s : ℝ := min (r / 2) 1 with hs
  have hspos : 0 < s := lt_min (by positivity) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hs2 : 2 * s ≤ r := by
    have : s ≤ r / 2 := min_le_left _ _
    linarith

  have hkey : 1 ≤ s ^ d * (2 ^ d * (1 + η⁻¹)) := by
    have hη' : 0 < η⁻¹ := inv_pos.mpr hη
    rcases le_total (r / 2) 1 with h | h
    · have : s = r / 2 := min_eq_left h
      rw [this, div_pow, hrd]
      have h2 : (2:ℝ) ^ d ≠ 0 := by positivity
      have : η / 2 ^ d * (2 ^ d * (1 + η⁻¹)) = η + 1 := by
        field_simp
      rw [this]; linarith
    · have : s = 1 := min_eq_right h
      rw [this, one_pow, one_mul]
      have : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith

  have hball : ∀ y : E, μ.real (Metric.ball y s) = s ^ d * V := by
    intro y
    have := MeasureTheory.Measure.addHaar_ball_of_pos μ y hspos
    simp only [MeasureTheory.Measure.real, hV]
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

  have hcomp : ∀ y x : E, x ∈ Metric.ball y s → (2 ^ A)⁻¹ * w y ≤ w x := by
    intro y x hx
    have hxy : ‖x‖ ≤ ‖y‖ + s := by
      have h1 : ‖x - y‖ < s := by simpa [dist_eq_norm] using hx
      have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
        have := norm_add_le y (x - y)
        simpa using this
      linarith
    have hle : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
      have := norm_nonneg y
      linarith
    have hx0 : (0:ℝ) < 1 + ‖x‖ := by positivity
    have hy0 : (0:ℝ) < 1 + ‖y‖ := by positivity
    have hp : (1 + ‖x‖) ^ A ≤ 2 ^ A * (1 + ‖y‖) ^ A := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hx0.le hle A
    simp only [hw]
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hp

  have hone : ∀ y : E, (2 ^ A)⁻¹ * w y * (s ^ d * V) ≤ ∫ x in Metric.ball y s, w x ∂μ := by
    intro y
    have := MeasureTheory.setIntegral_ge_of_const_le_real (μ := μ) (f := w) (c := (2 ^ A)⁻¹ * w y)
      (s := Metric.ball y s) Metric.isOpen_ball.measurableSet MeasureTheory.measure_ball_lt_top.ne
      (fun x hx => hcomp y x hx) hint.integrableOn
    rw [hball] at this
    exact this

  have hdisj : Set.Pairwise (F : Set E) (Function.onFun Disjoint fun y => Metric.ball y s) := by
    intro y hy y' hy' hne
    refine Metric.ball_disjoint_ball ?_
    have h1 := hF y hy y' hy' hne
    have h2 : r ≤ ‖y - y'‖ := by
      rw [← hrd] at h1
      exact le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) h1
    rw [dist_eq_norm]
    linarith
  have hsum : ∑ y ∈ F, ∫ x in Metric.ball y s, w x ∂μ ≤ I := by
    rw [← MeasureTheory.integral_biUnion_finset F (fun y _ => Metric.isOpen_ball.measurableSet) hdisj
      (fun y _ => hint.integrableOn)]
    exact MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun x => (hwpos x).le)
  have htot : (2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y ≤ I := by
    refine le_trans ?_ hsum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc _ = (2 ^ A)⁻¹ * w y * (s ^ d * V) := by ring
      _ ≤ _ := hone y
  have hS0 : 0 ≤ ∑ y ∈ F, w y := Finset.sum_nonneg fun y _ => (hwpos y).le
  have hsd : 0 < s ^ d := by positivity
  have hfin : ∑ y ∈ F, w y ≤ 2 ^ A * I / V * (1 / s ^ d) := by
    have h2 : (0:ℝ) < 2 ^ A := by positivity
    rw [show 2 ^ A * I / V * (1 / s ^ d) = (2 ^ A * I) / (s ^ d * V) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left htot h2.le
    calc _ = 2 ^ A * ((2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y) := by field_simp
      _ ≤ _ := this
  have hinv : 1 / s ^ d ≤ 2 ^ d * (1 + η⁻¹) := by
    rw [div_le_iff₀ hsd]
    linarith [hkey, mul_comm (s ^ d) (2 ^ d * (1 + η⁻¹))]
  calc ∑ y ∈ F, ((1 + ‖y‖) ^ A)⁻¹ = ∑ y ∈ F, w y := rfl
    _ ≤ 2 ^ A * I / V * (1 / s ^ d) := hfin
    _ ≤ 2 ^ A * I / V * (2 ^ d * (1 + η⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 ^ A * I / V * 2 ^ d * (1 + η⁻¹) := by ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
section
namespace UpperTheory.Reformulated.B.S6

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := by
    intro a
    have h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      exact a.2
    exact h
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem
  have hint : IsIntegral v.integer x := by
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P.map f, hP.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  exact (Valuation.integer.integers v).mem_of_integral hint

end UpperTheory.Reformulated.B.S6
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraExtra
section
open Filter Topology

theorem UpperTheory.Reformulated.B.Ydb1.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {K S : Set G},
      IsCompact K →
        S ⊆ K →
          (1 : G) ∈ S →
            ∀ {Ψ φ : G → G},
              Continuous Ψ →
                (∀ x ∈ S, Ψ x ∈ S) →
                  (∀ x ∈ S, φ x ∈ S) →
                    (∀ (x y : G), (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y)) →
                      ∀ {l : ℕ},
                        (0 : ℕ) < l →
                          (∀ (U : Set G), IsOpen U → (1 : G) ∈ U → ∃ (m₀ : ℕ), ∀ m ≥ m₀, ∀ x ∈ S, φ^[l * m] x ∈ U) →
                            ∃ v ∈ K, Ψ v = v := by
  intro G _ _ _ _ K S hK hSK h1 Ψ φ hΨ hΨS hφS hrel l _ hconv
  have hφ1 : φ 1 = 1 := by
    have := hrel 1 1
    rw [inv_mul_cancel, inv_one, one_mul] at this
    exact this.symm
  have hΨx : ∀ y, Ψ y = Ψ 1 * φ y := fun y => by
    have := hrel 1 y
    rw [inv_one, one_mul] at this
    rw [← this, mul_inv_cancel_left]
  have hd : ∀ x y, φ (x⁻¹ * y) = (φ x)⁻¹ * φ y := fun x y => by
    rw [← hrel x y, hΨx x, hΨx y, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hmul : ∀ p q, φ (p * q) = φ p * φ q := by
    intro p q
    have hinv : φ p⁻¹ = (φ p)⁻¹ := by
      have := hd p 1
      rw [mul_one, hφ1, mul_one] at this
      exact this
    have := hd p⁻¹ q
    rw [inv_inv, hinv, inv_inv] at this
    exact this
  have hit : ∀ n x, Ψ^[n] x = Ψ^[n] 1 * φ^[n] x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih x, hΨx (Ψ^[n] 1 * φ^[n] x), hΨx (Ψ^[n] 1), hmul, mul_assoc]
  have ha : Ψ 1 ∈ S := hΨS 1 h1
  have hPS : ∀ n, Ψ^[n] 1 ∈ S := fun n => (Set.MapsTo.iterate (f := Ψ) hΨS n) h1
  have hφa : ∀ n, φ^[n] (Ψ 1) ∈ S := fun n => (Set.MapsTo.iterate (f := φ) hφS n) ha
  have hstep : ∀ n, Ψ (Ψ^[n] 1) = Ψ^[n] 1 * φ^[n] (Ψ 1) := fun n => by
    rw [← Function.iterate_succ_apply' Ψ n 1, Function.iterate_succ_apply, hit]
  have hlim : Tendsto (fun m : ℕ => φ^[l * m] (Ψ 1)) atTop (𝓝 1) := by
    rw [(nhds_basis_opens (1 : G)).tendsto_right_iff]
    rintro U ⟨h1U, hU⟩
    obtain ⟨m₀, hm₀⟩ := hconv U hU h1U
    exact eventually_atTop.2 ⟨m₀, fun m hm => hm₀ m hm _ ha⟩
  obtain ⟨v, hvK, hv⟩ := hK.exists_mapClusterPt (f := (atTop : Filter ℕ))
    (u := fun m : ℕ => Ψ^[l * m] 1)
    (by
      rw [le_principal_iff, mem_map]
      exact univ_mem' fun m => hSK (hPS (l * m)))
  obtain ⟨𝒰, h𝒰, hu⟩ := mapClusterPt_iff_ultrafilter.1 hv
  refine ⟨v, hvK, ?_⟩
  have h₁ : Tendsto (fun m : ℕ => Ψ (Ψ^[l * m] 1)) 𝒰 (𝓝 (Ψ v)) := (hΨ.tendsto v).comp hu
  have h₂ : Tendsto (fun m : ℕ => Ψ (Ψ^[l * m] 1)) 𝒰 (𝓝 (v * 1)) := by
    simp_rw [hstep]
    exact hu.mul (hlim.mono_left h𝒰)
  rw [mul_one] at h₂
  exact tendsto_nhds_unique h₁ h₂
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraFurther
section
namespace UpperTheory.Reformulated.B.AddCharacterCount.Helpers

private lemma card_le {C F : Type} [Field C] [Fintype F] [AddCommGroup F] :
    Finite (AddChar F C) ∧ Nat.card (AddChar F C) ≤ Nat.card F := by
  have li : LinearIndependent C (M := Multiplicative F → C)
      ((fun f => f : (Multiplicative F →* C) → Multiplicative F → C) ∘ AddChar.toMonoidHomEquiv) :=
    (linearIndependent_monoidHom (Multiplicative F) C).comp _ AddChar.toMonoidHomEquiv.injective
  have h1 := li.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have hlt : Cardinal.mk (AddChar F C) < Cardinal.aleph0 :=
    lt_of_le_of_lt h1 Cardinal.natCast_lt_aleph0
  have hfin : Finite (AddChar F C) := Cardinal.lt_aleph0_iff_finite.mp hlt
  refine ⟨hfin, ?_⟩
  have : Nat.card (AddChar F C) ≤ Fintype.card (Multiplicative F) := by
    have h2 := Cardinal.toNat_le_toNat h1 Cardinal.natCast_lt_aleph0
    simpa only [Cardinal.toNat_mk, Cardinal.toNat_natCast] using h2
  simpa [Nat.card_eq_fintype_card] using this

end UpperTheory.Reformulated.B.AddCharacterCount.Helpers

open UpperTheory.Reformulated.B.AddCharacterCount.Helpers in
theorem UpperTheory.Reformulated.B.AddCharacterCount.main :
    ∀ {C F : Type} [inst : Field C] [inst_1 : Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F C),
      ψ ≠ (1 : AddChar F C) →
        ∃ (e : F ≃ AddChar F C),
          (∀ (h h' : F), (e : F → AddChar F C) (h + h') = (e : F → AddChar F C) h * (e : F → AddChar F C) h') ∧
            ∀ (h a : F), ((e : F → AddChar F C) h : F → C) a = (ψ : F → C) (h * a) := by
  intro C F _ _ _ _ ψ hψ
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)
  obtain ⟨hfin, hc⟩ := card_le (C := C) (F := F)
  have hbij : Function.Bijective ψ.mulShift := hinj.bijective_of_nat_card_le hc
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩
  · intro h h'
    simp [AddChar.mulShift_mul]
  · intro h a
    simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraLast
section
namespace DedekindLocalUniformizer
end DedekindLocalUniformizer

theorem UpperTheory.Reformulated.B.Yde5.main :
    ∀ {R : Type} [inst : CommRing R] [IsDedekindDomain R] (P : Ideal R),
      P.IsMaximal → P ≠ ⊥ → ∃ (π : R), π ≠ (0 : R) ∧ π ∈ P ∧ ∃ s ∉ P, ∀ y ∈ P, ∃ (c : R), s * y = π * c := by
  intro R _ _ P hmax hbot
  haveI : P.IsPrime := hmax.isPrime
  have hlt : P ^ (1 + 1) < P ^ 1 := Ideal.pow_succ_lt_pow hbot 1
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hπ2 (Ideal.zero_mem _)
  refine ⟨π, hπ0, hπP, ?_⟩
  have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 hπP
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun y hy => ?_⟩
  have hmem : s * y ∈ Ideal.span {π} := by
    rw [hJ, mul_comm s y]; exact Ideal.mul_mem_mul hy hsJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨c, by rw [← hc, mul_comm]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraMore
section
theorem UpperTheory.Reformulated.B.Ue24.eq_one_of_pow_near :
    ∀ {z : ℂ},
    (∀ (k : ℕ), ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 : ℕ) ^ (k + 1) - 1 = (z ^ (2 : ℕ) ^ k - 1) * (z ^ (2 : ℕ) ^ k + 1) := by
        rw [pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 : ℕ) ^ k + 1‖ := by
        have h3 := norm_sub_le (z ^ (2 : ℕ) ^ k + 1) (z ^ (2 : ℕ) ^ k - 1)
        have h4 : (z ^ (2 : ℕ) ^ k + 1) - (z ^ (2 : ℕ) ^ k - 1) = 2 := by ring
        rw [h4] at h3
        have h5 : ‖(2 : ℂ)‖ = 2 := by simp
        have h6 := h k
        linarith
      rw [e, norm_mul]
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
        _ ≤ _ := mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have h7 := key k
  have h8 := h k
  linarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraRest
section
theorem UpperTheory.Reformulated.B.Ydb6.main :
    ∀ {O Ω V : Type} [inst : CommRing O] [inst_1 : Field Ω] [inst_2 : Algebra O Ω] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module Ω V] (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω),
      (∀ (v : V), v ∈ B ↔ ∃ e ∈ A, v = c • e) →
        ∀ (v : V),
          v ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
            ∃ e ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e := by
  intro O Ω V _ _ _ _ _ R A B c hB v
  let f : V →+ V := DistribSMul.toAddMonoidHom V c
  have hS : {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} =
      f '' {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, e, he, rfl⟩
      obtain ⟨e', he', rfl⟩ := (hB e).1 he
      refine ⟨a • e', ⟨a, ha, e', he', rfl⟩, ?_⟩
      show c • a • e' = a • c • e'
      rw [smul_smul, smul_smul, mul_comm]
    · rintro ⟨x, ⟨a, ha, e, he, rfl⟩, rfl⟩
      refine ⟨a, ha, c • e, (hB _).2 ⟨e, he, rfl⟩, ?_⟩
      show c • a • e = a • c • e
      rw [smul_smul, smul_smul, mul_comm]
  rw [hS, ← AddMonoidHom.map_closure, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraSide
section
theorem UpperTheory.Reformulated.B.Ydc3.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have h1 : (z ^ 2).re = z.re * z.re - z.im * z.im := by
    rw [pow_two, Complex.mul_re]
  have h2 : (z ^ 2).im = z.re * z.im + z.im * z.re := by
    rw [pow_two, Complex.mul_im]
  have e1 : (-(d : ℂ)).re = -(d : ℝ) := by simp
  have e2 : (-(d : ℂ)).im = 0 := by simp
  rw [hz, e1] at h1
  rw [hz, e2] at h2
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm : z.re * z.im = 0 := by linarith
  have ha : z.re = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · exfalso
      have : z.im * z.im = 0 := by rw [h]; ring
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [ha]
  · simp
end

