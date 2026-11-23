module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLatticeGLConjLe
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem card_latticeGL_conj_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ A : ℕ,
    ∀ W : Set (GA E a), IsCompact W → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GL (Fin a) (Cinf E),
      {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.Finite ∧
      ({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℝ) ≤
        C * height y ^ (2 * A) := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨0, fun W _ => ⟨1, zero_le_one, fun y => ?_⟩⟩
    have hs : ∀ s : Set (GlobalTheory.UnitaryBC.latticeGL E 0), s.Subsingleton := fun s x _ z _ =>
      Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))
    refine ⟨(hs _).finite, ?_⟩
    rw [pow_zero, mul_one]
    exact_mod_cast (Set.ncard_le_one_iff (hs _).finite).2 fun h1 h2 => hs _ h1 h2
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.ratGL_bounded_count E a
  refine ⟨m, fun W hW => ?_⟩
  obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.CentralExponent.abs_le_of_conj_mem E a ha W hW
  obtain ⟨hInf, hFin, -, -⟩ := _root_.GlobalTheory.GLProj.continuous_proj_incl E a
  set e : GA E a := GlobalTheory.UnitaryBC.splitCentre E a 1 with he
  set W' : Set (GA E a) := ⋃ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, (fun g => g * (e ^ n)⁻¹) '' W with hW'
  have hW'c : IsCompact W' := (Finset.Icc (-(n₀ : ℤ)) n₀).isCompact_biUnion fun n _ =>
    hW.image (continuous_mul_const _)
  set Kf : Set (GL (Fin a) (Af E)) := (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) '' W' with hKf
  have hKfc : IsCompact Kf := hW'c.image hFin
  have hv : Continuous fun g : GA E a =>
      ((Matrix.GeneralLinearGroup.map (pInf E) g : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val.comp hInf
  have ht : Continuous (toL : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a) := continuous_id
  have hcn : Continuous fun g : GA E a => ‖toL (Matrix.GeneralLinearGroup.map (pInf E) g).val‖ :=
    continuous_norm.comp (ht.comp hv)
  obtain ⟨B₀, hB₀⟩ := hW'c.exists_bound_of_continuousOn hcn.continuousOn
  set B : ℝ := max 0 B₀ with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBb : ∀ w ∈ W', ‖toL (Matrix.GeneralLinearGroup.map (pInf E) w).val‖ ≤ B := fun w hw =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ w hw).trans (le_max_right _ _))
  obtain ⟨C₁, hC₁0, hC₁⟩ := hm Kf hKfc
  set N : ℝ := ((Set.Icc (-(n₀ : ℤ)) n₀).ncard : ℝ) with hN
  set c : ℝ := 1 + (a : ℝ) ^ 2 * B with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) ^ 2 * B := by positivity
    linarith
  refine ⟨C₁ * c ^ m * N, by positivity, fun y => ?_⟩
  set T : ℝ := c * height y ^ 2 with hT
  have hh := one_le_height y
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hh)
  obtain ⟨hfin, hcard⟩ := hC₁ T hT1
  set S := {δ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ)).val‖ ≤ T ∧
    Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) ∈ Kf} with hS
  let f : GL (Fin a) E × ℤ → GlobalTheory.UnitaryBC.latticeGL E a := fun p =>
    ⟨ratGL E a p.1 * e ^ p.2, GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨p.1, p.2, rfl⟩⟩
  have hsub : {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W} ⊆
      f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀) := by
    rintro ⟨γ, hγ⟩ hγW
    obtain ⟨δ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
    change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y ∈ W at hγW
    have hn : |n| ≤ n₀ := hn₀ δ n _ hγW
    have hn' : n ∈ Set.Icc (-(n₀ : ℤ)) n₀ := abs_le.1 hn
    set w := (infGL E a y)⁻¹ * ratGL E a δ * infGL E a y with hw
    have hcomm : Commute (e ^ n) (infGL E a y) :=
      (Commute.zpow_left (GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm 1 (infGL E a y)) n)
    have hwW : w ∈ W' := by
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2 hn')) ⟨_, hγW, ?_⟩
      change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y * (e ^ n)⁻¹ = w
      simp only [mul_assoc]
      rw [← mul_assoc (e ^ n) (infGL E a y), hcomm.eq, mul_inv_cancel_right]
      all_goals simp only [hw, mul_assoc]
    have hδ : ratGL E a δ = infGL E a y * w * (infGL E a y)⁻¹ := by rw [hw]; group
    refine ⟨(δ, n), ⟨⟨?_, ?_⟩, hn'⟩, rfl⟩
    · have e1 : Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ) =
          y * Matrix.GeneralLinearGroup.map (pInf E) w * y⁻¹ := by
        rw [hδ, map_mul, map_mul, map_inv, pInf_infGL]
      rw [e1, Units.val_mul, Units.val_mul]
      have hw' := hBb w hwW
      have p1 := GlobalTheory.AutGrowth.norm_toL_mul_le (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val) (y⁻¹).val
      have p2 := GlobalTheory.AutGrowth.norm_toL_mul_le y.val (Matrix.GeneralLinearGroup.map (pInf E) w).val
      have hy1 : ‖toL y.val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
      have hy2 : ‖toL (y⁻¹).val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL y.val)]
      have n1 := norm_nonneg (toL y.val)
      have n2 := norm_nonneg (toL (y⁻¹).val)
      have n3 := norm_nonneg (toL (Matrix.GeneralLinearGroup.map (pInf E) w).val)
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have q1 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val)‖ ≤ a * (height y * B) :=
        p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hy1 hw' n3 (by linarith)) ha0)
      have q2 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val * (y⁻¹).val)‖ ≤
          a * ((a * (height y * B)) * height y) :=
        p1.trans (mul_le_mul_of_nonneg_left (mul_le_mul q1 hy2 n2 (by positivity)) ha0)
      refine q2.trans ?_
      rw [hT, hc]
      have : 0 ≤ height y ^ 2 := by positivity
      nlinarith
    · have e2 : Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) =
          Matrix.GeneralLinearGroup.map (pFin E) w := by
        rw [hδ, map_mul, map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
      rw [e2]
      exact ⟨w, hwW, rfl⟩
  have hfin2 : (f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)).Finite := (hfin.prod (Set.finite_Icc _ _)).image f
  refine ⟨hfin2.subset hsub, ?_⟩
  have k1 := Set.ncard_le_ncard hsub hfin2
  have k2 := Set.ncard_image_le (f := f) (hfin.prod (Set.finite_Icc (-(n₀ : ℤ)) n₀))
  rw [Set.ncard_prod] at k2
  have k3 : (({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℕ) : ℝ) ≤
      (S.ncard : ℝ) * N := by rw [hN]; exact_mod_cast k1.trans k2
  refine k3.trans ?_
  have hN0 : 0 ≤ N := by positivity
  calc (S.ncard : ℝ) * N ≤ C₁ * T ^ m * N := mul_le_mul_of_nonneg_right hcard hN0
    _ = C₁ * c ^ m * N * height y ^ (2 * m) := by rw [hT, mul_pow, ← pow_mul, mul_comm 2 m]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClaimSOfNumbers
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShortEnd

theorem claimS_of_numbers : ∀ (T D δ d y e : ℕ) (n Λ β Λ₀ ΛD ΛT Hf H' dg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ δ → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ Λ₀ → 1 ≤ ΛD → 1 ≤ ΛT → (T - 1).choose D * δ + y ≤ d → ∀ b : ℕ, (D + 1) * b = (T - 1).choose D * (T + D * (D + 1)) → b * ((D + 1) * δ) + e = (T - 1).choose D * δ * T + y * (T - D) → -(cst n Λ * ((D + 1) * δ)) ≤ Hf → -(cst n Λ * e) ≤ H' → b * Hf + H' - (((T - 1).choose D * δ : ℕ) * Real.log (Real.sqrt β ^ T * Λ₀) + y * Real.log (Real.sqrt β ^ (T - D) * ΛD) + (d - (T - 1).choose D * δ - y : ℕ) * Real.log ΛT) ≤ dg → 0 < d ∧ ClaimS T D n Λ β Λ₀ ΛD ΛT δ (Hf / (((D : ℝ) + 1) * δ)) d dg := by
  intro T D δ d y e n Λ β Λ₀ ΛD ΛT Hf H' dg hD hDT hδ hn hΛ hβ hΛ₀ hΛD hΛT hd b hb he hHf hH' hdg
  have hDT' : D ≤ T - 1 := by omega
  have hR : 1 ≤ (T - 1).choose D := Nat.choose_pos hDT'
  set R := (T - 1).choose D with hRdef
  have hRδ : 1 ≤ R * δ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdpos : 0 < d := by omega
  refine ⟨hdpos, ?_⟩

  have hc : 0 ≤ cst n Λ := by
    unfold cst
    have h1 : 0 ≤ Real.log (n * Λ) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log n := Real.log_nonneg hn
    positivity
  set c := cst n Λ with hcdef

  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDTR : (D : ℝ) + 1 ≤ T := by exact_mod_cast hDT
  have hdR' : (R : ℝ) * δ + y ≤ d := by exact_mod_cast hd
  have hbR : ((D : ℝ) + 1) * b = R * (T + D * (D + 1)) := by exact_mod_cast hb
  have hTD : D ≤ T := by omega
  have heR : (b : ℝ) * ((D + 1) * δ) + e = R * δ * T + y * ((T : ℝ) - D) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) he
    push_cast [Nat.cast_sub hTD] at this
    linarith
  have hsub : ((d - R * δ - y : ℕ) : ℝ) = d - R * δ - y := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsubTD : ((T - D : ℕ) : ℝ) = T - D := by rw [Nat.cast_sub hTD]

  have hβ0 : 0 < β := by linarith
  have hsq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hlb : Real.log (Real.sqrt β) = Real.log β / 2 := Real.log_sqrt hβ0.le
  have hL0 : Real.log (Real.sqrt β ^ T * Λ₀) = T * (Real.log β / 2) + Real.log Λ₀ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb]
  have hLD : Real.log (Real.sqrt β ^ (T - D) * ΛD) = ((T : ℝ) - D) * (Real.log β / 2) + Real.log ΛD := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb, hsubTD]
  have lβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have lD : 0 ≤ Real.log ΛD := Real.log_nonneg hΛD
  have lT : 0 ≤ Real.log ΛT := Real.log_nonneg hΛT
  have l0 : 0 ≤ Real.log Λ₀ := Real.log_nonneg hΛ₀
  rw [hL0, hLD, hsub] at hdg
  push_cast at hdg

  set h := Hf / (((D : ℝ) + 1) * δ) with hhdef
  have hpos : (0 : ℝ) < ((D : ℝ) + 1) * δ := by positivity
  have hHfh : Hf = ((D : ℝ) + 1) * δ * h := by rw [hhdef]; field_simp
  have hh : -c ≤ h := by
    rw [hhdef, le_div_iff₀ hpos]; linarith
  have hbHf : (b : ℝ) * Hf = R * δ * (T + D * (D + 1)) * h := by
    rw [hHfh]
    calc (b : ℝ) * (((D : ℝ) + 1) * δ * h) = (((D : ℝ) + 1) * b) * δ * h := by ring
      _ = _ := by rw [hbR]; ring

  have he2 : (e : ℝ) = y * ((T : ℝ) - D) - R * δ * (D * (D + 1)) := by
    have : (b : ℝ) * ((D + 1) * δ) = R * δ * (T + D * (D + 1)) := by
      calc (b : ℝ) * ((D + 1) * δ) = (((D : ℝ) + 1) * b) * δ := by ring
        _ = _ := by rw [hbR]; ring
    linarith
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hRδ0 : (0 : ℝ) ≤ R * δ := by positivity
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDD : (0 : ℝ) ≤ D * (D + 1) := by positivity
  have heT : (e : ℝ) ≤ T * (d - R * δ) := by
    rw [he2]
    linarith [mul_nonneg hRδ0 hDD, mul_nonneg hy0 hD0, mul_nonneg (sub_nonneg.mpr hdR') hT0]
  have hce : c * e ≤ c * (T * (d - R * δ)) := mul_le_mul_of_nonneg_left heT hc
  have hch : R * δ * (D * (D + 1)) * (-c) ≤ R * δ * (D * (D + 1)) * h :=
    mul_le_mul_of_nonneg_left hh (mul_nonneg hRδ0 hDD)
  have hX : 0 ≤ (d - R * δ - y) * (T * (Real.log β / 2) + Real.log ΛD) := by
    apply mul_nonneg (by linarith); positivity
  have hyD : 0 ≤ (y : ℝ) * D * Real.log β := by positivity
  have hyT : 0 ≤ (y : ℝ) * Real.log ΛT := by positivity
  have key : (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ dg := by
    linarith [hbHf, hce, hch, hX, hyD, hyT, hdg, hH']
  unfold ClaimS
  have hρ0 : (0 : ℝ) ≤ R * δ / d := div_nonneg hRδ0 hdR.le
  have hρ1 : (R : ℝ) * δ / d ≤ 1 := by rw [div_le_one hdR]; linarith
  refine ⟨by push_cast; linarith, by push_cast; linarith, ?_⟩
  rw [le_div_iff₀ hdR]
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have expand : ((1 - (1 - ((R : ℕ) : ℝ) * δ / d)) * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((R : ℕ) : ℝ) * δ / d) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT)) * d =
      (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) := by
    field_simp
    ring
  push_cast at expand ⊢
  rw [expand]; exact key

end GlobalTheory.HSShortEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffDetMemSpanDetIntegralPolynomialVectors
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetCoeff

theorem prod_monomial_eq {τ R ι : Type} [CommSemiring R] (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, ih, monomial_mul, Finset.sum_insert hj, Finset.prod_insert hj]

open Classical in
theorem coeff_det_eq {F τ : Type} [Field F] {d : ℕ} (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F))
    (s : Finset (τ →₀ ℕ)) (hs : ∀ i k, (P i k).support ⊆ s) (m : τ →₀ ℕ) :
    AddMonoidAlgebra.coeff P.det m = ∑ g ∈ Fintype.piFinset (fun _ : Fin d => s),
      if ∑ k, g k = m then (Matrix.of fun i k => AddMonoidAlgebra.coeff (P i k) (g k)).det else 0 := by
  classical
  have hP : ∀ i k, P i k = ∑ n ∈ s, monomial n (AddMonoidAlgebra.coeff (P i k) n) := by
    intro i k
    conv_lhs => rw [(P i k).as_sum]
    exact Finset.sum_subset (hs i k) (fun n _ hn => by simp [MvPolynomial.notMem_support_iff.mp hn])
  have hprod : ∀ σ : Equiv.Perm (Fin d), ∏ k, P (σ k) k = ∑ g ∈ Fintype.piFinset (fun _ : Fin d => s),
      monomial (∑ k, g k) (∏ k, AddMonoidAlgebra.coeff (P (σ k) k) (g k)) := by
    intro σ
    rw [Finset.prod_congr rfl (fun k _ => hP (σ k) k), Finset.prod_univ_sum]
    exact Finset.sum_congr rfl (fun g _ => prod_monomial_eq _ _ _)
  rw [Matrix.det_apply]
  simp_rw [hprod, Finset.smul_sum, coeff_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Matrix.det_apply]
  split_ifs with h
  · subst h
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Units.smul_def, coeff_smul, coeff_monomial, if_pos rfl]
    rfl
  · refine Finset.sum_eq_zero (fun σ _ => ?_)
    simp only [Units.smul_def, coeff_smul, coeff_monomial, if_neg h, smul_zero]

end GlobalTheory.DetCoeff

namespace GlobalTheory.DetCoeff

theorem coeff_det_mem_span_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V) (τ : Type) (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F)), (∀ k m, ∑ i, AddMonoidAlgebra.coeff (P i k) m • b i ∈ M) → ∀ m, AddMonoidAlgebra.coeff P.det m ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ M d b τ P hP m
  classical
  have hs : ∀ i k, (P i k).support ⊆ Finset.univ.biUnion (fun ik : Fin d × Fin d => (P ik.1 ik.2).support) :=
    fun i k => Finset.subset_biUnion_of_mem (fun ik : Fin d × Fin d => (P ik.1 ik.2).support) (Finset.mem_univ (i, k))
  rw [coeff_det_eq P _ hs m]
  refine Submodule.sum_mem _ (fun g _ => ?_)
  split_ifs
  · apply Submodule.subset_span
    refine ⟨fun k => ∑ i, AddMonoidAlgebra.coeff (P i k) (g k) • b i, fun k => hP k (g k), ?_⟩
    rw [Module.Basis.det_apply]
    congr 1
    ext i k
    simp [Module.Basis.toMatrix_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  · exact Submodule.zero_mem _

end GlobalTheory.DetCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLeOfBounded
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFloor

theorem coeff_le_of_bounded {E : Type} [Field E] {σ : Type} [Fintype σ] (k : MvPolynomial σ E)
    (s : E →+* ℂ) (B : ℝ) (hB : ∀ z : σ → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B) (m : σ →₀ ℕ) :
    ‖s (k.coeff m)‖ ≤ B := by

  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality σ (MvPolynomial.map s k)).2 m
  have hz : ∀ i, ‖ReciprocityTheory.MultiplicativeHeights.torusPoint θ i‖ ≤ 1 := by
    intro i
    simp [ReciprocityTheory.MultiplicativeHeights.torusPoint, Complex.norm_exp]
  rw [MvPolynomial.coeff_map, MvPolynomial.eval_map] at hθ
  exact hθ.trans (hB _ hz)

theorem floor : ∀ (E : Type) [Field E] [NumberField E] (σ : Type) [Fintype σ] (k : MvPolynomial σ E)
    (B : (E →+* ℂ) → ℝ), k ≠ 0 →
    (∀ (s : E →+* ℂ) (z : σ → ℂ), (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B s) →
    -mean E (fun s => Real.log (B s)) ≤ finPart k := by
  intro E _ _ σ _ k B hk hB
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
  refine le_trans (b := -mean E (fun s => Real.log ‖s (k.coeff m)‖)) ?_
    ((GlobalTheory.HSFinPart.finPart_props E σ σ).2.2 k m hm)
  rw [neg_le_neg_iff]
  unfold mean
  gcongr with τ _

  have hpos : 0 < ‖τ (k.coeff m)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hm)
  exact Real.log_le_log hpos (coeff_le_of_bounded k τ (B τ) (hB τ) m)

end GlobalTheory.HSFloor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.ConjSch

open scoped Classical

noncomputable def conjSch {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := (Complex.conjLIE.toContinuousLinearEquiv.contDiff).comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => star (f x)) = Complex.conjLIE ∘ f := rfl
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSch_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSch f x = star (f x) := rfl

theorem star_mem_schA {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨conjSch f, fun y => star (g y),
      ⟨hg.1.comp _, hg.2.comp_left (g := star) (star_zero _)⟩, ?_⟩
    funext y
    simp only [pureA, conjSch_apply, star_mul', mul_comm]
  | zero =>
    simp only [Pi.zero_apply, star_zero]
    exact (schA F κ).zero_mem
  | add x y _ _ hx hy =>
    have := (schA F κ).add_mem hx hy
    convert this using 1
    funext z; simp
  | smul c x _ hx =>
    have := (schA F κ).smul_mem (star c) hx
    convert this using 1
    funext z; simp [star_mul', mul_comm]

end GlobalTheory.ConjSch

theorem GlobalTheory.star_mem_schA_main : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ :=
  fun κ _ => GlobalTheory.ConjSch.star_mem_schA κ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZeroStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA h h0
  exact GlobalTheory.constant_one_mem_cuspForms_of_wittIndex_zero (B := B) (sA := sA) (sB := sB) (t := t) h h0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariation
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.CuspRep

theorem norm_le_of_unip_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a),
    IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ),
      (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  intro E _ _ _ a ψ hψ s hs0 hsa g e he
  letI : MeasurableSpace (BlockIx a s → Ad E) := borel _
  haveI : BorelSpace (BlockIx a s → Ad E) := ⟨rfl⟩
  set μ : Measure (BlockIx a s → Ad E) := Measure.addHaar with hμ
  obtain ⟨𝓕, h𝓕, h0, htop⟩ := _root_.GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN E a s μ
  have hc := ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  have hI := CuspidalL2GL.integrableOn_unip hc hψ.1.left μ h𝓕 g
  have hz : ∫ x in 𝓕, ψ.1 (unip x * g) ∂μ = 0 := hψ.2 s hs0 hsa μ 𝓕 inferInstance h𝓕 g
  have key : ∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ = μ.real 𝓕 • ψ.1 g := by
    have h1 : IntegrableOn (fun _ => ψ.1 g) 𝓕 μ := integrableOn_const htop.ne
    rw [integral_sub h1 hI, hz, setIntegral_const, sub_zero]
  have hb : ‖∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ‖ ≤ e * μ.real 𝓕 :=
    norm_setIntegral_le_of_norm_le_const htop fun x _ => by rw [norm_sub_rev]; exact he x
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, mul_comm] at hb
  have hpos : 0 < μ.real 𝓕 := ENNReal.toReal_pos h0 htop.ne
  exact le_of_mul_le_mul_right hb hpos

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangianStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_integral_invariant_form_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  first | exact @GlobalTheory.RealLift.diagLagr_invForm | exact GlobalTheory.RealLift.diagLagr_invForm | (intros; apply GlobalTheory.RealLift.diagLagr_invForm <;> assumption)
end

