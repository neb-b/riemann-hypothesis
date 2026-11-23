module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DiagonalOnSubgroupOfConjugate
section
open Matrix UpperTheory.V

private theorem diagonal_on_subgroup_from_equations {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (W : Γ →* GL (Fin 2) k)
    (Ψ : Γ →* kˣ) (a b c d : k) (hdet : a * d - b * c ≠ 0)
    (h : ∀ g ∈ H, a * W g 0 0 + b * W g 1 0 = (Ψ g : k) * a ∧ a * W g 0 1 + b * W g 1 1 = (Ψ g : k) * b ∧
      c * W g 0 0 + d * W g 1 0 = (Ψ g : k)⁻¹ * c ∧ c * W g 0 1 + d * W g 1 1 = (Ψ g : k)⁻¹ * d) :
    Af.IsDiagOn W H ![Ψ, Ψ⁻¹] := by
  have hd : Matrix.det !![a, b; c, d] ≠ 0 := by rwa [Matrix.det_fin_two_of]
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 2) k, (P : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, rfl⟩
  refine ⟨P, fun t ht => ?_⟩
  have hPW : !![a, b; c, d] * (W t : Matrix (Fin 2) (Fin 2) k) =
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) * !![a, b; c, d] := by
    obtain ⟨h1, h2, h3, h4⟩ := h t ht
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h3
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h4
  rw [Units.val_mul, Units.val_mul, hP, hPW, Matrix.mul_assoc, ← hP, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

theorem UpperTheory.diagonal_on_subgroup_of_conjugate :
    ∀ {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ) (M : GL (Fin 3) k), (∀ g ∈ H, (M : Matrix (Fin 3) (Fin 3) k) * !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] = Matrix.diagonal ![(Ψ g : k), 1, (((Ψ g)⁻¹ : kˣ) : k)] * (M : Matrix (Fin 3) (Fin 3) k)) → Af.IsDiagOn W H ![Ψ, Ψ⁻¹] := by
  intro Γ k _ _ H W Ψ M hM
  have hMi : ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  by_cases htriv : ∀ g ∈ H, Ψ g = 1
  · refine ⟨1, fun t ht => ?_⟩
    have e := hM t ht
    have hD : Matrix.diagonal ![(Ψ t : k), 1, (((Ψ t)⁻¹ : kˣ) : k)] = 1 := by
      rw [htriv t ht]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hD, Matrix.one_mul] at e
    have hB : !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1] = (1 : Matrix (Fin 3) (Fin 3) k) := by
      calc _ = ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
            ((M : Matrix (Fin 3) (Fin 3) k) * !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1]) := by
            rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
        _ = 1 := by rw [e, hMi]
    have b00 := congrFun (congrFun hB 0) 0
    have b02 := congrFun (congrFun hB 0) 2
    have b20 := congrFun (congrFun hB 2) 0
    have b22 := congrFun (congrFun hB 2) 2
    simp at b00 b02 b20 b22
    rw [one_mul, inv_one, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [htriv t ht, b00, b02, b20, b22]
  · push_neg at htriv
    obtain ⟨g0, hg0, hne⟩ := htriv
    have e0 := hM g0 hg0
    have x01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = (Ψ g0 : k) * (M : Matrix (Fin 3) (Fin 3) k) 0 1 := by
      have := congrFun (congrFun e0 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have x21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 =
        (((Ψ g0)⁻¹ : kˣ) : k) * (M : Matrix (Fin 3) (Fin 3) k) 2 1 := by
      have := congrFun (congrFun e0 2) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have m01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 := by
      have : (M : Matrix (Fin 3) (Fin 3) k) 0 1 * (1 - (Ψ g0 : k)) = 0 := by linear_combination x01
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h).symm) hne
    have m21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
      have : (M : Matrix (Fin 3) (Fin 3) k) 2 1 * (1 - (((Ψ g0)⁻¹ : kˣ) : k)) = 0 := by
        linear_combination x21
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (inv_eq_one.mp (Units.val_eq_one.mp (sub_eq_zero.mp h).symm)) hne
    have hdetM : (M : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hMi
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have hdet : (M : Matrix (Fin 3) (Fin 3) k) 0 0 * (M : Matrix (Fin 3) (Fin 3) k) 2 2 -
        (M : Matrix (Fin 3) (Fin 3) k) 0 2 * (M : Matrix (Fin 3) (Fin 3) k) 2 0 ≠ 0 := by
      intro h0
      apply hdetM
      rw [Matrix.det_fin_three, m01, m21]
      linear_combination (M : Matrix (Fin 3) (Fin 3) k) 1 1 * h0
    refine diagonal_on_subgroup_from_equations H W Ψ _ _ _ _ hdet fun g hg => ⟨?_, ?_, ?_, ?_⟩
    · have := congrFun (congrFun (hM g hg) 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 0) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 2) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 2) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsDiagOnOfIsDiagOnInfKerSign
section
open Matrix UpperTheory.V

private theorem exists_char {Γ k : Type} [Group Γ] [Field k] (η : Γ →* ℤˣ) (Φ : Γ →* kˣ) (s : Γ) (hs : η s = -1)
    (x : k) (hx : x * x = (Φ s : k) * Φ s) :
    ∃ χ : Γ →* kˣ, (∀ g, η g = 1 → χ g = Φ g) ∧ (χ s : k) = x := by
  have hΦ : (Φ s : k) ≠ 0 := (Φ s).ne_zero
  have hsq : (x / Φ s) * (x / Φ s) = 1 := by
    rw [div_mul_div_comm, hx, div_self (mul_ne_zero hΦ hΦ)]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact ⟨Φ, fun g _ => rfl, ((div_eq_one_iff_eq hΦ).mp h).symm⟩
  · refine ⟨Φ * (Units.map (Int.castRingHom k).toMonoidHom).comp η, fun g hg => by simp [hg], ?_⟩
    rw [div_eq_iff hΦ] at h
    simp [hs, h]

private theorem diag_sq {k : Type} [Field k] [CharZero k] (S : Matrix (Fin 2) (Fin 2) k) (a : k) (ha : a ≠ 0)
    (hS : S * S = Matrix.diagonal fun _ => a * a) :
    ∃ (P : GL (Fin 2) k) (x : Fin 2 → k), (∀ i, x i * x i = a * a) ∧
      (P : Matrix (Fin 2) (Fin 2) k) * S = Matrix.diagonal x * P := by
  have e : ∀ i j, (S * S) i j = (Matrix.diagonal fun _ : Fin 2 => a * a) i j := fun i j => by rw [hS]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at e00 e01 e10 e11
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  by_cases hr : S 1 0 = 0
  · by_cases hq : S 0 1 = 0
    · refine ⟨1, ![S 0 0, S 1 1], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp
          linear_combination e00 - S 1 0 * hq
        · simp
          linear_combination e11 - S 0 1 * hr
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [hq, hr]
    · have ht : S 1 1 = -S 0 0 := by
        have : S 0 1 * (S 0 0 + S 1 1) = 0 := by linear_combination e01
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hq
        · linear_combination h
      have hp2 : S 0 0 * S 0 0 = a * a := by linear_combination e00 - S 0 1 * hr
      have hp : S 0 0 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hp2
        exact mul_ne_zero ha ha hp2.symm
      have hd : Matrix.det !![2 * S 0 0, S 0 1; 0, 1] ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        simpa using mul_ne_zero h2 hp
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ![S 0 0, -S 0 0], ?_, ?_⟩
      · intro i
        fin_cases i <;> simpa using hp2
      · show !![2 * S 0 0, S 0 1; 0, 1] * S = Matrix.diagonal ![S 0 0, -S 0 0] * !![2 * S 0 0, S 0 1; 0, 1]
        ext i j
        fin_cases i <;> fin_cases j
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination S 0 1 * hr
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination S 0 1 * ht
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination hr
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination ht
  · have ht : S 1 1 = -S 0 0 := by
      have : S 1 0 * (S 0 0 + S 1 1) = 0 := by linear_combination e10
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hr
      · linear_combination h
    have hd : Matrix.det !![S 1 0, a - S 0 0; S 1 0, -a - S 0 0] ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      have : S 1 0 * (-a - S 0 0) - (a - S 0 0) * S 1 0 = -(2 * (a * S 1 0)) := by ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero h2 (mul_ne_zero ha hr)
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ![a, -a], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · show !![S 1 0, a - S 0 0; S 1 0, -a - S 0 0] * S = Matrix.diagonal ![a, -a] * !![S 1 0, a - S 0 0; S 1 0, -a - S 0 0]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination e00 + (a - S 0 0) * ht
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination e00 + (-a - S 0 0) * ht

private theorem diag_ext {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (η : Γ →* ℤˣ) (W : Γ →* GL (Fin 2) k)
    (χ : Fin 2 → Γ →* kˣ) (g : GL (Fin 2) k) (s : Γ) (hsH : s ∈ H) (hs : η s = -1)
    (h0 : ∀ t ∈ H, η t = 1 → ((g * W t * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.diagonal fun i => (χ i t : k))
    (h1 : ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = Matrix.diagonal fun i => (χ i s : k)) :
    Af.IsDiagOn W H χ := by
  refine ⟨g, fun t ht => ?_⟩
  rcases Int.units_eq_one_or (η t) with h | h
  · exact h0 t ht h
  · have hu : s⁻¹ * t ∈ H := H.mul_mem (H.inv_mem hsH) ht
    have hη : η (s⁻¹ * t) = 1 := by simp [hs, h]
    have key : g * W t * g⁻¹ = (g * W s * g⁻¹) * (g * W (s⁻¹ * t) * g⁻¹) := by
      rw [map_mul, map_inv]; group
    rw [key, Units.val_mul, h1, h0 _ hu hη, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]

theorem UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign :
    ∀ {Γ k : Type} [Group Γ] [Field k] [CharZero k] (H : Subgroup Γ) (η : Γ →* ℤˣ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ), Af.IsDiagOn W (H ⊓ η.ker) ![Ψ, Ψ⁻¹] → ∃ χ : Fin 2 → Γ →* kˣ, (∀ i g, Ψ g = 1 → η g = 1 → χ i g = 1) ∧ Af.IsDiagOn W H χ := by
  intro Γ k _ _ _ H η W Ψ hD
  obtain ⟨g, hg⟩ := hD
  by_cases hex : ∃ s ∈ H, η s = -1
  swap
  · push_neg at hex
    refine ⟨![Ψ, Ψ⁻¹], ?_, g, fun t ht => hg t ⟨ht, MonoidHom.mem_ker.mpr ?_⟩⟩
    · intro i x hΨ _
      fin_cases i <;> simp [hΨ]
    · rcases Int.units_eq_one_or (η t) with h | h
      · exact h
      · exact absurd h (hex t ht)
  obtain ⟨s, hsH, hs⟩ := hex
  have hmul : ∀ a b : Γ, ((g * W (a * b) * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ((g * W a * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g * W b * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    intro a b
    rw [← Units.val_mul, map_mul]
    congr 1
    group
  have hconj : ∀ (φ : Γ →* kˣ) (t : Γ), φ (s * t * s⁻¹) = φ t := by
    intro φ t
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  have hmemk : ∀ t, t ∈ H ⊓ η.ker ↔ t ∈ H ∧ η t = 1 := fun t => by
    simp [Subgroup.mem_inf, MonoidHom.mem_ker]
  have hss : s * s ∈ H ⊓ η.ker := (hmemk _).mpr ⟨H.mul_mem hsH hsH, by rw [map_mul, hs]; decide⟩
  have hcomm : ∀ t ∈ H ⊓ η.ker, ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) =
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) *
        ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    intro t ht
    obtain ⟨htH, htk⟩ := (hmemk t).mp ht
    have hm : s * t * s⁻¹ ∈ H ⊓ η.ker :=
      (hmemk _).mpr ⟨H.mul_mem (H.mul_mem hsH htH) (H.inv_mem hsH), by simp [htk]⟩
    have e2 := hg _ hm
    simp only [hconj] at e2
    conv_rhs => rw [← e2]
    rw [← hg t ht, ← hmul, ← hmul, inv_mul_cancel_right]
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) k,
      ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = S := ⟨_, rfl⟩
  have hSS : S * S = Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i (s * s) : kˣ) : k)) := by
    rw [← hS, ← hmul, hg _ hss]
  by_cases hdist : ∃ t ∈ H ⊓ η.ker, ((Ψ t : kˣ) : k) ≠ (((Ψ⁻¹) t : kˣ) : k)
  · obtain ⟨t0, ht0, hne⟩ := hdist
    have hc := hcomm t0 ht0
    rw [hS] at hc
    have c01 := congrFun (congrFun hc 0) 1
    have c10 := congrFun (congrFun hc 1) 0
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at c01 c10
    have h01 : S 0 1 = 0 := by
      have : S 0 1 * (((Ψ t0 : kˣ) : k) - (((Ψ⁻¹) t0 : kˣ) : k)) = 0 := by linear_combination -c01
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have h10 : S 1 0 = 0 := by
      have : S 1 0 * (((Ψ t0 : kˣ) : k) - (((Ψ⁻¹) t0 : kˣ) : k)) = 0 := by linear_combination c10
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have d0 := congrFun (congrFun hSS 0) 0
    have d1 := congrFun (congrFun hSS 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply_eq, h01, h10, mul_zero,
      add_zero, zero_mul, zero_add, map_mul, Units.val_mul] at d0 d1
    have hxi : ∀ i, S i i * S i i = ((![Ψ, Ψ⁻¹] i s : kˣ) : k) * ((![Ψ, Ψ⁻¹] i s : kˣ) : k) := by
      intro i
      fin_cases i
      · exact d0
      · exact d1
    choose χ hχ1 hχ2 using fun i => exists_char η (![Ψ, Ψ⁻¹] i) s hs (S i i) (hxi i)
    refine ⟨χ, ?_, diag_ext H η W χ g s hsH hs ?_ ?_⟩
    · intro i x hΨ hη
      rw [hχ1 i x hη]
      fin_cases i <;> simp [hΨ]
    · intro t htH htη
      rw [hg t ((hmemk t).mpr ⟨htH, htη⟩)]
      congr 1
      funext i
      rw [hχ1 i t htη]
    · rw [hS]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hχ2, h01, h10]
  · push_neg at hdist
    have hDt : ∀ t ∈ H ⊓ η.ker, Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) =
        Matrix.diagonal (fun _ => ((Ψ t : kˣ) : k)) := by
      intro t ht
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact (hdist t ht).symm
    have hSS' : S * S = Matrix.diagonal (fun _ => ((Ψ s : kˣ) : k) * ((Ψ s : kˣ) : k)) := by
      rw [hSS, hDt _ hss, map_mul, Units.val_mul]
    obtain ⟨P, x, hx, hP⟩ := diag_sq S _ (Ψ s).ne_zero hSS'
    choose χ hχ1 hχ2 using fun i => exists_char η Ψ s hs (x i) (hx i)
    have hconjP : ∀ t, (((P * g) * W t * (P * g)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
        (P : Matrix (Fin 2) (Fin 2) k) * ((g * W t * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
          ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
      intro t
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have hPinv : (P : Matrix (Fin 2) (Fin 2) k) * ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨χ, ?_, diag_ext H η W χ (P * g) s hsH hs ?_ ?_⟩
    · intro i y hΨ hη
      rw [hχ1 i y hη, hΨ]
    · intro t htH htη
      have ht : t ∈ H ⊓ η.ker := (hmemk t).mpr ⟨htH, htη⟩
      have hsc : (P : Matrix (Fin 2) (Fin 2) k) * Matrix.diagonal (fun _ => ((Ψ t : kˣ) : k)) =
          Matrix.diagonal (fun _ => ((Ψ t : kˣ) : k)) * (P : Matrix (Fin 2) (Fin 2) k) := by
        ext i j
        simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
      rw [hconjP, hg t ht, hDt t ht, hsc, mul_assoc, hPinv, mul_one]
      congr 1
      funext i
      rw [hχ1 i t htη]
    · rw [hconjP, hS, hP, mul_assoc, hPinv, mul_one]
      congr 1
      funext i
      rw [hχ2 i]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsFlagOnOfEigenvectorNormalSubgroup
section
open Matrix UpperTheory.V

private theorem UpperTheory.exists_gl2_first_column {k : Type} [Field k] (v : Fin 2 → k) (hv : v ≠ 0) :
    ∃ h : GL (Fin 2) k, ∀ i, (h : Matrix (Fin 2) (Fin 2) k) i 0 = v i := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro i
    fin_cases i <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro i
    fin_cases i <;> rfl

private theorem UpperTheory.upper_triangular_characters {Γ k : Type} [Group Γ] [Field k] (D I : Subgroup Γ)
    (r : Γ →* Matrix (Fin 2) (Fin 2) k) (Ψ : Γ →* kˣ)
    (hn : ∀ d ∈ D, ∀ s ∈ I, d⁻¹ * s * d ∈ I)
    (h00 : ∀ s ∈ I, r s 0 0 = Ψ s) (h10 : ∀ s ∈ I, r s 1 0 = 0)
    (hdet : ∀ s ∈ I, (r s).det = 1) (hex : ∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) :
    ∃ κ : Fin 2 → ↥D →* kˣ, (∀ s : ↥D, (∀ i j, j < i → r s i j = 0) ∧ ∀ i, r s i i = (κ i s : k)) ∧
      ∀ s : ↥D, (s : Γ) ∈ I → κ 0 s = Ψ s ∧ κ 1 s = (Ψ s)⁻¹ := by
  have r11 : ∀ s ∈ I, r s 1 1 = ((Ψ s)⁻¹ : kˣ) := by
    intro s hs
    have hd := hdet s hs
    rw [Matrix.det_fin_two, h00 s hs, h10 s hs, mul_zero, sub_zero] at hd
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hd
  obtain ⟨s0, hs0, ha⟩ := hex
  have hane : (Ψ s0 : k) - (Ψ s0 : k)⁻¹ ≠ 0 := by
    intro h
    apply ha
    rw [sub_eq_zero] at h
    calc (Ψ s0 : k) ^ 2 = (Ψ s0 : k) * (Ψ s0 : k)⁻¹ := by rw [sq]; nth_rewrite 2 [h]; rfl
      _ = 1 := mul_inv_cancel₀ (Ψ s0).ne_zero
  have low : ∀ d ∈ D, r d 1 0 = 0 := by
    intro d hd
    have ht : d⁻¹ * s0 * d ∈ I := hn d hd s0 hs0
    have hΨ : Ψ (d⁻¹ * s0 * d) = Ψ s0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    have hm : r s0 * r d = r d * r (d⁻¹ * s0 * d) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have key := congrArg (fun M => M 1 0) hm
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at key
    rw [h10 s0 hs0, r11 s0 hs0, h10 _ ht, h00 _ ht, hΨ, Units.val_inv_eq_inv_val] at key
    have : r d 1 0 * ((Ψ s0 : k) - (Ψ s0 : k)⁻¹) = 0 := by
      rw [mul_sub]
      linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hane
  have diag : ∀ d ∈ D, ∀ e ∈ D, ∀ i, r (d * e) i i = r d i i * r e i i := by
    intro d hd e he i
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i
    · simp [low e he]
    · simp [low d hd]
  let f : Fin 2 → ↥D →* k := fun i =>
    { toFun := fun d => r d i i
      map_one' := by simp
      map_mul' := fun d e => diag _ d.2 _ e.2 i }
  refine ⟨fun i => (f i).toHomUnits, ?_, ?_⟩
  · intro s
    refine ⟨?_, fun i => rfl⟩
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact low s s.2
    · exact absurd hij (by decide)
  · intro s hs
    constructor
    · ext
      exact h00 _ hs
    · ext
      exact r11 _ hs

theorem UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup :
    ∀ {Γ k : Type} [Group Γ] [Field k] (D I : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ) (v : Fin 2 → k), (∀ d ∈ D, ∀ s ∈ I, d⁻¹ * s * d ∈ I) → v ≠ 0 → (∀ s ∈ I, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = (Ψ s : k) • v) → (∀ s ∈ I, (W s : Matrix (Fin 2) (Fin 2) k).det = 1) → (∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) → ∃ κ : Fin 2 → ↥D →* kˣ, Af.IsFlagOn W D κ ∧ ∀ s : ↥D, (s : Γ) ∈ I → κ 0 s = Ψ s ∧ κ 1 s = (Ψ s)⁻¹ := by
  intro Γ k _ _ D I W Ψ v hn hv heig hdet hex
  obtain ⟨h, hh⟩ := UpperTheory.exists_gl2_first_column v hv
  have hcol : (h : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = v := by
    rw [Matrix.mulVec_single_one]
    funext i
    exact hh i
  have hinv : ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let r : Γ →* Matrix (Fin 2) (Fin 2) k := (Units.coeHom _).comp ((MulAut.conj h⁻¹).toMonoidHom.comp W)
  have hr2 : ∀ s, r s = ((h⁻¹ * W s * h⁻¹⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := fun s => rfl
  have hr : ∀ s, r s = ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (W s : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) := by
    intro s
    rw [hr2, inv_inv, Units.val_mul, Units.val_mul]
  have hcol' : ∀ s ∈ I, r s *ᵥ Pi.single 0 1 = (Ψ s : k) • (Pi.single 0 1 : Fin 2 → k) := by
    intro s hs
    rw [hr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, heig s hs, Matrix.mulVec_smul, ← hcol,
      Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h00 : ∀ s ∈ I, r s 0 0 = Ψ s := by
    intro s hs
    have := congrFun (hcol' s hs) 0
    simpa [Matrix.mulVec_single_one] using this
  have h10 : ∀ s ∈ I, r s 1 0 = 0 := by
    intro s hs
    have := congrFun (hcol' s hs) 1
    simpa [Matrix.mulVec_single_one] using this
  have hdet' : ∀ s ∈ I, (r s).det = 1 := by
    intro s hs
    rw [hr, Matrix.det_mul, Matrix.det_mul, hdet s hs, mul_one, ← Matrix.det_mul, hinv, Matrix.det_one]
  obtain ⟨κ, hκ, hI⟩ := UpperTheory.upper_triangular_characters D I r Ψ hn h00 h10 hdet' hex
  exact ⟨κ, ⟨h⁻¹, hκ⟩, hI⟩
end

