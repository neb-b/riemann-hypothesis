module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasis
section
open Matrix

namespace GlobalTheory.CompanionTheory.Flag

theorem exists_frame_extension {n D : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (h1 : Cᴴ * C = 1)
    (U : Submodule ℂ (Fin n → ℂ)) (hU : ∀ v, C *ᵥ v ∈ U) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ Cᴴ * B = 0 ∧
      ∀ y, y ∈ U ↔ ∃ u w, y = C *ᵥ u + B *ᵥ w := by
  classical
  let W' : Submodule ℂ (Fin n → ℂ) := U ⊓ LinearMap.ker (Matrix.mulVecLin Cᴴ)
  obtain ⟨r, B, hB1, hBW⟩ := GlobalTheory.IsoTorus.exists_frame W'
  have hmemW' : ∀ y, y ∈ W' ↔ y ∈ U ∧ Cᴴ *ᵥ y = 0 := fun y => by
    simp [W', Submodule.mem_inf]
  have hBin : ∀ w, B *ᵥ w ∈ W' := fun w => (hBW _).mpr (by
    rw [Matrix.mulVec_mulVec w (B * Bᴴ) B, Matrix.mul_assoc, hB1, Matrix.mul_one])
  have hCB : Cᴴ * B = 0 := by
    ext i j
    have h := congrFun ((hmemW' _).mp (hBin (Pi.single j 1))).2 i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa using h
  refine ⟨r, B, hB1, hCB, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨z, hzdef⟩ : ∃ z, z = y - C *ᵥ (Cᴴ *ᵥ y) := ⟨_, rfl⟩
    have hCC : Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ y)) = Cᴴ *ᵥ y := by
      rw [Matrix.mulVec_mulVec (Cᴴ *ᵥ y) Cᴴ C, h1, Matrix.one_mulVec]
    have hz : z ∈ W' := (hmemW' z).mpr ⟨hzdef ▸ U.sub_mem hy (hU _), by
      rw [hzdef, Matrix.mulVec_sub, hCC, sub_self]⟩
    have hz' := (hBW z).mp hz
    refine ⟨Cᴴ *ᵥ y, Bᴴ *ᵥ z, ?_⟩
    rw [Matrix.mulVec_mulVec z B Bᴴ, hz', hzdef]
    abel
  · rintro ⟨u, w, rfl⟩
    exact U.add_mem (hU u) ((hmemW' _).mp (hBin w)).1

private theorem append_cols_mulVec_eq_add {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (v : Fin (D + r) → ℂ) :
    (Matrix.of fun i => Fin.append (C i) (B i)) *ᵥ v =
      C *ᵥ (fun j => v (Fin.castAdd r j)) + B *ᵥ (fun j => v (Fin.natAdd D j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

private theorem append_cols_conjTranspose_mul_eq_one {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (h1 : Cᴴ * C = 1) (h2 : Bᴴ * B = 1) (h3 : Cᴴ * B = 0) :
    (Matrix.of fun i => Fin.append (C i) (B i))ᴴ * (Matrix.of fun i => Fin.append (C i) (B i)) = 1 := by
  have h4 : Bᴴ * C = 0 := by simpa using congrArg Matrix.conjTranspose h3
  ext c c'
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;> refine Fin.addCases (fun j' => ?_) (fun j' => ?_) c'
  · have h := congrFun (congrFun h1 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · have hne : Fin.castAdd r j ≠ Fin.natAdd D j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h3 j) j'
    simpa [Matrix.mul_apply] using h
  · have hne : Fin.natAdd D j ≠ Fin.castAdd r j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h4 j) j'
    simpa [Matrix.mul_apply] using h
  · have h := congrFun (congrFun h2 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem exists_flag_frame : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧
      Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  intro n a
  induction a with
  | zero =>
    intro W hW0 _
    refine ⟨0, 0, fun _ => 0, ?_, fun x _ _ => x.elim0, fun c => c.elim0, fun i y => ?_⟩
    · ext i j
      exact i.elim0
    · have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      rw [hW0, Submodule.mem_bot]
      constructor
      · rintro rfl
        exact ⟨0, by simp, fun c => c.elim0⟩
      · rintro ⟨v, rfl, -⟩
        simp
  | succ a ih =>
    intro W hW0 hWm
    obtain ⟨D, C, τ, hC1, hτm, hτa, hCW⟩ := ih (fun i => W i.castSucc) (by simpa using hW0)
      (fun i j hij => hWm (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hU : ∀ v, C *ᵥ v ∈ W (Fin.last (a + 1)) := fun v =>
      hWm (Fin.castSucc_lt_last (Fin.last a)).le
        ((hCW (Fin.last a) _).mpr ⟨v, rfl, fun c h => absurd h (not_le.mpr (hτa c))⟩)
    obtain ⟨r, B, hB1, hCB, hBU⟩ := exists_frame_extension C hC1 (W (Fin.last (a + 1))) hU
    refine ⟨D + r, Matrix.of fun i => Fin.append (C i) (B i), Fin.append τ (fun _ => a),
      append_cols_conjTranspose_mul_eq_one C B hC1 hB1 hCB, ?_, ?_, ?_⟩
    · intro c c' hcc'
      induction c using Fin.addCases with
      | left j =>
        induction c' using Fin.addCases with
        | left j' =>
          simp only [Fin.append_left]
          exact hτm (Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hcc'))
        | right j' =>
          simp only [Fin.append_left, Fin.append_right]
          exact (hτa j).le
      | right j =>
        induction c' using Fin.addCases with
        | left j' =>
          exfalso
          have h := Fin.le_iff_val_le_val.mp hcc'
          have := j'.isLt
          simp at h
          omega
        | right j' =>
          simp only [Fin.append_right]
          exact le_refl _
    · intro c
      refine Fin.addCases (fun j => ?_) (fun j => ?_) c
      · simp only [Fin.append_left]
        exact (hτa j).trans (Nat.lt_succ_self a)
      · simp only [Fin.append_right]
        exact Nat.lt_succ_self a
    · intro i y
      induction i using Fin.lastCases with
      | last =>
        rw [hBU]
        constructor
        · rintro ⟨u, w, rfl⟩
          refine ⟨Fin.append u w, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp
          · exfalso
            revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro h
              simp only [Fin.append_left, Fin.val_last] at h
              have := hτa j
              omega
            · intro h
              simp only [Fin.append_right, Fin.val_last] at h
              omega
        · rintro ⟨v, rfl, -⟩
          exact ⟨_, _, append_cols_mulVec_eq_add C B v⟩
      | cast i' =>
        refine (hCW i' y).trans ?_
        constructor
        · rintro ⟨v, rfl, hv⟩
          refine ⟨Fin.append v 0, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
            rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, Matrix.mulVec_zero, add_zero]
          · revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro hc
              simp only [Fin.append_left, Fin.val_castSucc] at hc ⊢
              exact hv j hc
            · intro _
              simp
        · rintro ⟨v, rfl, hv⟩
          refine ⟨fun j => v (Fin.castAdd r j), ?_, fun c hc => hv (Fin.castAdd r c) (by simpa using hc)⟩
          rw [append_cols_mulVec_eq_add]
          have hz : (fun j => v (Fin.natAdd D j)) = 0 := funext fun j => hv _ (by
            have := i'.isLt
            simp only [Fin.append_right, Fin.val_castSucc]
            omega)
          rw [hz, Matrix.mulVec_zero, add_zero]

end GlobalTheory.CompanionTheory.Flag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FriedrichsFc

open UniformSpace (Completion)

theorem exists_extension {E F : Type} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : E →ₗ[ℂ] F) (hf : ∀ u, ‖f u‖ ≤ ‖u‖) :
    ∃ g : Completion E →L[ℂ] F, (∀ u : E, g (u : Completion E) = f u) ∧ ‖g‖ ≤ 1 := by
  let f' : E →L[ℂ] F := f.mkContinuous 1 (by simpa using hf)
  let e : E →L[ℂ] Completion E := UniformSpace.Completion.toComplL
  have hd : DenseRange e := UniformSpace.Completion.denseRange_coe
  have hu : IsUniformInducing e := UniformSpace.Completion.isUniformInducing_coe E
  have he : ∀ u : E, (f'.extend e) (u : Completion E) = f u := fun u => f'.extend_eq hd hu u
  refine ⟨f'.extend e, he, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [he, UniformSpace.Completion.norm_coe, one_mul]
    exact hf u

theorem norm_map_le {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ)
    (V V' : H →L[ℂ] H) (V₀ : E →ₗ[ℂ] E) (h1 : V' * V = 1)
    (hadj : ∀ u v, ⟪V u, v⟫_ℂ = ⟪u, V' v⟫_ℂ)
    (hι : ∀ u, V (ι u) = ι (V₀ u)) (hBV : ∀ u, B (V₀ u) = V (B u)) (u : E) :
    ‖V₀ u‖ ≤ ‖u‖ := by
  have key : ⟪V₀ u, V₀ u⟫_ℂ = ⟪u, u⟫_ℂ := by
    have h2 : V' (V (ι u)) = ι u := by
      have := congrArg (fun W : H →L[ℂ] H => W (ι u)) h1
      simpa using this
    rw [← hB, hBV, ← hι, hadj, h2, hB]
  have : ‖V₀ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this)

theorem exists_inverse_of_form {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ) (hι : ∀ u, ‖ι u‖ ≤ ‖u‖) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : E →ₗ[ℂ] E), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  obtain ⟨g, hg, hgn⟩ := exists_extension ι hι
  let S : H →L[ℂ] Completion E := ContinuousLinearMap.adjoint g
  have hSi : ∀ h c, ⟪S h, c⟫_ℂ = ⟪h, g c⟫_ℂ := fun h c =>
    ContinuousLinearMap.adjoint_inner_left g c h
  have hS : ∀ u : E, S (B u) = (u : Completion E) := by
    intro u
    refine ext_inner_right ℂ fun c => ?_
    rw [hSi]
    induction c using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih v => rw [hg, hB, UniformSpace.Completion.inner_coe]
  have hSn : ‖S‖ ≤ 1 := by
    have : ‖S‖ = ‖g‖ := by simp [S]
    rw [this]; exact hgn
  have hTpos : (g ∘L S).IsPositive := ContinuousLinearMap.isPositive_self_comp_adjoint g
  refine ⟨g ∘L S, hTpos.isSelfAdjoint, ?_, ?_, ?_⟩
  · calc ‖g ∘L S‖ ≤ ‖g‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · intro u
    simp only [ContinuousLinearMap.comp_apply]
    rw [hS, hg]
  · intro U U' U₀ U₀' hUU' hU'U hadj hι₀ hι₀' hB₀ hB₀'
    have hadj' : ∀ u v, ⟪U' u, v⟫_ℂ = ⟪u, U v⟫_ℂ := fun u v => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    let c : E →ₗ[ℂ] Completion E :=
      (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
    have hc : ∀ u : E, c u = (u : Completion E) := fun _ => rfl
    obtain ⟨U₁, hU₁, -⟩ := exists_extension (c ∘ₗ U₀) (fun u => by
      simpa [hc] using norm_map_le ι B hB U U' U₀ hU'U hadj hι₀ hB₀ u)
    obtain ⟨U₁', hU₁', -⟩ := exists_extension (c ∘ₗ U₀') (fun u => by
      simpa [hc] using norm_map_le ι B hB U' U U₀' hUU' hadj' hι₀' hB₀' u)
    have h1 : ∀ x, g (U₁ x) = U (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁, LinearMap.comp_apply, hc, hg, hg, hι₀]
    have h1' : ∀ x, g (U₁' x) = U' (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁', LinearMap.comp_apply, hc, hg, hg, hι₀']
    have h3 : ∀ a x, ⟪U₁ a, x⟫_ℂ = ⟪a, U₁' x⟫_ℂ := by
      intro a x
      induction a using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u =>
        induction x using UniformSpace.Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih v =>
          rw [hU₁, hU₁', LinearMap.comp_apply, LinearMap.comp_apply, hc, hc,
            UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
            ← hB, hB₀, hadj, hι₀', hB]
    have h4 : ∀ h, S (U h) = U₁ (S h) := by
      intro h
      refine ext_inner_right ℂ fun x => ?_
      rw [hSi, hadj, ← h1', ← hSi, h3]
    ext h
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [h4, h1]

theorem exists_inverse_of_coercive {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [AddCommGroup D] [Module ℂ D] (ι B : D →ₗ[ℂ] H)
    (hsym : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪ι u, B v⟫_ℂ)
    (hpos : ∀ u, ‖ι u‖ ^ 2 ≤ (⟪B u, ι u⟫_ℂ).re) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : D →ₗ[ℂ] D), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  letI core : PreInnerProductSpace.Core ℂ D :=
    { inner := fun u v => ⟪B u, ι v⟫_ℂ
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) ⟪B y, ι x⟫_ℂ = ⟪B x, ι y⟫_ℂ
        rw [inner_conj_symm, hsym]
      re_inner_nonneg := fun x => le_trans (sq_nonneg _) (hpos x)
      add_left := fun x y z => by
        show ⟪B (x + y), ι z⟫_ℂ = ⟪B x, ι z⟫_ℂ + ⟪B y, ι z⟫_ℂ
        rw [map_add (f := _), inner_add_left]
      smul_left := fun x y r => by
        show ⟪B (r • x), ι y⟫_ℂ = (starRingEnd ℂ) r * ⟪B x, ι y⟫_ℂ
        rw [map_smul, inner_smul_left] }
  letI sn : SeminormedAddCommGroup D := InnerProductSpace.Core.toSeminormedAddCommGroup (c := core)
  letI ips : InnerProductSpace ℂ D := InnerProductSpace.ofCore core
  have hι : ∀ u : D, ‖ι u‖ ≤ ‖u‖ := fun u => by
    have h : ‖u‖ ^ 2 = (⟪B u, ι u⟫_ℂ).re := @norm_sq_eq_re_inner ℂ D _ sn ips u
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h ▸ hpos u)
  exact exists_inverse_of_form ι B (fun _ _ => rfl) hι

theorem friedrichs : PositivityTheory.RgBcC.Fc.Friedrichs := by
  intro H _ _ _ D A hsym hpos
  obtain ⟨R, hR, hRn, hRA, hRU⟩ := exists_inverse_of_coercive (D := D) D.subtype A
    (fun x y => hsym x y) (fun x => hpos x)
  refine ⟨R, hR, hRn, fun x => hRA x, ?_⟩
  intro U hU1 hU2 hD hD'
  have lift : ∀ (V : H →L[ℂ] H), (∀ x : D, ∃ y : D, (y : H) = V x ∧ A y = V (A x)) →
      ∃ V₀ : D →ₗ[ℂ] D, (∀ u, V (D.subtype u) = D.subtype (V₀ u)) ∧ ∀ u, A (V₀ u) = V (A u) := by
    intro V hV
    have hmem : ∀ x : D, (V.toLinearMap ∘ₗ D.subtype) x ∈ D := fun x => by
      obtain ⟨y, hy, -⟩ := hV x
      simpa [← hy] using y.2
    refine ⟨LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem, fun u => rfl, fun u => ?_⟩
    obtain ⟨y, hy, hAy⟩ := hV u
    have : LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem u = y :=
      Subtype.ext (by simp [hy])
    rw [this, hAy]
  obtain ⟨U₀, h1, h2⟩ := lift U hD
  obtain ⟨U₀', h1', h2'⟩ := lift (ContinuousLinearMap.adjoint U) hD'
  exact hRU U (ContinuousLinearMap.adjoint U) U₀ U₀' hU2 hU1
    (fun u v => (ContinuousLinearMap.adjoint_inner_right U u v).symm) h1 h1' h2 h2'

end GlobalTheory.CompanionTheory.FriedrichsFc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralDoubleSum
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Sym

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_add Rd_smul differentiableAt_of_smooth Rd_contDiffOn isOpen_GLs)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Expand

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Expand

section Pairing

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrable_of_cpt (hL : LgFacts) {F : Mat n → ℂ} (hc : ContinuousOn F (GLs n)) (hF : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hF
  have hc' : Continuous fun y : G n => F y.val :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  refine hc'.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem cpt_inner_left {u v : Mat n → V} (hu : Cpt u) : Cpt fun y => ⟪u y, v y⟫_ℂ := by
  obtain ⟨R, hR⟩ := hu
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem integrable_inner (hL : LgFacts) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n))
    (hv : ContDiffOn ℝ ∞ v (GLs n)) (hc : Cpt fun y => ⟪u y, v y⟫_ℂ) :
    Integrable (fun y : G n => ⟪u y.val, v y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (F := fun y => ⟪u y, v y⟫_ℂ) (hu.inner ℂ hv).continuousOn hc

end Pairing

end GlobalTheory.CompanionTheory.WaveK.Sym
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZero
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem Rd_ofReal_eq {n : ℕ} {Ψ : Mat n → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (GLs n)) (X : Mat n)
    {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (Ψ z : ℂ)) y = ((Rr X Ψ y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Ψ y :=
    ((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
  have h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt
  simp only [Rd, Rr, h.fderiv]
  rfl

theorem integral_Rr_eq_zero : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  intro hR n _ _ μ _ Ψ hΨ hc X
  have hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hcf : Cpt (fun z => (Ψ z : ℂ)) := by
    obtain ⟨R, hR'⟩ := hc
    exact ⟨R, fun y hy h => by simp [hR' y hy h]⟩
  have h0 := (hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X
  have h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) =
      fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ) :=
    funext fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)
  rw [h1, integral_complex_ofReal] at h0
  exact Complex.ofReal_eq_zero.1 h0

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExists
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SmoothCut

theorem exists_smooth_antitone_cut :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧
      (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  have hanti : Antitone (fun x : ℝ => Real.smoothTransition (1 - x)) := fun a b hab =>
    Real.smoothTransition.monotone (by linarith)
  refine ⟨fun x => Real.smoothTransition (1 - x),
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id), ?_,
    fun x => Real.smoothTransition.nonneg _,
    fun x hx => Real.smoothTransition.one_of_one_le (by linarith),
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  intro x
  have hneg : Monotone (fun x : ℝ => -Real.smoothTransition (1 - x)) := fun a b hab =>
    neg_le_neg (hanti hab)
  have h := hneg.deriv_nonneg (x := x)
  rw [deriv.fun_neg] at h
  linarith

end GlobalTheory.CompanionTheory.SmoothCut
end

