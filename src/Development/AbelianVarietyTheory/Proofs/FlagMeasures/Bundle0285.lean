module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCount
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem finrank_le_card_of_isotropic {n : ℕ} (ε : Fin n → Bool) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) (b : Bool) :
    Module.finrank ℂ V ≤ (univ.filter fun a => ε a = b).card := by

  let f : V →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {a // ε a = b} → Fin n)) ∘ₗ V.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : ∀ a, ε a = b → (x : Fin n → ℂ) a = 0 := fun a ha => by
      simpa [f] using congrFun hx ⟨a, ha⟩
    have hterm : ∀ a, star ((x : Fin n → ℂ) a) * ((if ε a then (1 : ℂ) else -1) * (x : Fin n → ℂ) a)
        = (if b then (-1 : ℂ) else 1) * ((Complex.normSq ((x : Fin n → ℂ) a) : ℝ) : ℂ) := by
      intro a
      by_cases ha : ε a = b
      · simp [hx0 a ha]
      · have hb : ε a = !b := by cases h1 : ε a <;> cases b <;> simp_all
        rw [Complex.normSq_eq_conj_mul_self, hb]
        cases b <;> simp [Complex.star_def] <;> ring
    have h0 := hV x x.2
    simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, hterm,
      ← Finset.mul_sum] at h0
    have hc : (if b then (-1 : ℂ) else 1) ≠ 0 := by cases b <;> simp
    have hsum : (∑ a, Complex.normSq ((x : Fin n → ℂ) a) : ℝ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left hc
      exact_mod_cast this
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp hsum
    ext a
    simpa using hall a (Finset.mem_univ a)
  calc Module.finrank ℂ V ≤ Module.finrank ℂ ({a // ε a = b} → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card {a // ε a = b} := Module.finrank_fintype_fun_eq_card ℂ
    _ = (univ.filter fun a => ε a = b).card := Fintype.card_subtype _

private theorem finrank_last_eq_sum_of_finrank_succ {n : ℕ} : ∀ (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) →
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i := by
  intro a
  induction a with
  | zero =>
    intro j W h0 _
    simp [show Fin.last 0 = (0 : Fin 1) from rfl, h0]
  | succ a ih =>
    intro j W h0 hstep
    have hprev := ih (fun i => j i.castSucc) (fun i => W i.castSucc) (by simpa using h0)
      (fun i => by have hs := hstep i.castSucc; rw [Fin.succ_castSucc] at hs; exact hs)
    rw [Fin.sum_univ_castSucc, ← hprev, ← Fin.succ_last, hstep (Fin.last a)]

theorem finrank_last_eq_sum {n : ℕ} {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : IsIsoFlag ε j W) :
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i :=
  finrank_last_eq_sum_of_finrank_succ a j W h.1 h.2.2.1

private theorem sq_sum_eq_sum_sq_add_two_mul_sum_lt' {a : ℕ} (j : Fin a → ℕ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
  have split : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hsym : ∑ i, ∑ k, (if k < i then j i * j k else 0) = ∑ i, ∑ k, (if i < k then j i * j k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hexp : ∑ i, ∑ k, j i * j k = ∑ i, ∑ k, ((if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => split i k
  have hdiag : ∑ i, ∑ k, (if i = k then j i * j k else 0) = ∑ i, j i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  rw [sq, Finset.sum_mul_sum, hexp]
  simp only [Finset.sum_add_distrib]
  rw [hsym, hdiag]
  simp only [Finset.sum_filter]
  ring

theorem flag_dims : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  intro n ε a j W h p q hp hq
  have hpq : p + q = n := by
    rw [← hp, ← hq]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this

  have hV : ∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0 :=
    fun x hx => h.2.2.2 x hx x hx
  have hS := finrank_last_eq_sum h
  have hSp : ∑ i, j i ≤ p := by
    rw [← hS, ← hp]; exact finrank_le_card_of_isotropic ε _ hV true
  have hSq : ∑ i, j i ≤ q := by
    rw [← hS, ← hq]; exact finrank_le_card_of_isotropic ε _ hV false
  have hsq := sq_sum_eq_sum_sq_add_two_mul_sum_lt' j
  subst hpq
  simp only [dimN]
  set S := ∑ i, j i
  set X := ∑ i, j i ^ 2
  set T := ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k
  obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hSp
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hSq
  have e1 : S + P + (S + Q) - 2 * S = P + Q := by omega
  have e2 : S + P - S = P := by omega
  have e3 : S + Q - S = Q := by omega
  rw [e1, e2, e3]
  refine ⟨by trivial, ?_, ?_⟩ <;> nlinarith [hsq]

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeeps
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagMem

variable {n : ℕ} {ε : Fin n → Bool}

theorem form_mul (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star (uMat g⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simpa using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y

theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem Jm_mul_conjTranspose (m : Formalism.REAL.UJ ε) :
    Formalism.REAL.Jm ε * (uMat m)ᴴ = uMat m⁻¹ * Formalism.REAL.Jm ε := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, GlobalTheory.FlagLeviGroup.uMat_mul_inv, Matrix.mul_one]
  calc Formalism.REAL.Jm ε * (uMat m)ᴴ
      = Formalism.REAL.Jm ε * ((uMat m)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem form_conjTranspose (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat m)ᴴ *ᵥ y)) = star ((uMat m⁻¹)ᴴ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧
      ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  intro n ε a j W hW
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1
    have hu' : u⁻¹ ∈ flagN ε W := by
      rw [← hN] at hu ⊢
      exact N.inv_mem hu
    simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]
    refine ⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩
    have h := hy _ (hu'.1 i x hx)
    rw [star_sub, sub_dotProduct] at h
    rw [Matrix.mulVec_sub, dotProduct_sub, form_mul]
    exact h
  · have hm' : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub (ε := ε) W).inv_mem hm
    simp only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]
    refine ⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩,
      ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩
    · rw [form_mul]
      exact hy _ (hm' i x hx).1
    · rw [form_conjTranspose]
      exact hy _ (hm' i x hx).2

end GlobalTheory.IwConst.FlagMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLevi
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem iwasawa_shift_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (M : Set G) (μM μK : Measure G) [SFinite μK] (δ φ ψ : G → ENNReal)
    (hδ : Measurable δ) (hφ : Measurable φ) (hψ : Measurable ψ) (hM : μM Mᶜ = 0) (l : G)
    (h1 : μM.map (fun g => g * l) = μM) (h2 : μK.map (fun g => l * g) = μK)
    (h3 : ∀ m ∈ M, δ (m * l) = δ m) (u : G) :
    ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM
      = ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM := by
  have hae : ∀ᵐ m ∂μM, m ∈ M := by rw [ae_iff]; exact hM

  have hK : ∀ m, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK
      = ∫⁻ k, φ (u * (m * l⁻¹) * k) * ψ k ∂μK := by
    intro m
    conv_rhs => rw [← h2, show (fun g : G => l * g) = ⇑(MeasurableEquiv.mulLeft l) from rfl,
      lintegral_map_equiv]
    simp [mul_assoc]
  simp_rw [hK]

  conv_rhs => rw [← h1, show (fun g : G => g * l) = ⇑(MeasurableEquiv.mulRight l) from rfl,
    lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [hae] with m hm
  simp [mul_assoc, h3 m hm]

theorem iwasawa_unfold_lintegral : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  intro G _ _ _ M L μN μM μK νL _ _ _ _ δ φ ψ hδ hφ hψ hM hL h1 h2 h3
  have hLae : ∀ᵐ l ∂νL, l ∈ L := by rw [ae_iff]; exact hL

  have hH : Measurable fun p : G × G × G =>
      δ p.2.1 * ∫⁻ k, φ (p.1 * p.2.1 * k) * ψ (p.2.2 * k) ∂μK := by
    refine Measurable.mul (hδ.comp measurable_snd.fst) ?_
    exact Measurable.lintegral_prod_right'
      (f := fun q : (G × G × G) × G => φ (q.1.1 * q.1.2.1 * q.2) * ψ (q.1.2.2 * q.2)) (by fun_prop)
  have hX : Measurable fun p : G × G =>
      ∫⁻ m, δ m * ∫⁻ k, φ (p.1 * m * k) * ψ (p.2 * k) ∂μK ∂μM :=
    Measurable.lintegral_prod_right' (f := fun q : (G × G) × G =>
        δ q.2 * ∫⁻ k, φ (q.1.1 * q.2 * k) * ψ (q.1.2 * k) ∂μK)
      (hH.comp (f := fun q : (G × G) × G => (q.1.1, q.2, q.1.2)) (by fun_prop))

  have step1 : ∀ u m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
      = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
    intro u m
    have hg : Measurable fun l => ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK :=
      Measurable.lintegral_prod_right' (f := fun q : G × G => φ (u * m * q.2) * ψ (q.1 * q.2))
        (by fun_prop)
    calc δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
        = δ m * ∫⁻ k, ∫⁻ l, φ (u * m * k) * ψ (l * k) ∂νL ∂μK := by
          congr 1
          exact lintegral_congr fun k => (lintegral_const_mul _ (hψ.comp (measurable_mul_const k))).symm
      _ = δ m * ∫⁻ l, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
          congr 1
          exact lintegral_lintegral_swap (by
            exact (show Measurable fun q : G × G => φ (u * m * q.1) * ψ (q.2 * q.1) by fun_prop).aemeasurable)
      _ = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := (lintegral_const_mul _ hg).symm
  have step2 : ∀ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM
      = ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL := by
    intro u
    calc _ = ∫⁻ m, ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL ∂μM :=
          lintegral_congr fun m => step1 u m
      _ = _ := lintegral_lintegral_swap (by
          exact (hH.comp (f := fun q : G × G => (u, q.1, q.2)) (by fun_prop)).aemeasurable)

  have key : ∀ᵐ l ∂νL, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN
      = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN := by
    filter_upwards [hLae] with l hl
    exact lintegral_congr fun u =>
      (iwasawa_shift_lintegral M μM μK δ φ ψ hδ hφ hψ hM l (h1 l hl) (h2 l hl) (h3 l hl) u).symm
  calc νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN
      = ∫⁻ _l, (∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN) ∂νL := by
        rw [lintegral_const]; exact mul_comm _ _
    _ = ∫⁻ l, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN ∂νL :=
        lintegral_congr_ae (key.mono fun _ hl => hl.symm)
    _ = ∫⁻ u, ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL ∂μN :=
        (lintegral_lintegral_swap (by exact hX.aemeasurable)).symm
    _ = _ := lintegral_congr fun u => (step2 u).symm

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersection
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.CloseLevi

variable {n : ℕ} {ε : Fin n → Bool}

theorem isClosed_stab {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) := GlobalTheory.FlagLeviGroup.continuous_uMat
  have h : {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} =
      ⋂ i, ⋂ y ∈ (W i : Set (Fin n → ℂ)),
        (fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  exact (W i).closed_of_finiteDimensional.preimage (hc.matrix_mulVec continuous_const)

theorem mem_flagM_of_keeps {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {l : Formalism.REAL.UJ ε}
    (hl : l ∈ maxK ε) (h : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i) : l ∈ flagM ε W := by
  have hl' : (uMat l)ᴴ * uMat l = 1 := hl
  show ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i
  intro i y hy
  exact ⟨h i y hy, GlobalTheory.FlagLeviGroup.inv_keeps hl' (W i) (h i) y hy⟩

private theorem exists_unit_valuation_le_subset_nhds {G : Type} [Group G] [TopologicalSpace G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {O : Set G} (hO : IsOpen O) (h1O : (1 : G) ∈ O) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ g, f g < ρ → g ∈ O := by
  have hC : IsCompact ({g | f g ≤ 1} ∩ Oᶜ) := hB.inter_right hO.isClosed_compl
  rcases ({g | f g ≤ 1} ∩ Oᶜ).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨le_of_lt hg, hgO⟩
    rw [hE] at hgC
    simpa using hgC
  · obtain ⟨c, ⟨_, hcO⟩, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
    have hc : 0 < f c := by
      rcases (h0 c).lt_or_eq with h | h
      · exact h
      · exfalso
        have hc1 : c = 1 := (h1 c).1 h.symm
        rw [hc1] at hcO
        exact absurd h1O hcO
    refine ⟨min 1 (f c), lt_min one_pos hc, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨(lt_of_lt_of_le hg (min_le_left _ _)).le, hgO⟩
    have hcg : f c ≤ f g := isMinOn_iff.1 hmin g hgC
    exact absurd (lt_of_lt_of_le hg (min_le_right _ _)) (not_lt.2 hcg)

theorem close_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {K P L : Set G} (hK : IsCompact K) (hP : IsClosed P) (hL : ∀ k ∈ K, k⁻¹ ∈ P → k⁻¹ ∈ L) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ P, ∀ k ∈ K, f (p * k) ≤ r → ∃ l ∈ L, f (l * k) < t := by

  have hloc : ∀ k ∈ K, ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k),
      ∀ p ∈ P, f (p * z.2) ≤ z.1 → ∃ l ∈ L, f (l * z.2) < t := by
    intro k hk
    by_cases hkP : k⁻¹ ∈ P
    ·
      have hkL := hL k hk hkP
      have hc : Continuous fun x : G => f (k⁻¹ * x) := hf.comp (continuous_const.mul continuous_id)
      have hopen : IsOpen {x : G | f (k⁻¹ * x) < t} := isOpen_lt hc continuous_const
      have hmem : k ∈ {x : G | f (k⁻¹ * x) < t} := by
        show f (k⁻¹ * k) < t
        rw [inv_mul_cancel, (h1 1).2 rfl]
        exact ht
      have hev : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ {x : G | f (k⁻¹ * x) < t} :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hopen.mem_nhds hmem)
      filter_upwards [hev] with z hz
      intro p _ _
      exact ⟨k⁻¹, hkL, hz⟩
    ·
      have hcont : Continuous (fun q : G × G => q.1 * q.2⁻¹) := continuous_fst.mul continuous_snd.inv
      have hopen : IsOpen ((fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ) := hP.isOpen_compl.preimage hcont
      have hmem : ((1 : G), k) ∈ (fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ := by
        show (1 : G) * k⁻¹ ∈ Pᶜ
        rw [one_mul]
        exact hkP
      obtain ⟨O, V, hO, hV, h1O, hkV, hOV⟩ := isOpen_prod_iff.1 hopen 1 k hmem
      obtain ⟨ρ, hρ, hρO⟩ := exists_unit_valuation_le_subset_nhds hf h0 h1 hB hO h1O
      have e1 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.1 < ρ :=
        (continuous_fst.tendsto ((0 : ℝ), k)).eventually (gt_mem_nhds hρ)
      have e2 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ V :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hV.mem_nhds hkV)
      filter_upwards [e1, e2] with z hz1 hz2
      intro p hp hpz
      exfalso
      have hO' : p * z.2 ∈ O := hρO _ (lt_of_le_of_lt hpz hz1)
      have hmem' := hOV (Set.mk_mem_prod hO' hz2)
      simp only [Set.mem_preimage, mul_inv_cancel_right, Set.mem_compl_iff] at hmem'
      exact hmem' hp
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun r x => ∀ p ∈ P, f (p * x) ≤ r → ∃ l ∈ L, f (l * x) < t) hloc
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := eventually_mem_nhdsWithin
  obtain ⟨r, hr, hrK⟩ := (hpos.and (hev.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨r, hr, fun p hp k hk hpk => hrK k hk p hp hpk⟩

theorem nrm_uMat_eq_zero (g : Formalism.REAL.UJ ε) : nrm (uMat g - 1) = 0 ↔ g = 1 := by
  rw [nrm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    apply Subtype.ext
    exact Units.ext h
  · rintro rfl
    exact GlobalTheory.FlagLeviGroup.uMat_one

theorem close_levi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r →
      ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  intro n ε a j W hW t ht

  have hL : ∀ k ∈ maxK ε, k⁻¹ ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} →
      k⁻¹ ∈ maxK ε ∩ flagM ε W := by
    intro k hk hkP
    have hk' : k⁻¹ ∈ maxK ε := (GlobalTheory.FlagLeviGroup.compactSub (ε := ε)).inv_mem hk
    exact Set.mem_inter hk' (mem_flagM_of_keeps W hk' hkP)
  obtain ⟨r, hr, hrP⟩ := close_of_compact (G := Formalism.REAL.UJ ε) (f := fun g => nrm (uMat g - 1))
    (continuous_nrm_uMat ε) (fun g => nrm_nonneg _) (fun g => nrm_uMat_eq_zero g) (isCompact_hsBall ε 1)
    (isCompact_maxK ε) (isClosed_stab W) hL ht
  refine ⟨r, hr, fun u hu m hm k hk hle => ?_⟩
  have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
  have hum : u * m ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
    rw [Set.mem_setOf_eq]
    intro i y hy
    rw [GlobalTheory.FlagLeviGroup.uMat_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FlagMeas.UnipRad.keeps hW u hu i _ (hm' i y hy).1
  exact hrP (u * m) hum k hk hle

end GlobalTheory.IwConst.CloseLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebra
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwTangent

variable {n : ℕ}

open scoped Matrix.Norms.Frobenius

theorem coe_smul_eq (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : (t : ℂ) • X = t • X := by
  ext i j; simp

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hs' := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at hs'
  have hc : IsClosed (A : Set (Matrix (Fin n) (Fin n) ℂ)) := A.closed_of_finiteDimensional
  exact hc.mem_of_tendsto hs'.tendsto_sum_nat (Filter.Eventually.of_forall fun m =>
    A.sum_mem fun k _ => A.smul_mem _ (hp k))

theorem mem_of_exp_sub_one_mem (T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) - 1 ∈ T) : X ∈ T := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  have hc : IsClosed (T : Set (Matrix (Fin n) (Fin n) ℂ)) := T.closed_of_finiteDimensional
  refine hc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  simp only [zero_add, zero_smul, NormedSpace.exp_zero]
  exact T.smul_mem _ (h t)

theorem exists_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    ∃ g : Formalism.REAL.UJ ε, uMat g = NormedSpace.exp (t • X) :=
  ⟨GlobalTheory.GaugeConst.expJ ε ⟨t • X, (GlobalTheory.GaugeConst.lieJ ε).smul_mem t hX⟩, rfl⟩

theorem lie_algebra_of_isCut : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  rintro n ε S d E ⟨A, hA, -, hE, rfl⟩
  simp only [coe_smul_eq]
  have h1 : ∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ,
      ∃ g ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A}, uMat g = NormedSpace.exp (t • X) := by
    intro X hX t
    obtain ⟨hXA, hXG⟩ := (hE X).2 hX
    obtain ⟨g, hg⟩ := exists_exp hXG t
    refine ⟨g, ?_, hg⟩
    change uMat g - 1 ∈ A
    rw [hg]
    exact exp_sub_one_mem A hA (A.smul_mem t hXA)
  refine ⟨h1, fun T hT i => mem_of_exp_sub_one_mem T _ fun t => ?_, fun X hX h => (hE X).1 ⟨?_, hX⟩⟩
  · obtain ⟨g, hg, hg'⟩ := h1 (E i) (Submodule.subset_span ⟨i, rfl⟩) t
    rw [← hg']
    exact hT g hg
  · refine mem_of_exp_sub_one_mem A _ fun t => ?_
    obtain ⟨g, hg⟩ := exists_exp hX t
    rw [← hg]
    exact h t g hg

end GlobalTheory.IwTangent
end
end

