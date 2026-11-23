module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariant
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasEquiv

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

abbrev trF (U V : Mx n) : ℝ := (trace (U * V)).re

theorem trF_sum_left {ι : Type} (s : Finset ι) (r : ι → ℝ) (Z : ι → Mx n) (V : Mx n) :
    trF (∑ c ∈ s, r c • Z c) V = ∑ c ∈ s, r c * trF (Z c) V := by
  simp [trF, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem trF_comm (U V : Mx n) : trF U V = trF V U := by
  simp only [trF, Matrix.trace_mul_comm U V]

theorem dRep_finsum (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (w : ι → H) (hw : ∀ i, Sm ε σ (w i)) : dRep σ Z (∑ i ∈ s, w i) = ∑ i ∈ s, dRep σ Z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul hσ (l := [Z]) (by simp [hZ]) (0 : ℂ) (x := 0) ((smooth (Jm ε) σ).zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact Dw_add hσ (l := [Z]) (by simp [hZ]) (hw _) ((smooth (Jm ε) σ).sum_mem fun i _ => hw i)

variable [CompleteSpace H]

theorem dRep_sum_fin (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {w : H}
    (hw : Sm ε σ w) (a : ι → ℝ) : dRep σ (∑ c, a c • Z c) w = ∑ c, (a c : ℂ) • dRep σ (Z c) w := by
  let e := Fintype.equivFin ι
  have := h.dRep_sum (B := Z ∘ e.symm) (fun i => hZ _) hw (a ∘ e.symm)
  simpa only [Function.comp_apply, e.symm.sum_comp (fun c => a c • Z c),
    e.symm.sum_comp (fun c => (a c : ℂ) • dRep σ (Z c) w)] using this

theorem dRep_dRep_sum (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (a b : ι → ℝ) :
    dRep σ (∑ c, a c • Z c) (dRep σ (∑ d, b d • Z d) v) =
      ∑ c, ∑ d, ((a c * b d : ℝ) : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) := by
  have hs : ∀ d, Sm ε σ (dRep σ (Z d) v) := fun d => dRep_mem (isUnit_Jm ε) h.1 hv (hZ d)
  have hw : Sm ε σ (∑ d, (b d : ℂ) • dRep σ (Z d) v) :=
    (smooth (Jm ε) σ).sum_mem fun d _ => (smooth (Jm ε) σ).smul_mem _ (hs d)
  rw [dRep_sum_fin h hZ hv b, dRep_sum_fin h hZ hw a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dRep_finsum h.1 (hZ c) _ _ fun d => (smooth (Jm ε) σ).smul_mem _ (hs d), Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := Dw_smul h.1 (l := [Z c]) (by simp [hZ c]) (b d : ℂ) (hs d)
  rw [show dRep σ (Z c) ((b d : ℂ) • dRep σ (Z d) v) = (b d : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) from this,
    smul_smul]
  push_cast; ring_nf

theorem trF_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) : trF (g⁻¹ * U * g) V = trF U (g * V * g⁻¹) := by
  unfold trF
  congr 1
  rw [show g⁻¹ * U * g * V = g⁻¹ * (U * g * V) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trF_conj_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) :
    trF (g * U * g⁻¹) (g * V * g⁻¹) = trF U V := by
  unfold trF
  congr 1
  have e : g * U * g⁻¹ * (g * V * g⁻¹) = g * (U * V * g⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g⁻¹ g, inv_mul_UJ hg, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, inv_mul_UJ hg, Matrix.mul_one]

theorem conj_mem' {g : Mx n} (hg : g ∈ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) : g * X * g⁻¹ ∈ lieSet ε := by
  have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) hX
  rwa [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg))] at this

theorem coef_orth {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ} (hs : ∀ c, s c * s c = 1)
    (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) (d e : ι) :
    ∑ c, s c * (s d * trF (g⁻¹ * Z c * g) (Z d)) * (s e * trF (g⁻¹ * Z c * g) (Z e)) =
      if d = e then s d else 0 := by
  have h3 : ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) =
      trF (g * Z d * g⁻¹) (g * Z e * g⁻¹) := by
    conv_rhs => rw [hE _ (conj_mem' hg (hZ d)), trF_sum_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [trF_comm (g * Z d * g⁻¹) (Z c)]
  rw [trF_conj_conj hg, hO] at h3
  simp only [trF_conj hg]
  calc _ = s d * s e * ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_; ring
    _ = _ := by
        rw [h3]; split_ifs with hde
        · subst hde; rw [mul_assoc, hs, mul_one]
        · simp

theorem sum_sq_conj (h : Std ε σ) {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ}
    (hs : ∀ c, s c * s c = 1) (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    ∑ c, (s c : ℂ) • dRep σ (g⁻¹ * Z c * g) (dRep σ (g⁻¹ * Z c * g) v) =
      ∑ c, (s c : ℂ) • dRep σ (Z c) (dRep σ (Z c) v) := by
  set a : ι → ι → ℝ := fun c d => s d * trF (g⁻¹ * Z c * g) (Z d) with ha
  have hW : ∀ c, g⁻¹ * Z c * g = ∑ d, a c d • Z d := fun c =>
    hE _ (conj_mem_lie (isUnit_Jm ε) hg (hZ c))
  have key := coef_orth hs hO hE hZ hg
  calc _ = ∑ c, (s c : ℂ) • ∑ d, ∑ e, ((a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) :=
        Finset.sum_congr rfl fun c _ => by rw [hW c, dRep_dRep_sum h hZ hv]
    _ = ∑ d, ∑ e, ((∑ c, s c * a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1; push_cast; ring
    _ = _ := by
        simp only [ha, key]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp [apply_ite]

omit [CompleteSpace H] in
theorem casOp_translate (hσ : IsURepOn (UJset ε) σ) {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    casOp σ X Y (σ g v) = σ g (casOp σ (fun i => g⁻¹ * X i * g) (fun b => g⁻¹ * Y b * g) v) := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (σ g v)) = σ g (dRep σ (g⁻¹ * Z * g) (dRep σ (g⁻¹ * Z * g) v)) :=
    fun Z hZ => Dw_translate hσ hg hv (l := [Z, Z]) (by simp [hZ])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casOp, h _ (hX _), h _ (hY _), map_sub, map_sum]

theorem kk_orth (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length) :
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := _root_.GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal n ε i j
theorem pp_orth (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length) :
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := _root_.GlobalTheory.TypeSum.CasBasis.pB_orthonormal n ε a b
theorem kp_orth (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length) :
    (trace (kB ε i * pB ε b)).re = 0 := _root_.GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB n ε i b
theorem expand (n : ℕ) (ε : Fin n → Bool) : ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := _root_.GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases n ε

theorem casOp_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ g ∈ UJset ε, ∀ v, Sm ε σ v →
      casOp σ (kB ε) (pB ε) (σ g v) = σ g (casOp σ (kB ε) (pB ε) v) := by
  intro n ε H _ _ _ σ h g hg v hv
  obtain ⟨hk, hp⟩ := _root_.GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet n ε
  let Z : Fin (kList ε).length ⊕ Fin (pList ε).length → Mx n := Sum.elim (kB ε) (pB ε)
  let s : Fin (kList ε).length ⊕ Fin (pList ε).length → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)
  have hs : ∀ c, s c * s c = 1 := by rintro (c | c) <;> simp [s]
  have hZ : ∀ c, Z c ∈ lieSet ε := by rintro (c | c); exacts [hk c, hp c]
  have hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0 := by
    rintro (c | c) (d | d)
    · simpa [Z, s] using kk_orth n ε c d
    · simpa [Z, s] using kp_orth n ε c d
    · simpa [Z, s, trF_comm] using kp_orth n ε d c
    · simpa [Z, s] using pp_orth n ε c d
  have hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c := by
    intro U hU
    simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, neg_one_mul, one_mul, neg_smul,
      Finset.sum_neg_distrib]
    conv_lhs => rw [expand n ε U hU]
    abel
  have := sum_sq_conj h hs hO hE hZ hg hv
  simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_neg, Complex.ofReal_one, neg_smul,
    one_smul, Finset.sum_neg_distrib] at this
  rw [casOp_translate h.1 hk hp hg hv]
  congr 1
  simp only [casOp, sub_eq_neg_add]
  exact this

end GlobalTheory.TypeSum.CasEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoefBoundTwoFinSum
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

section SobSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sobCont_zero_form : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add_form {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩
  have n1 := sobNorm_nonneg σ S w
  have n2 := sobNorm_nonneg σ S' w
  have b1 : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  have b2 : ‖ℓ' w‖ ≤ C' * sobNorm σ S' w := hC' w hw
  show ‖ℓ w + ℓ' w‖ ≤ (|C| + |C'|) * sobNorm σ (S ++ S') w
  rw [sobNorm_append]
  have a1 : C * sobNorm σ S w ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) n1
  have a2 : C' * sobNorm σ S' w ≤ |C'| * sobNorm σ S' w := mul_le_mul_of_nonneg_right (le_abs_self C') n2
  have a3 := abs_nonneg C
  have a4 := abs_nonneg C'
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem sobCont_smul_form (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) :
    Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have b : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  show ‖c • ℓ w‖ ≤ ‖c‖ * C * sobNorm σ S w
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left b (norm_nonneg c)

theorem sobCont_sum_form {ι : Type} (s : Finset ι) (f : ι → H →ₗ[ℂ] ℂ) (h : ∀ i, Sobolev₂ (lieSet ε) σ (f i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (sobCont_zero_form (ε := ε) (σ := σ) (H := H))
  · intro i s hi ih
    rw [Finset.sum_insert hi]
    exact sobCont_add_form (h i) ih

end SobSum

theorem coefBound_two_finSum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (x j)) → ∀ M : ℝ, 0 ≤ M → (∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (x j))‖ ≤ M * (1 + hs y) ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ h hB N
  have hσ := h.1
  obtain ⟨a, c, ha0, hc0, haK, hcK, Z, C₀, hZ, hZU, hC₀, hA⟩ := exists_rank_one_isAvg n ε H σ h
  have ha : Sm ε σ a := h.2.2.1 a haK
  have hc : Sm ε σ c := h.2.2.1 c hcK
  obtain ⟨S, C₁, hS, hC₁, hb2⟩ := coefBound_two n ε H σ h hB a c ha ha0 hc hc0 N
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn
    (f := fun y : Mx n => (1 + hs y) ^ N) ((continuous_const.add continuous_hs).pow N).continuousOn
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, (1 + hs y) ^ N ≤ K := fun y hy =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK₀ y hy)).trans (le_max_left _ _)
  refine ⟨S, C₁ * C₀ * K, hS, mul_nonneg (mul_nonneg hC₁ hC₀) hK0, ?_⟩
  intro p ℓ x hℓ hx M hM hgr b w hb hw
  let γ : H → H → ℂ := fun b w => ∑ j, ⟪b, x j⟫_ℂ * ℓ j w
  have h1 : ∀ b, Sm ε σ b → SobFun ε σ (γ b) := by
    intro b _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ (fun j => ⟪b, x j⟫_ℂ • ℓ j)
      (fun j => sobCont_smul_form _ (hℓ j))
    have e : γ b = ⇑(∑ j, ⟪b, x j⟫_ℂ • ℓ j) := by
      funext w
      simp [γ, LinearMap.sum_apply]
    rw [e]
    exact sobFun_of_sobCont hL
  have h2 : ∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w)) := by
    intro w _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ
      (fun j => star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) (fun j => sobCont_smul_form _ (sobCont_inner _))
    have e : (fun b => star (γ b w)) = ⇑(∑ j, star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) := by
      funext b
      simp only [γ, star_sum, LinearMap.sum_apply, LinearMap.smul_apply,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul', mul_comm, ← inner_conj_symm, starRingEnd_apply, star_star]
    rw [e]
    exact sobFun_of_sobCont hL
  have h3 : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε,
      ‖γ (σ g' c) (σ g a)‖ ≤ (C₀ * K * M) * (1 + hs g) ^ N * (1 + hs g') ^ N := by
    intro g hg g' hg'
    have hg'i := inv_mem_UJ hg'
    have hinv : g'⁻¹⁻¹ = g' :=
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg'))
    have e : γ (σ g' c) (σ g a) =
        ∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) ((fun v => ⟪c, v⟫_ℂ • a) (σ g'⁻¹ (x j))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hi := inner_sigma hσ hg'i c (x j)
      rw [hinv] at hi
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      rw [hi]
    have P0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) N
    have P1 : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have hbd : ∀ y ∈ Z, ‖∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j)))‖ ≤
        M * K * (1 + hs g) ^ N * (1 + hs g') ^ N := by
      intro y hy
      have hyU := hZU hy
      have hm : g * y * g'⁻¹ ∈ UJset ε := mul_mem_UJ (mul_mem_UJ hg hyU) hg'i
      have e2 : ∀ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j))) = ℓ j (σ (g * y * g'⁻¹) (x j)) := fun j => by
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        rw [sigma_mul hσ (mul_mem_UJ hg hyU) hg'i, sigma_mul hσ hg hyU]
      simp only [e2]
      refine (hgr _ hm).trans ?_
      have q1 := one_add_hs_mul_le (g * y) g'⁻¹
      have q2 := one_add_hs_mul_le g y
      rw [hs_inv hg'] at q1
      have hy0 := hs_nonneg y
      have hgg := hs_nonneg g
      have hgg' := hs_nonneg g'
      have q : 1 + hs (g * y * g'⁻¹) ≤ (1 + hs g) * (1 + hs y) * (1 + hs g') :=
        q1.trans (mul_le_mul_of_nonneg_right q2 (by linarith))
      have qN : (1 + hs (g * y * g'⁻¹)) ^ N ≤ (1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith [hs_nonneg (g * y * g'⁻¹)]) q N
      have hKy := hK y hy
      calc M * (1 + hs (g * y * g'⁻¹)) ^ N ≤ M * ((1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N) :=
            mul_le_mul_of_nonneg_left qN hM
        _ ≤ M * ((1 + hs g) ^ N * K * (1 + hs g') ^ N) := by gcongr
        _ = _ := by ring
    have key := avgBd_sobCont n ε H σ h (fun v => ⟪c, v⟫_ℂ • a) Z C₀ hZ hZU hC₀ hA (Fin p)
      (fun j => ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (fun j => σ g'⁻¹ (x j))
      (fun j => sobCont_translate hσ (hℓ j) hg) (fun j => (hx j).translate hσ hg'i)
      (fun j => sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ha)))
      (M * K * (1 + hs g) ^ N * (1 + hs g') ^ N)
      (mul_nonneg (mul_nonneg (mul_nonneg hM hK0) P0) P1) hbd
    rw [e]
    exact key.trans (le_of_eq (by ring))
  have fin := hb2 γ h1 h2 (C₀ * K * M) (mul_nonneg (mul_nonneg hC₀ hK0) hM) h3 b w hb hw
  calc ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ = ‖γ b w‖ := rfl
    _ ≤ _ := fin
    _ = _ := by ring

end GlobalTheory.TypeSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivativesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  first | exact @GlobalTheory.AvgFam.avg_closed | exact GlobalTheory.AvgFam.avg_closed | (intros; apply GlobalTheory.AvgFam.avg_closed <;> assumption)
end

