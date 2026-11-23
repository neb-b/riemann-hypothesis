module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.CardEqOfMulEqOne
section
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

private theorem mulVec_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (i : ι) :
    (Γ *ᵥ (x ∘ e)) i = (Γ.submatrix e.symm e.symm *ᵥ x) (e i) := by
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun j => by simp)

private theorem vecMul_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (j : ι) :
    ((x ∘ e) ᵥ* Γ) j = (x ᵥ* Γ.submatrix e.symm e.symm) (e j) := by
  simp only [vecMul, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem jac {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι K) (hΓ : S.IntM Γ) (hH : S.Herm Γ)
    (hU : S.UM Γ) :
    ∃ (k : ℕ) (v : Fin k → ι → K), (∀ c, S.IntV (v c)) ∧
      (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
      ∑ c, Matrix.vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hU' : S.UM (Γ.submatrix e.symm e.symm) := by
    intro x hx hxd
    obtain ⟨x', hx', hxx'⟩ := hU (x ∘ e) (fun i => hx (e i)) (fun i => by
      rw [mulVec_comp_equiv_apply Γ e x i]; exact hxd (e i))
    refine ⟨x' ∘ e.symm, fun s => hx' (e.symm s), ?_⟩
    funext s
    have h1 := mulVec_comp_equiv_apply Γ e x (e.symm s)
    have h2 := mulVec_comp_equiv_apply Γ e (x' ∘ e.symm) (e.symm s)
    rw [Equiv.apply_symm_apply] at h1 h2
    have h3 : (x' ∘ e.symm) ∘ e = x' := by funext i; simp
    rw [h3] at h2
    rw [Pi.smul_apply, ← h1, ← h2, hxx', Pi.smul_apply]
  have jac_fin : ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) K), S.IntM Γ → S.Herm Γ → S.UM Γ →
      ∃ (k : ℕ) (v : Fin k → Fin m → K), (∀ c, S.IntV (v c)) ∧
        (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
        ∑ c, vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ := by
    intro m
    induction m with
    | zero =>
      intro Γ _ _ _
      exact ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by ext i; exact i.elim0⟩
    | succ m ih =>
      intro Γ hΓ hH hU
      by_cases h0 : Γ = 0
      · exact ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by simp [h0]⟩
      obtain ⟨a, i, ha, hai, haa⟩ := S.exists_unit_vec (Γ := Γ) hΓ hH hU h0
      have hG := S.IntM_Γp hΓ ha
      have hHG := S.Herm_Γp hΓ hH ha
      have hUG := S.UM_Γp hΓ hH hU ha haa
      have hGa := S.Γp_mulVec_self (Γ := Γ) haa
      have haG := S.vecMul_Γp_self (Γ := Γ) haa
      set G := S.Γp Γ a with hG_def
      obtain ⟨k, v'', hvI, hvo, hvs⟩ := ih (G.submatrix i.succAbove i.succAbove)
        (fun s t => hG _ _) (fun s t => hHG _ _) (S.UM_drop i hUG ha hai hGa haG)
      have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
      have hσa : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU (S.not_NU_σ (ha i) hai)
      set v' : Fin k → Fin (m + 1) → K := fun c => ins i (v'' c) with hv'_def
      have hv'I : ∀ c, S.IntV (v' c) := fun c => S.IntV_ins i (hvI c)
      have hv'o : ∀ c c', S.hf G (v' c) (v' c') = if c = c' then 1 else 0 := fun c c' => by
        rw [hv'_def, S.hf_ins, hvo]
      have hv's : ∑ c, vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) = G := by
        apply S.ext_drop i hai0 hσa _ hGa _ haG
        · intro s t
          rw [Matrix.sum_apply]
          conv_rhs => rw [← submatrix_apply G i.succAbove i.succAbove s t, ← hvs, Matrix.sum_apply]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [vecMulVec_apply, hv'_def, S.cv_ins, mulVec_ins, vecMul_ins]
        · rw [sum_mulVec']
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [vecMulVec_mulVec, ← dotProduct_mulVec, hGa, dotProduct_zero, op_smul_eq_smul, zero_smul]
        · rw [vecMul_sum']
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [vecMul_vecMulVec, dotProduct_mulVec, haG, zero_dotProduct, zero_smul]
      refine ⟨k + 1, Fin.cons a (fun c => S.proj Γ a (v' c)), ?_, ?_, ?_⟩
      · intro c
        refine Fin.cases ?_ (fun c => ?_) c
        · simpa using ha
        · simpa using S.IntV_proj hΓ ha (hv'I c)
      · intro c c'
        refine Fin.cases ?_ (fun c => ?_) c <;> refine Fin.cases ?_ (fun c' => ?_) c'
        · simpa using haa
        · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_self_proj haa]
          rw [ite_eq_right (Fin.succ_ne_zero c').symm]
        · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_proj_self hΓ hH ha haa (hv'I c)]
          rw [ite_eq_right (Fin.succ_ne_zero c)]
        · simp only [Fin.cons_succ, S.hf_proj_proj haa, Fin.succ_inj]
          exact hv'o c c'
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : ∀ c, vecMulVec (Γ *ᵥ S.proj Γ a (v' c)) (S.cv (S.proj Γ a (v' c)) ᵥ* Γ)
            = vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) := fun c => by
          rw [S.mulVec_proj, S.vecMul_proj hΓ hH ha (hv'I c)]
        rw [Finset.sum_congr rfl (fun c _ => this c), hv's, hG_def, Γp]
        abel
  obtain ⟨k, v, hv, hort, hsum⟩ := jac_fin (Fintype.card ι) (Γ.submatrix e.symm e.symm)
    (fun s t => hΓ _ _) (fun s t => hH _ _) hU'
  have hconj : ∀ x : Fin (Fintype.card ι) → K, S.cv (x ∘ e) = S.cv x ∘ e := fun x => rfl
  refine ⟨k, fun c => v c ∘ e, fun c i => hv c (e i), fun c c' => ?_, ?_⟩
  · rw [← hort c c']
    simp only [hf, hconj, dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by
      simp only [Function.comp, mulVec_comp_equiv_apply Γ e (v c') i])
  · ext i j
    have h := congrFun (congrFun hsum (e i)) (e j)
    simp only [Matrix.sum_apply, vecMulVec_apply, submatrix_apply, Equiv.symm_apply_apply] at h
    simp only [Matrix.sum_apply, vecMulVec_apply, hconj, mulVec_comp_equiv_apply Γ e _ i,
      vecMul_comp_equiv_apply Γ e _ j]
    exact h

end JSetup

theorem card_eq_of_mul_eq_one {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (V : Matrix n (Fin k) K) (W : Matrix (Fin k) n K) (h1 : V * W = 1) (h2 : W * V = 1) :
    Fintype.card n = k := by
  have e : (Fin k → K) ≃ₗ[K] (n → K) :=
    LinearEquiv.ofLinear (Matrix.toLin' V) (Matrix.toLin' W)
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have h := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.ConjMatrixApply
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem conj_entry_int {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} {ha : 0 < a₀} {hdK : 0 < dK} {lam : ℂ} {hlam : lam ≠ 0}
    (hCm : CmOK a₀ b₀ c₀ dK) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hIdx : ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)))
    (τ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (hτ : ∀ y ∈ pow4 Λ, τ y ∈ pow4 Λ) (x w : Fin 4 × n) :
    ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧
      g₁ (τ (g₁.symm (Pi.single w 1))) x = q₁ + q₂ * sq dK := by
  classical
  have hl2 : ¬ l ∣ 2 := fun h2 => by have := Nat.le_of_dvd two_pos h2; omega
  have hla : ¬ l ∣ a₀ := by
    intro hla
    apply hin
    refine ⟨(b₀ : ZMod l), ?_⟩
    have e := congrArg (Int.cast : ℤ → ZMod l) hCm.1
    push_cast at e
    have ha0 : (a₀ : ZMod l) = 0 := (CharP.cast_eq_zero_iff (ZMod l) l a₀).mpr hla
    rw [ha0] at e
    linear_combination -e
  set N := relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) with hN
  have hN0 : N ≠ 0 := fun h0 => hIdx (by rw [h0]; exact dvd_zero l)
  have hden : ¬ l ∣ 2 * N ^ 2 * a₀ := by
    intro hd
    have hp : l.Prime := Fact.out
    rcases (Nat.Prime.dvd_mul hp).mp hd with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact hl2 h''
      · exact hIdx (hp.dvd_of_dvd_pow h'')
    · exact hla h'
  have he : Pi.single w (lam * (a₀ : ℂ)) ∈ stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n) := by
    intro i _
    by_cases hi : i = w
    · subst hi
      rw [Pi.single_eq_same]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice
    · rw [Pi.single_eq_of_ne hi]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).lattice.toAddSubgroup.zero_mem
  have h1 := idx_smul_symm_mem (cmL a₀ b₀ dK ha hdK lam hlam) h Λ hΛ g₁ hIso he
  have h3 := idx_smul_mem (cmL a₀ b₀ dK ha hdK lam hlam) Λ g₁ (hτ _ h1)
  have h4 := h3 x (Set.mem_univ x)
  obtain ⟨m, k, hmk⟩ := PeriodPair.mem_lattice.mp h4
  have hsingle : Pi.single w (lam * (a₀ : ℂ)) = (lam * (a₀ : ℂ)) • Pi.single w (1 : ℂ) := by
    ext i; by_cases hi : i = w
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  rw [hsingle, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hmk
  simp only [map_smul, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at hmk
  have hω1 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₁ = lam * (a₀ : ℂ) := rfl
  have hω2 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₂ = lam * cmTheta b₀ dK := rfl
  rw [hω1, hω2, cmTheta] at hmk
  refine ⟨((2 * m * a₀ + k * b₀ : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ),
    ((k : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ), ?_, ?_, ?_⟩
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    have hac : (a₀ : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    set E := g₁ (τ (g₁.symm (Pi.single w 1))) x with hEdef
    have hE : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) * E =
        lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) := by
      linear_combination (-2 : ℂ) * hmk
    have hc : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) ≠ 0 := by simp [hNc, hac, hlam]
    have hE' : E = lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) /
        ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) := by
      rw [eq_div_iff hc, mul_comm]; exact hE
    rw [hE']
    unfold sq
    push_cast
    field_simp

theorem gmat_eq {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    gmat g = LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  ext x w
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem conj_matrix_apply {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (x w : Fin 4 × n) :
    (LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g) x w
      = g (Matrix.toLin' T (g.symm (Pi.single w 1))) x := by
  have e : LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g =
      LinearMap.toMatrix' ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ Matrix.toLin' T ∘ₗ
        (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', gmat_eq, mul_assoc]
  rw [e, LinearMap.toMatrix'_apply]
  rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.NormAddLeKur
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP Jac

variable {l : ℕ} [Fact l.Prime]

def OO (dK : ℕ) (δ : MaximalUnramifiedExtension l) (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : Subring (MaximalUnramifiedExtension l) where
  carrier := {x | ∃ a b : ℤ_[l], x = ψ l a + δ * ψ l b}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c - dK * (b * e), a * e + b * c, ?_⟩
    simp only [map_add (f := _), map_sub, map_mul, map_natCast]
    linear_combination (ψ l b * ψ l e) * hδ
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by simp only [map_add (f := _)]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by simp only [map_neg]; ring⟩

theorem norm_add_le_Kur (x y : MaximalUnramifiedExtension l) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  show ‖(x : ℂ_[l]) + y‖ ≤ max ‖(x : ℂ_[l])‖ ‖(y : ℂ_[l])‖
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_δ_le {dK : ℕ} {δ : MaximalUnramifiedExtension l} (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) : ‖δ‖ ≤ 1 := by
  have h : ‖δ‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hδ, norm_neg, norm_natCast_Kur]
    have : ((dK : ℤ_[l]) : ℚ_[l]) = (dK : ℚ_[l]) := by push_cast; rfl
    rw [← this]; exact PadicInt.norm_le_one _
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

theorem norm_le_one_of_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} {x : MaximalUnramifiedExtension l}
    (hx : x ∈ OO dK δ hδ) : ‖x‖ ≤ 1 := by
  obtain ⟨a, b, rfl⟩ := hx
  refine (norm_add_le_Kur _ _).trans (max_le (norm_ψ_le l a) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (norm_δ_le hδ) (norm_nonneg _) (norm_ψ_le l b)

theorem ratCast_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} (q : ℚ) (hq : padicNorm l q ≤ 1) :
    (q : MaximalUnramifiedExtension l) ∈ OO dK δ hδ := by
  have hq' : ‖(q : ℚ_[l])‖ ≤ 1 := by rw [Padic.eq_padicNorm]; exact_mod_cast hq
  refine ⟨⟨(q : ℚ_[l]), hq'⟩, 0, ?_⟩
  simp only [map_zero, mul_zero, add_zero]
  show (q : MaximalUnramifiedExtension l) = φ l (q : ℚ_[l])
  rw [map_ratCast]

theorem δ_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} : δ ∈ OO dK δ hδ := ⟨0, 1, by simp⟩

theorem norm_sq_unit {dK : ℕ} (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (a b : ℤ_[l])
    (h : ‖a‖ = 1 ∨ ‖b‖ = 1) : ‖a * a + dK * (b * b)‖ = 1 := by
  rw [norm_eq_one_iff]
  intro h0
  rw [map_add (f := _), map_mul, map_mul, map_mul, toZMod_natCast] at h0
  by_cases hB : PadicInt.toZMod b = 0
  · have hA : PadicInt.toZMod a = 0 := by
      rw [hB, mul_zero, mul_zero, add_zero] at h0; exact mul_self_eq_zero.mp h0
    rcases h with h | h
    · exact (norm_eq_one_iff l a).mp h hA
    · exact (norm_eq_one_iff l b).mp h hB
  · exact hin ⟨PadicInt.toZMod a / PadicInt.toZMod b, by field_simp; linear_combination h0⟩

def setup (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l))
    (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (δ : MaximalUnramifiedExtension l) (hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)) (hσδ : σ δ = -δ) :
    JSetup (MaximalUnramifiedExtension l) where
  σ := σ
  O := OO dK δ hδ
  p := (l : MaximalUnramifiedExtension l)
  hp0 := by
    intro h
    have := norm_l_Kur l
    rw [h, norm_zero] at this
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    exact (inv_pos.mpr hl).ne this
  hpO := ⟨l, 0, by simp⟩
  hσp := map_natCast σ l
  hσO := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a, -b, by rw [map_add (f := _), map_mul, σ_ψ l σ hσ, σ_ψ l σ hσ, hσδ, map_neg]; ring⟩
  hσσ := by
    rintro _ ⟨a, b, rfl⟩
    simp only [map_add (f := _), map_mul, σ_ψ l σ hσ, hσδ, map_neg, neg_neg]
  hinv := by
    rintro _ ⟨a, b, rfl⟩ hnu
    have hab : ‖a‖ = 1 ∨ ‖b‖ = 1 := by
      by_contra hc
      push Not at hc
      apply hnu
      obtain ⟨a', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (lt_of_le_of_ne (PadicInt.norm_le_one a) hc.1)
      obtain ⟨b', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd b).mp (lt_of_le_of_ne (PadicInt.norm_le_one b) hc.2)
      exact ⟨ψ l a' + δ * ψ l b', ⟨a', b', rfl⟩, by simp only [map_mul, map_natCast]; ring⟩
    obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr (norm_sq_unit hin a b hab)
    refine ⟨a * ↑u⁻¹, -(b * ↑u⁻¹), ?_⟩
    have hNu : ψ l (a * a + dK * (b * b)) * ψ l ↑u⁻¹ = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hmul : (ψ l a + δ * ψ l b) * (ψ l (a * ↑u⁻¹) + δ * ψ l (-(b * ↑u⁻¹))) = 1 := by
      simp only [map_mul, map_neg, map_add (f := _), map_natCast] at hNu ⊢
      linear_combination hNu + (-(ψ l b * ψ l b * ψ l ↑u⁻¹)) * hδ
    exact inv_eq_of_mul_eq_one_right hmul
  hone := by
    rintro ⟨y, hy, h⟩
    have h1 := congrArg norm h
    rw [norm_one, norm_mul, norm_l_Kur] at h1
    have hy1 := norm_le_one_of_mem hy
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have : (l : ℝ)⁻¹ * ‖y‖ ≤ (l : ℝ)⁻¹ := mul_le_of_le_one_right (by positivity) hy1
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
    linarith
  htwo := by
    have h2 : ‖(2 : ℤ_[l])‖ = 1 := by
      rw [norm_eq_one_iff, map_ofNat]; exact odd_l l h5
    obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr h2
    refine ⟨↑u⁻¹, 0, ?_⟩
    have : (2 : MaximalUnramifiedExtension l) * ψ l ↑u⁻¹ = 1 := by
      rw [← map_ofNat (ψ l) 2, ← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_zero, mul_zero, add_zero]
    exact inv_eq_of_mul_eq_one_right this
  h2 := two_ne_zero
  hnorm := by
    rintro _ ⟨a, b, rfl⟩ hσu hnu
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at hδ
      exact hld (hδ ▸ dvd_zero l)
    have hb : ψ l b = 0 := by
      rw [map_add (f := _), map_mul, σ_ψ l σ hσ, σ_ψ l σ hσ, hσδ] at hσu
      have h2δ : (2 * δ) * ψ l b = 0 := by linear_combination -hσu
      rcases mul_eq_zero.mp h2δ with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hδ0)
      · exact h
    have ha : ‖a‖ = 1 := by
      by_contra hc
      apply hnu
      obtain ⟨a', rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).mp (lt_of_le_of_ne (PadicInt.norm_le_one a) hc)
      exact ⟨ψ l a', ⟨a', 0, by simp⟩, by rw [hb]; simp [map_mul]⟩
    obtain ⟨x, y, hxy⟩ := exists_norm l h5 dK hld a ha
    refine ⟨ψ l x + δ * ψ l y, ⟨x, y, rfl⟩, ?_⟩
    rw [hb, mul_zero, add_zero, ← hxy]
    simp only [map_add (f := _), map_mul, σ_ψ l σ hσ, hσδ, map_natCast]
    linear_combination (-(ψ l y * ψ l y)) * hδ
  hsep := by
    intro x hx hx0
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
    refine ⟨N, ?_⟩
    rintro ⟨y, hy, rfl⟩
    have hy1 := norm_le_one_of_mem hy
    rw [norm_mul, norm_pow, norm_l_Kur] at hpos
    rw [norm_mul, norm_pow, norm_l_Kur] at hN
    have : (l : ℝ)⁻¹ ^ N * ‖y‖ ≤ (l : ℝ)⁻¹ ^ N := mul_le_of_le_one_right (by positivity) hy1
    linarith

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

