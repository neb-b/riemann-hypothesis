module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInB
section
noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

abbrev Bsp (τ : T) (m n : ℕ) : Type := {τ' : T // τ' ≠ τ} → Fin m → Fin n → ℂ

def extF (b : Bsp τ m n) : T → Fin m → Fin n → ℂ := fun τ' => if h : τ' = τ then 0 else b ⟨τ', h⟩

def extL : Bsp τ m n →L[ℝ] (T → Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := extF τ
      map_add' := fun b b' => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h]
      map_smul' := fun r b => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h] }

def coordL (k : T × Fin m × Fin n) : Bsp τ m n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => Fin m → Fin n → ℂ) k.1).comp (extL τ)))

theorem tg_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type} (v : σ → E → ℂ)
    (hv : ∀ k, (v k).HasTemperateGrowth) (p : MvPolynomial σ ℂ) :
    (fun x => MvPolynomial.eval (fun k => v k x) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := Function.HasTemperateGrowth.const (E := E) a
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | add p q hp hq =>
    have := hp.add hq
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | mul_X p k hp =>
    have := hp.mul (hv k)
    convert this using 1
    all_goals first | rfl | (funext x; simp)

def vC (k : T × Fin m × Fin n × Bool) (b : Bsp τ m n) : ℂ :=
  if k.2.2.2 then conj (coordL τ (k.1, k.2.1, k.2.2.1) b) else coordL τ (k.1, k.2.1, k.2.2.1) b

theorem tg_vC (k : T × Fin m × Fin n × Bool) : (vC (m := m) (n := n) τ k).HasTemperateGrowth := by
  by_cases hk : k.2.2.2 = true
  · have e : vC (m := m) (n := n) τ k = ⇑(Complex.conjCLE.toContinuousLinearMap.comp (coordL τ (k.1, k.2.1, k.2.2.1))) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _
  · have e : vC (m := m) (n := n) τ k = ⇑(coordL τ (k.1, k.2.1, k.2.2.1)) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _

theorem tg_poly (p : MvPolynomial (T × Fin m × Fin n × Bool) ℂ) :
    (fun b : Bsp τ m n => MvPolynomial.eval (fun k => vC τ k b) p).HasTemperateGrowth :=
  tg_eval _ (tg_vC τ) p

variable (fr : Matrix (Fin m) (Fin m) ℂ)

def eL (hfr : IsUnit fr.det) : (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] ((Fin m → Fin n → ℂ) × Bsp τ m n) where
  toFun z := (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ)), fun τ' => z τ'.1)
  invFun ab := fun τ' => if h : τ' = τ then Matrix.of.symm (fr * Matrix.of ab.1) else ab.2 ⟨τ', h⟩
  map_add' z w := by
    ext1
    · exact Matrix.mul_add fr⁻¹ (of (z τ)) (of (w τ))
    · rfl
  map_smul' r z := by
    ext1
    · exact Matrix.mul_smul fr⁻¹ r (of (z τ))
    · rfl
  left_inv z := by
    funext τ'
    by_cases h : τ' = τ
    · subst h
      simp
      change (fr * (fr⁻¹ * of (z τ'))).row = (of (z τ')).row
      rw [Matrix.mul_nonsing_inv_cancel_left fr _ hfr]
    · simp [h]
  right_inv ab := by
    ext1
    · simp
      change (fr⁻¹ * (fr * of ab.1)).row = (of ab.1).row
      rw [Matrix.nonsing_inv_mul_cancel_left fr _ hfr]
    · funext τ'
      simp [τ'.2]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBound
section
noncomputable section

open Matrix Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

def famPQ {m n : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ)
    (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e p q y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

namespace DBoundH

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def EntD (S : Set ℂ) (f : ℂ → Matrix ι ι ℂ) : Prop := ∀ i j, DifferentiableOn ℂ (fun z => f z i j) S

theorem entD_const (S : Set ℂ) (A : Matrix ι ι ℂ) : EntD S (fun _ => A) := fun _ _ => differentiableOn_const _

theorem entD_add {S : Set ℂ} {f g : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (hg : EntD S g) :
    EntD S (fun z => f z + g z) := fun i j => by
  simp only [Matrix.add_apply]
  exact (hf i j).fun_add (hg i j)

theorem entD_mul {S : Set ℂ} {f g : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (hg : EntD S g) :
    EntD S (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hf i k).mul (hg k j)

theorem det_diff {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    DifferentiableOn ℂ (fun z => (f z).det) S := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiableOn_const _).mul (DifferentiableOn.fun_finsetProd fun i _ => hf _ _)

theorem entD_adjugate {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    EntD S (fun z => (f z).adjugate) := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine det_diff (f := fun z => (f z).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
  · simp only [Matrix.updateRow_ne hab]; exact hf a b

theorem entD_inv {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (h0 : ∀ z ∈ S, (f z).det ≠ 0) :
    EntD S (fun z => (f z)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_diff hf).inv h0).mul (entD_adjugate hf i j)

theorem trace_diff {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    DifferentiableOn ℂ (fun z => (f z).trace) S := by
  simp only [Matrix.trace, Matrix.diag]
  exact DifferentiableOn.fun_sum fun i _ => hf i i

theorem entD_aC (X : Fin n → ℝ) (S : Set ℂ) : EntD S (aC X) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j
    · subst h
      simpa [aC] using (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (X i : ℂ)))).differentiableOn
    · simpa [aC, h] using differentiableOn_const (c := (0 : ℂ))
  · simpa [aC] using differentiableOn_const (c := (0 : ℂ))
  · simpa [aC] using differentiableOn_const (c := (0 : ℂ))
  · by_cases h : i = j
    · subst h
      simpa [aC] using (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-(z * (X i : ℂ))))).differentiableOn
    · simpa [aC, h] using differentiableOn_const (c := (0 : ℂ))

theorem entD_toBlocks₁₁ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₁₁) :=
  fun i j => hf (Sum.inl i) (Sum.inl j)

theorem entD_toBlocks₁₂ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₁₂) :=
  fun i j => hf (Sum.inl i) (Sum.inr j)

theorem entD_toBlocks₂₁ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₂₁) :=
  fun i j => hf (Sum.inr i) (Sum.inl j)

theorem entD_toBlocks₂₂ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₂₂) :=
  fun i j => hf (Sum.inr i) (Sum.inr j)

theorem bigM_diff (y : GR n) (X : Fin n → ℝ) (S : Set ℂ) : EntD S (fun z => mR y * aC X z) :=
  entD_mul (entD_const _ _) (entD_aC X S)

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [Matrix.det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => by rw [← Complex.exp_add]; simp

theorem det_bigM_ne (y : GR n) (X : Fin n → ℝ) (z : ℂ) : (mR y * aC X z).det ≠ 0 := by
  rw [det_mul, det_aC, mul_one]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.1.isUnit).ne_zero

end DBoundH

namespace DBoundH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem famPQ_holo {m n : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (y : GR n)
    (u : Fin m → Fin n → ℂ) : DifferentiableOn ℂ (fun z => famPQ ε t c e p q y X z u) (stripS X) := by
  set S := stripS X
  have hM := bigM_diff y X S
  have hQ : ∀ s : ℂ, EntD S (fun z => (mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) :=
    fun s => entD_add (entD_mul (entD_toBlocks₂₁ hM) (entD_const _ _)) (entD_toBlocks₂₂ hM)
  have hP : ∀ s : ℂ, EntD S (fun z => (mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) :=
    fun s => entD_add (entD_mul (entD_toBlocks₁₁ hM) (entD_const _ _)) (entD_toBlocks₁₂ hM)
  have hd1 : ∀ z ∈ S, ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 :=
    fun z hz => (dSieg n y X z hz).2.2.1
  have hd2 : ∀ z ∈ S, ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 :=
    fun z hz => (dSieg n y X z hz).2.2.2
  have hZ1 : EntD S (fun z => ptZ y X z Complex.I) := entD_mul (hP _) (entD_inv (hQ _) hd1)
  have hZ2 : EntD S (fun z => ptZ y X z (-Complex.I)) := entD_mul (hP _) (entD_inv (hQ _) hd2)
  have hj : DifferentiableOn ℂ (fun z => jC e p q y X z) S := by
    unfold jC
    refine (((det_diff hM).zpow (Or.inl fun z _ => det_bigM_ne y X z)).mul
      ((det_diff (hQ _)).zpow (Or.inl fun z hz => hd1 z hz))).mul ((det_diff (hQ _)).zpow (Or.inl fun z hz => hd2 z hz))
  have hg : DifferentiableOn ℂ (fun z => gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u) S := by
    unfold gC
    refine DifferentiableOn.cexp ?_
    exact ((trace_diff (entD_mul hZ1 (entD_const _ _))).const_mul _).sub
      ((trace_diff (entD_mul hZ2 (entD_const _ _))).const_mul _)
  exact hj.mul hg

variable {n : ℕ} {T : Type} [TopologicalSpace T]

def EntC (S : Set T) (f : T → Matrix ι ι ℂ) : Prop := ∀ i j, ContinuousOn (fun x => f x i j) S

omit [Fintype ι] [DecidableEq ι] in
theorem entC_const (S : Set T) (A : Matrix ι ι ℂ) : EntC S (fun _ => A) := fun _ _ => continuousOn_const

omit [Fintype ι] [DecidableEq ι] in
theorem entC_add {S : Set T} {f g : T → Matrix ι ι ℂ} (hf : EntC S f) (hg : EntC S g) :
    EntC S (fun z => f z + g z) := fun i j => by
  simp only [Matrix.add_apply]
  exact (hf i j).add (hg i j)

omit [DecidableEq ι] in
theorem entC_mul {S : Set T} {f g : T → Matrix ι ι ℂ} (hf : EntC S f) (hg : EntC S g) :
    EntC S (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact continuousOn_finsetSum _ fun k _ => (hf i k).mul (hg k j)

theorem det_cont {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    ContinuousOn (fun z => (f z).det) S := by
  simp only [Matrix.det_apply]
  refine continuousOn_finsetSum _ fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => hf _ _)

theorem entC_adjugate {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    EntC S (fun z => (f z).adjugate) := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine det_cont (f := fun z => (f z).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact continuousOn_const
  · simp only [Matrix.updateRow_ne hab]; exact hf a b

theorem entC_inv {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) (h0 : ∀ z ∈ S, (f z).det ≠ 0) :
    EntC S (fun z => (f z)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_cont hf).inv₀ h0).mul (entC_adjugate hf i j)

omit [DecidableEq ι] in
theorem trace_cont {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    ContinuousOn (fun z => (f z).trace) S := by
  simp only [Matrix.trace, Matrix.diag]
  exact continuousOn_finsetSum _ fun i _ => hf i i

theorem mR_cont : Continuous fun y : GR n => mR y :=
  Units.continuous_val.comp continuous_subtype_val

theorem gramB_cont {m : ℕ} (ε : Fin m → Bool) (b : Bool) (i j : Fin n) :
    Continuous fun u : Fin m → Fin n → ℂ => gramB ε b u i j := by
  unfold gramB evX
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun k => by
    split_ifs
    · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
    · exact (continuous_apply _).comp (continuous_apply _))

theorem famPQ_cont {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) :
    ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => famPQ ε t c e p q p'.1 X p'.2.1 p'.2.2)
      (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) := by
  set S : Set (GR n × ℂ × (Fin m → Fin n → ℂ)) := Set.univ ×ˢ (stripS X ×ˢ Set.univ) with hS
  have hzS : ∀ p' ∈ S, p'.2.1 ∈ stripS X := fun p' hp => hp.2.1
  have hY : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => mR p'.1) := fun i j =>
    (((continuous_apply j).comp ((continuous_apply i).comp mR_cont)).comp continuous_fst).continuousOn
  have hA : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => aC X p'.2.1) := by
    intro i j
    have := (entD_aC X Set.univ i j).continuousOn
    exact (this.comp_continuous (continuous_fst.comp continuous_snd) (fun _ => Set.mem_univ _)).continuousOn
  have hM : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => mR p'.1 * aC X p'.2.1) := entC_mul hY hA
  have hM' : ∀ i j, ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1) i j) S := hM
  have projected_block_lower_sum : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₂₁) :=
    fun i j => hM' (Sum.inr i) (Sum.inl j)
  have lowerDiagonalBlockAsGL : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₂₂) :=
    fun i j => hM' (Sum.inr i) (Sum.inr j)
  have upper_block_rank_one_update : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₁₁) :=
    fun i j => hM' (Sum.inl i) (Sum.inl j)
  have projected_block_upper_sum : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₁₂) :=
    fun i j => hM' (Sum.inl i) (Sum.inr j)
  have hQ : ∀ s : ℂ, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      (mR p'.1 * aC X p'.2.1).toBlocks₂₁ * (s • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂) :=
    fun s => entC_add (entC_mul projected_block_lower_sum (entC_const _ _)) lowerDiagonalBlockAsGL
  have hP : ∀ s : ℂ, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      (mR p'.1 * aC X p'.2.1).toBlocks₁₁ * (s • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₁₂) :=
    fun s => entC_add (entC_mul upper_block_rank_one_update (entC_const _ _)) projected_block_upper_sum
  have hd1 : ∀ p' ∈ S, ((mR p'.1 * aC X p'.2.1).toBlocks₂₁ * (Complex.I • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂).det ≠ 0 :=
    fun p' hp => (dSieg n p'.1 X p'.2.1 (hzS p' hp)).2.2.1
  have hd2 : ∀ p' ∈ S, ((mR p'.1 * aC X p'.2.1).toBlocks₂₁ * ((-Complex.I) • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂).det ≠ 0 :=
    fun p' hp => (dSieg n p'.1 X p'.2.1 (hzS p' hp)).2.2.2
  have hZ1 : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => ptZ p'.1 X p'.2.1 Complex.I) :=
    entC_mul (hP _) (entC_inv (hQ _) hd1)
  have hZ2 : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => ptZ p'.1 X p'.2.1 (-Complex.I)) :=
    entC_mul (hP _) (entC_inv (hQ _) hd2)
  have hG : ∀ b : Bool, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => gramB (epsT t ε) b p'.2.2) := fun b i j =>
    ((gramB_cont (epsT t ε) b i j).comp (continuous_snd.comp continuous_snd)).continuousOn
  have hj : ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => jC e p q p'.1 X p'.2.1) S := by
    unfold jC
    exact (((det_cont hM).zpow₀ _ fun p' _ => Or.inl (det_bigM_ne p'.1 X p'.2.1)).mul
      ((det_cont (hQ _)).zpow₀ _ fun p' hp => Or.inl (hd1 p' hp))).mul
      ((det_cont (hQ _)).zpow₀ _ fun p' hp => Or.inl (hd2 p' hp))
  have hg : ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      gC ε t c (ptZ p'.1 X p'.2.1 Complex.I) (ptZ p'.1 X p'.2.1 (-Complex.I)) p'.2.2) S := by
    unfold gC
    refine ContinuousOn.cexp ?_
    exact (continuousOn_const.mul (trace_cont (entC_mul hZ1 (hG true)))).sub
      (continuousOn_const.mul (trace_cont (entC_mul hZ2 (hG false))))
  exact hj.mul hg

end DBoundH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcC
section
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcCH

open DCalcH DCalcBH

variable {m n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [h]

theorem det_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j))).det = Complex.exp (-(z * ∑ j, (X j : ℂ))) := by
  rw [det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem zpow_exp_neg (w : ℂ) (p : ℕ) : Complex.exp (-w) ^ (-(p : ℤ)) = Complex.exp ((p : ℂ) * w) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem jC_one (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    jC e p q 1 X z = Complex.exp (((p : ℂ) + q) * (z * ∑ j, (X j : ℂ))) := by
  unfold jC
  simp only [mR_one, Matrix.one_mul]
  rw [det_aC]
  unfold aC
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]
  rw [det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]
  congr 1
  ring

theorem inv_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j)))⁻¹ = diagonal fun j => Complex.exp (z * X j) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  conv_rhs => rw [← diagonal_one]
  congr 1
  funext j
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem ptZ_one (X : Fin n → ℝ) (z s₀ : ℂ) :
    ptZ 1 X z s₀ = s₀ • diagonal fun j => Complex.exp (2 * z * X j) := by
  unfold ptZ
  simp only [mR_one, Matrix.one_mul]
  unfold aC
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.zero_mul, zero_add, add_zero]
  rw [inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  rw [← Complex.exp_add]
  congr 1
  ring

theorem gramB_diag (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramB ε b u j j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a j) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramB, Qb, evX, map_sum, eval_X]

theorem trace_sdiag (s₀ : ℂ) (w : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    ((s₀ • diagonal w) * G).trace = s₀ * ∑ j, w j * G j j := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, diagonal_mul]

theorem famC_one (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    famC ε t c e 1 X (s : ℂ) u = fF c X 1 u s := by
  unfold famC fF fP
  rw [jC_one, ptZ_one, ptZ_one, gs_vS]
  unfold gC
  rw [trace_sdiag, trace_sdiag]
  simp only [gramB_diag, evX_eq, map_one, one_mul]
  have hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ) := by
    rw [← Nat.cast_add, cnt_add]
  rw [hpq, ← Complex.exp_add, Complex.ofReal_exp]
  have hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) +
      (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)
    simp only [Bool.not_eq_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold nS
  push_cast
  simp only [e2]
  have key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) -
      Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      -((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [← hsum, mul_add, Finset.sum_add_distrib]
    linear_combination ((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j +
      (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI
  rw [key, ← Complex.exp_add]
  have hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j := by
    intro E N
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  congr 1
  push_cast
  rw [hswap]
  ring

end DCalcCH

end PositivityTheory.Rg.Sw.Glob
end
end

