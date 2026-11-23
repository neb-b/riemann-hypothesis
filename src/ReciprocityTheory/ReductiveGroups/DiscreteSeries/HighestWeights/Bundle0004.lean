module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0002
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen
section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Pre

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def preUnits (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)) : Fin n → Fin n → Module.End ℂ V :=
  fun a b => ((dτ (Matrix.single a b 1) : V →L[ℂ] V) : Module.End ℂ V)

variable [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)


include hcont hder in
theorem pre_kRel : Formalism.REAL.KRel ε (preUnits dτ) := by
  intro a b c d hab hcd
  have hbr := pre_dτ_bracket_single τ dτ hder hab hcd
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1 h2; simp [Matrix.single_mul_single_same]
    · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
    · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
    · simp [Matrix.single_mul_single_of_ne, Matrix.single_mul_single_of_ne, h1, h2]
  rw [hm] at hbr
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun F : V →L[ℂ] V => F x) hbr
  have e : ∀ A B : V →L[ℂ] V, (A * B) x = A (B x) := fun _ _ => rfl
  simp only [_root_.sub_apply, e, map_sub] at hx
  simp only [preUnits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  rw [hx]
  split_ifs <;> simp

include hcont hder in
theorem pre_kUnit : Formalism.REAL.KUnit ε (preUnits dτ) := by
  intro a b hab x y
  show ⟪dτ (Matrix.single a b 1) x, y⟫_ℂ = ⟪x, dτ (Matrix.single b a 1) y⟫_ℂ
  rw [← pre_star_dτ_single τ dτ hder hab, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem pre_dτ_stable_of_kStable (W : Submodule ℂ V) (hW : Formalism.REAL.KStable ε (preUnits dτ) W) :
    ∀ Y, inK ε Y → ∀ v ∈ W, dτ Y v ∈ W := by
  intro Y hY v hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.matrix_eq_sum_single Y, map_sum, _root_.sum_apply]
  refine W.sum_mem fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, _root_.sum_apply]
  refine W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · have e : Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 := by
      ext i j; simp [Matrix.single_apply]
    rw [e, map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab v hv)
  · have e : Matrix.single a b (Y a b) = 0 := by
      rw [inK_entry_eq_zero hY hab]; ext i j; simp [Matrix.single_apply]
    rw [e, map_zero, _root_.zero_apply]
    exact W.zero_mem


include hcont hder in
theorem pre_kStable_of_stable (W : Submodule ℂ V)
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) :
    Formalism.REAL.KStable ε (preUnits dτ) W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := hder X hX γ hγ
    have hdv : HasDerivAt (fun t : ℝ => preOp τ (γ t) v) (dτ X v) 0 := by
      have := ((ContinuousLinearMap.apply ℂ V v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    rw [hasDerivAt_iff_tendsto_slope] at hdv
    have hcl : IsClosed (W : Set V) := W.closed_of_finiteDimensional
    refine hcl.mem_of_tendsto hdv (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module, SetLike.mem_coe]
    exact Submodule.smul_of_tower_mem W _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  show dτ (Matrix.single a b 1) v ∈ W
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1
  have hA : A * Jm ε = Jm ε * A := single_mul_Jm_comm hab 1
  have hB : B * Jm ε = Jm ε * B := single_mul_Jm_comm hab.symm 1
  have hAB : Aᴴ = B := by
    ext i j
    simp only [A, B, Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]
  have hBA : Bᴴ = A := by rw [← hAB, Matrix.conjTranspose_conjTranspose]
  have h1 : inK ε (A - B) := inK_of_skew_comm (by rw [Matrix.conjTranspose_sub, hAB, hBA, neg_sub])
    (by rw [sub_mul, mul_sub, hA, hB])
  have h2 : inK ε (Complex.I • (A + B)) := inK_of_skew_comm
    (by rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hAB, hBA, Complex.star_def,
      Complex.conj_I, add_comm, neg_smul])
    (by rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hA, hB])
  have e : A = (1 / 2 : ℂ) • (A - B) - (Complex.I / 2) • (Complex.I • (A + B)) := by
    rw [smul_smul, show Complex.I / 2 * Complex.I = -(1 / 2 : ℂ) by
      rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring]
    module
  rw [e, map_sub, map_smul, map_smul, _root_.sub_apply, _root_.smul_apply,
    _root_.smul_apply]
  exact W.sub_mem (W.smul_mem _ (hK _ h1 v hv)) (W.smul_mem _ (hK _ h2 v hv))


include hcont hder in
theorem pre_kSpan_stable (x : V) (k : KG ε) :
    ∀ v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x,
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x := by
  have hS : Formalism.REAL.KStable ε (preUnits dτ) (Formalism.REAL.kSpan ε (preUnits dτ) x) := by
    intro a b hab y hy
    unfold Formalism.REAL.kSpan at hy ⊢
    rw [Submodule.mem_sInf] at hy ⊢
    intro S hS
    exact hS.2 a b hab y (hy S hS)
  obtain ⟨Y, hY, he⟩ := pre_op_eq_exp' τ dτ hder k
  rw [show ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = NormedSpace.exp (dτ Y) from he]
  exact exp_mem_of_stable _ _ (pre_dτ_stable_of_kStable dτ _ hS Y hY)


include hcont hder in
theorem irred_of_gen {Λ : Fin n → ℝ} (w : V)
    (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) :
    ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hx : w ∈ Formalism.REAL.kSpan ε (preUnits dτ) w := by
    unfold Formalism.REAL.kSpan
    rw [Submodule.mem_sInf]
    intro S hS
    exact hS.1
  have htop : Formalism.REAL.kSpan ε (preUnits dτ) w = ⊤ :=
    hgen _ (pre_kSpan_stable τ hcont dτ hder w) hx
  have hhi : Formalism.REAL.KHighest ε (preUnits dτ) Λ w :=
    ⟨fun a => hwt a, fun a b hab he => hhw a b hab he⟩
  have := Formalism.REAL.kIrr V n ε (preUnits dτ) Λ w inferInstance (pre_kRel τ hcont dτ hder)
    (pre_kUnit τ hcont dτ hder) hhi W (htop ▸ le_top) (pre_kStable_of_stable τ hcont dτ hder W hW)
  rwa [htop] at this

end Pre

def kTypeOfGen {ε : Fin n → Bool} {Λ : Fin n → ℝ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
    (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
    (w : V) (hw : ‖w‖ = 1) (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) : KType ε Λ where
  V := V
  τ := τ
  cont := hcont
  irred := irred_of_gen τ hcont dτ hder w hwt hhw hgen
  dτ := dτ
  hasDeriv := hder
  w := w
  w_norm := hw
  w_wt := hwt
  w_hw := hhw

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma uq_offdiag_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    {a b : Fin n} (hab : ε a ≠ ε b) : X a b = 0 := by
  have hd : (if ε a then (1 : ℂ) else -1) ≠ (if ε b then (1 : ℂ) else -1) := by
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab ⊢ <;> norm_num
  have h := congrFun (congrFun hX a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : X a b * ((if ε b then (1 : ℂ) else -1) - (if ε a then (1 : ℂ) else -1)) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hd

lemma uq_kHighest {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w :=
  ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

theorem kType_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T T' : KType ε Λ) :
    ∃ φ : T.V ≃ₗᵢ[ℂ] T'.V, (∀ (k : KG ε) (v : T.V), φ (T.op k v) = T'.op k (φ v)) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X → ∀ v : T.V, φ (T.dτ X v) = T'.dτ X (φ v)) ∧
      φ T.w = T'.w := by
  obtain ⟨φ, hφF, hφw⟩ := uq_exists_isometry ε (kunits T) (kunits T') Λ T.w T'.w (KType.kRel T)
    (KType.kRel T') (KType.kUnit T) (KType.kUnit T') (uq_kHighest T) (uq_kHighest T') T.w_norm
    T'.w_norm (KType.kSpan_eq_top T) (KType.kSpan_eq_top T')
  have expand : ∀ (S : KType ε Λ) (X : Matrix (Fin n) (Fin n) ℂ) (u : S.V),
      S.dτ X u = ∑ a, ∑ b, X a b • S.dτ (Matrix.single a b 1) u := by
    intro S X u
    have hs : ∀ i j, Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := fun i j => by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hs, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hdτ : ∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X → ∀ v : T.V,
      φ (T.dτ X v) = T'.dτ X (φ v) := by
    intro X hX v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [expand T X v, expand T' X (φ v), map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : ε a = ε b
    · rw [map_smul]
      congr 1
      exact hφF a b h v
    · rw [uq_offdiag_zero hX h, zero_smul, zero_smul, map_zero]
  refine ⟨φ, ?_, hdτ, hφw⟩
  intro k v
  obtain ⟨Y, hY, hkY⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : toMK (γ 1) = toMK k := by
    rw [hγ 1, hkY]
    simp
  have hk : γ 1 = k := Subtype.ext (Subtype.ext (Units.ext h1))
  have hop : ∀ S : KType ε Λ, S.op k = NormedSpace.exp (S.dτ Y) := by
    intro S
    rw [← hk, KType.op_curve S hY γ hγ 1]
    simp
  rw [hop T, hop T']
  let f := φ.toContinuousLinearEquiv.conjContinuousAlgEquiv
  have hf : f (T.dτ Y) = T'.dτ Y := by
    ext u
    simp only [f, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, hdτ Y hY.2]
    simp
  letI : NormedAlgebra ℚ (T.V →L[ℂ] T.V) := NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ (T'.V →L[ℂ] T'.V) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hexp := NormedSpace.map_exp f (map_continuous f) (T.dτ Y)
  rw [hf] at hexp
  rw [← hexp]
  simp [f, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

