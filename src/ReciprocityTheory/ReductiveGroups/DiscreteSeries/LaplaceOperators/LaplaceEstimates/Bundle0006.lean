module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.BasePointPsiExpFormula
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmDSingleMulVec

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.BlockEmbeddingSkewHermitian
section
noncomputable section

open Matrix Finset Filter

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N TransportGeo

variable {k r : ℕ}

def kap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Fin r) : ℝ :=
  if p.val + 1 < r then 1 else Real.sqrt (Tz k r z)

def LF (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Y : Mat k r) : ℂ :=
  ∑ p, c p * (kap k r z p * Y (eI k r p) (nxt k r p))

theorem ellA_frame {z : Fin (2 * r + k + 1) → ℂ} {g₀ : Mat k r} (hg : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hT : 0 < Tz k r z) (m : Mat k r) (p : Fin r) :
    Formalism.MainNotions.S.ellA k r z (g₀ * m * g₀⁻¹) p = kap k r z p * m (eI k r p) (nxt k r p) := by
  have hc := (colStd_iff g₀).mpr hg.2.1
  have hM := hc.midM hg.1
  have hrow : ∀ v : Fin (2 * r + k + 1) → ℂ, (g₀ *ᵥ v) (eI k r p) = v (eI k r p) := fun v => by
    simp only [Matrix.mulVec, dotProduct, fun j => hM (eI k r p) j (Or.inl (Or.inl p.isLt)), ite_mul,
      one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
  have hs : (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne')
  unfold Formalism.MainNotions.S.ellA kap nxt
  split_ifs with h
  · have e1 : ∀ X : Mat k r, X (eI k r p) (eI k r ⟨p.val + 1, h⟩) =
        (X *ᵥ bvec (eI k r ⟨p.val + 1, h⟩)) (eI k r p) := fun X => by simp [bvec]
    rw [e1 (g₀ * m * g₀⁻¹), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hc.inv hg.1 _ (Or.inl h), hrow, ← e1 m, Complex.ofReal_one, one_mul]
    rfl
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      inv_mulVec (uh_det hg.1) hs (frame_mulVec hg hT), inv_inv, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Pi.smul_apply, hrow]
    simp [z0, bvec, wI]

theorem conj_lie {g₀ Y : Mat k r} (hg : g₀ ∈ UH (Hpk k r)) (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) :
    (g₀ * Y * g₀⁻¹)ᴴ * Hpk k r + Hpk k r * (g₀ * Y * g₀⁻¹) = 0 := by
  have h1 : (g₀⁻¹)ᴴ * Hpk k r * g₀⁻¹ = Hpk k r := uh_inv hg
  have hd := uh_det hg
  have e1 : Hpk k r * (g₀ * Y * g₀⁻¹) = (g₀⁻¹)ᴴ * (Hpk k r * Y) * g₀⁻¹ := by
    conv_lhs => rw [← h1]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  have e2 : (g₀ * Y * g₀⁻¹)ᴴ * Hpk k r = (g₀⁻¹)ᴴ * (Yᴴ * Hpk k r) * g₀⁻¹ := by
    have h2 : g₀ᴴ * (g₀⁻¹)ᴴ = 1 := by
      rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hd, conjTranspose_one]
    conv_lhs => rw [← h1]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g₀ᴴ, h2, Matrix.one_mul]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hY, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_frame {g₀ : Mat k r} (hg : g₀ ∈ UH (Hpk k r)) (Y : Mat k r) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (g₀ * Y * g₀⁻¹)) = g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ := by
  rw [← Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det g₀).mpr (uh_det hg)), Matrix.mul_smul,
    Matrix.smul_mul]

open scoped Matrix.Norms.Operator in
theorem lieN_facts {z : Fin (2 * r + k + 1) → ℂ} (c : Fin r → ℂ) {g₀ Y : Mat k r}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g₀) (hT : 0 < Tz k r z) (h1 : Y ∈ levF (levB k r) 0)
    (h2 : Hpk k r * Yᴴ * Hpk k r = -Y) :
    Yᴴ * Hpk k r + Hpk k r * Y = 0 ∧ ∀ t : ℝ,
      g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ ∈ Nset k r ∧
      Formalism.MainNotions.S.psiGen k r z c (g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹) =
        Complex.exp ((t : ℂ) * (Complex.I * ((LF z c Y).re : ℂ))) := by
  have hc := (colStd_iff g₀).mpr hg.2.1
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · have := congrArg (fun X => Hpk k r * X) h2
    simp only [← Matrix.mul_assoc, Hpk_sq, Matrix.one_mul, Matrix.mul_neg] at this
    rw [this, neg_add_cancel]
  · have hY : Y ∈ Formalism.MainNotions.S.lieOf (Nset k r) := by
      rw [lieOf_Nset_eq]; exact mem_lieN.mpr ⟨h1, h2⟩
    exact conj_mem_N hg.1 (hc.midM hg.1).lev0 ((hc.inv hg.1).midM (uh_inv hg.1)).lev0 (hY t)
  · have h3 : (t : ℂ) • Y ∈ levF (levB k r) 0 := fun a b h => by simp [h1 a b h]
    unfold Formalism.MainNotions.S.psiGen
    simp only [ellA_frame hg hT, exp_entry _ h3]
    have : (∑ p, c p * (kap k r z p * ((t : ℂ) • Y) (eI k r p) (nxt k r p))) = t * LF z c Y := by
      simp only [LF, mul_sum, Matrix.smul_apply, smul_eq_mul]
      exact sum_congr rfl fun p _ => by ring
    rw [this, Complex.re_ofReal_mul]
    congr 1; push_cast; ring

def emb0 (k r : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Mat k r where
  toFun A := Formalism.MainNotions.S.blockW k r A - Formalism.MainNotions.S.blockW k r 0
  map_add' A B := by
    ext i j; simp only [Formalism.MainNotions.S.blockW, Matrix.sub_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' t A := by
    ext i j; simp only [Formalism.MainNotions.S.blockW, Matrix.sub_apply, Matrix.smul_apply]; split_ifs <;> simp

theorem block_embedding_single (i j : Fin k) :
    emb0 k r (Matrix.single i j 1) = Matrix.single (StandardBasisEmbedding.eB k r i) (StandardBasisEmbedding.eB k r j) 1 := by
  ext a b
  simp only [emb0, LinearMap.coe_mk, AddHom.coe_mk, Formalism.MainNotions.S.blockW, Matrix.sub_apply,
    Matrix.single_apply, StandardBasisEmbedding.eB, Fin.ext_iff]
  have := i.isLt
  have := j.isLt
  split_ifs <;> first | omega | simp

open scoped Matrix.Norms.Operator in
theorem exp_embed (A : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 k r A) = Formalism.MainNotions.S.blockW k r (NormedSpace.exp A) := by
  set B0 := Formalism.MainNotions.S.blockW k r (0 : Matrix (Fin k) (Fin k) ℂ) with hB0
  have hb : ∀ X, Formalism.MainNotions.S.blockW k r X = emb0 k r X + B0 := fun X => (sub_add_cancel _ _).symm
  have l0 : ∀ X, B0 * Formalism.MainNotions.S.blockW k r X = B0 := fun X => by rw [hB0, ← StandardBasisEmbedding.blockW_mul, zero_mul]
  have r0 : ∀ X, Formalism.MainNotions.S.blockW k r X * B0 = B0 := fun X => by rw [hB0, ← StandardBasisEmbedding.blockW_mul, mul_zero]
  have b0 : B0 * B0 = B0 := l0 0
  let f : Matrix (Fin k) (Fin k) ℂ × ℂ →+* Mat k r :=
    { toFun := fun x => emb0 k r x.1 + x.2 • B0
      map_one' := by
        show emb0 k r 1 + (1 : ℂ) • B0 = 1
        rw [one_smul, ← hb, StandardBasisEmbedding.blockW_one]
      map_mul' := fun x y => by
        show (Formalism.MainNotions.S.blockW k r (x.1 * y.1) - B0) + (x.2 * y.2) • B0 =
          (Formalism.MainNotions.S.blockW k r x.1 - B0 + x.2 • B0) * (Formalism.MainNotions.S.blockW k r y.1 - B0 + y.2 • B0)
        simp only [StandardBasisEmbedding.blockW_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_smul, Matrix.smul_mul, l0, r0, b0, sub_self, smul_smul, zero_add,
          mul_comm y.2 x.2]
        abel
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), add_smul]; abel }
  have hf : Continuous f :=
    ((emb0 k r).continuous_of_finiteDimensional.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have h := NormedSpace.map_exp f hf (A, (0 : ℂ))
  have e1 : f (A, (0 : ℂ)) = emb0 k r A := by simp [f]
  have e2 : f (NormedSpace.exp (A, (0 : ℂ))) = Formalism.MainNotions.S.blockW k r (NormedSpace.exp A) := by
    have a1 := Prod.fst_exp (A, (0 : ℂ))
    have a2 := (Prod.snd_exp (A, (0 : ℂ))).trans NormedSpace.exp_zero
    refine (congrArg₂ (fun (X : Matrix (Fin k) (Fin k) ℂ) (t : ℂ) => emb0 k r X + t • B0) a1 a2).trans ?_
    simp only [one_smul]
    exact (hb _).symm
  exact (congrArg NormedSpace.exp e1.symm).trans (h.symm.trans e2)

theorem block_embedding_skew_hermitian {A : Matrix (Fin k) (Fin k) ℂ} (hA : Aᴴ = -A) :
    (emb0 k r A)ᴴ * Hpk k r + Hpk k r * emb0 k r A = 0 := by
  have h1 : (emb0 k r A)ᴴ = -emb0 k r A := by
    rw [← map_neg, ← hA]
    show (Formalism.MainNotions.S.blockW k r A - Formalism.MainNotions.S.blockW k r 0)ᴴ = _ - _
    rw [conjTranspose_sub, StandardBasisEmbedding.blockW_conjTranspose, StandardBasisEmbedding.blockW_conjTranspose, conjTranspose_zero]
  have h2 : Hpk k r * emb0 k r A = emb0 k r A * Hpk k r := by
    show Hpk k r * (_ - _) = (_ - _) * Hpk k r
    rw [Matrix.mul_sub, Matrix.sub_mul, StandardBasisEmbedding.H_comm, StandardBasisEmbedding.H_comm]
  rw [h1, h2, Matrix.neg_mul, neg_add_cancel]

theorem frame_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g₀ : Mat k r} (hg : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hT : 0 < Tz k r z) {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g₀ * Formalism.MainNotions.S.blockW k r h * g₀⁻¹ ∈ UWset k r z := by
  have hm := StandardBasisEmbedding.mem_UW (r := r) hh
  have hc := (colStd_iff g₀).mpr hg.2.1
  have hs : (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne')
  exact ⟨uh_mul (uh_mul hg.1 hm.1) (uh_inv hg.1),
    (colStd_iff _).mp ((hc.mul ((colStd_iff _).mpr hm.2.1)).mul (hc.inv hg.1)),
    (fix_iff (uh_det hg.1) hs (frame_mulVec hg hT) _).mp hm.2.2⟩

theorem exists_derived {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (ρ : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp)) (hρ : Formalism.MainNotions.S.IsHCTypeU k u ρ) :
    ∃ dρ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Module.End ℂ Vp,
      (∀ A : Matrix (Fin k) (Fin k) ℂ, Aᴴ = -A → ∀ v, HasDerivAt
        (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • A)) v) (dρ A v) 0) ∧
      ∀ (x : ℂ) (ζ : Vp), Capelli.capelliC (fun i j => dρ (Matrix.single i j 1)) x ζ =
        (∏ j : Fin k, (x + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) • ζ := by
  obtain ⟨T, U, hU⟩ := HW.kType_of_hcTypeU ρ hρ
  let dρ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Module.End ℂ Vp :=
    (U.symm.toLinearEquiv.conj : Module.End ℂ T.V →ₗ[ℂ] Module.End ℂ Vp) ∘ₗ
      (ContinuousLinearMap.coeLM ℂ) ∘ₗ T.dτ
  have hd : ∀ A v, dρ A (U.symm v) = U.symm (T.dτ A v) := fun A v => by
    simp [dρ, LinearEquiv.conj_apply]
  refine ⟨dρ, fun A hA v => ?_, fun x ζ => ?_⟩
  · have hK : inK (fun _ : Fin k => true) A := (HW.inK_iff' _ A).mpr ⟨hA, by simp [Jm]⟩
    obtain ⟨γ, hγ⟩ := HW.exists_curve _ hK
    have h1 := (((U.symm.toContinuousLinearEquiv : T.V →L[ℂ] Vp).comp
      (ContinuousLinearMap.apply ℂ T.V (U v))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (T.hasDeriv A hK γ hγ)
    refine HasDerivAt.congr_deriv (h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
    · show ρ _ v = U.symm (T.op (γ t) (U v))
      rw [← hU, hγ, U.symm_apply_apply]
    · have := hd A (U v)
      rw [U.symm_apply_apply] at this
      exact this.symm
  · have hk : ∀ a b v, dρ (Matrix.single a b 1) (U.symm v) = U.symm (HW.kunits T a b v) :=
      fun a b v => hd _ v
    have hE : IsGlRep fun i j => dρ (Matrix.single i j 1) := fun a b c d => by
      ext v
      obtain ⟨v, rfl⟩ := U.symm.surjective v
      have := congrArg U.symm (LinearMap.congr_fun (HW.KType.kRel T a b c d rfl rfl) v)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hk, map_sub] at this ⊢
      rw [this]
      congr 1 <;> split_ifs <;> simp [hk]
    have hw : IsHWVec (fun i j => dρ (Matrix.single i j 1)) (lowK (fun _ : Fin k => true) u)
        (U.symm T.w) := ⟨fun a => by rw [hd, T.w_wt, map_smul], fun a b h => by
      rw [hd, T.w_hw a b h rfl, map_zero]⟩
    have hgen : ζ ∈ genSub (fun i j => dρ (Matrix.single i j 1)) (Submodule.span ℂ {U.symm T.w}) := by
      refine Submodule.mem_sInf.mpr fun S hS => ?_
      have h1 : Formalism.REAL.kSpan (fun _ : Fin k => true) (HW.kunits T) T.w ≤
          S.comap U.symm.toLinearEquiv.toLinearMap :=
        sInf_le ⟨hS.1 (Submodule.subset_span rfl), fun a b _ v hv => by
          show U.symm (HW.kunits T a b v) ∈ S
          rw [← hk]; exact hS.2 a b _ hv⟩
      rw [HW.KType.kSpan_eq_top] at h1
      simpa using h1 (Submodule.mem_top (x := U ζ))
    rw [Capelli.capelliC_genSub _ hE _ _ hw x ζ hgen]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    have h1 : (univ.filter fun b : Fin k => j < b) = Ioi j := by ext; simp
    have h2 : (univ.filter fun b : Fin k => b < j) = Iio j := by ext; simp
    have h3 : j.val + 1 ≤ k := j.isLt
    simp only [lowK, rhoN, rhoC, Pi.sub_apply, Pi.add_apply, and_true, ne_eq, not_true_eq_false,
      and_false, filter_false, card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio, Nat.sub_sub,
      Nat.cast_sub (by omega : 1 + j.val ≤ k)]
    push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FrameForm
section
noncomputable section

open Matrix MeasureTheory Filter

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}
  {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
  [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
  {μW μN : Measure (Mt k r)} {P x₀ g : Mat k r} {w : H} {a : ℝ}

theorem good_bound {m : H} (hm : TmGood ε σ x₀ w a m) :
    ∃ C : ℝ, ∀ y ∈ UJset ε, ‖coefX σ x₀ w m y‖ ≤ C * frob y ^ (1 - a) := by
  obtain ⟨C, hC⟩ := hm.2 []
  refine ⟨|C|, fun y hy => (hC y hy).trans ?_⟩
  have h1 := tmA_one_le_frob hy (0 : Fin (2 * r + k + 1))
  exact mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
    (Real.rpow_nonneg (by linarith) _) (abs_nonneg C)

theorem per_lin (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {m m' : H} (hm : TmGood ε σ x₀ w a m)
    (hm' : TmGood ε σ x₀ w a m') (t : ℂ) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m + t • m')) ξ g =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m) ξ g +
        t • per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w m') ξ g := by
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have i1 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm.1) C hC
  have i2 := CurveContinuity.int_of_bound hP hB hg ξ a hb _ (CurveContinuity.smooth_contOn hm'.1) C' hC'
  unfold per sInt
  rw [← integral_smul]
  refine Eq.trans ?_ (integral_add i1 (i2.smul t))
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [coefX, map_add (f := _), map_smul, inner_add_right, inner_smul_right, add_smul, smul_smul,
    Pi.smul_apply]

theorem frame_form (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hg : g ∈ UH (Hpk k r)) :
    IsUnit (g * P⁻¹).det ∧ (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = Jm ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine ⟨by rw [Matrix.det_mul]; exact (TransportGeo.uh_det hg).mul (Matrix.isUnit_nonsing_inv_det P hd),
    ?_⟩
  calc (g * P⁻¹)ᴴ * Hpk k r * (g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * Hpk k r * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * Pᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by rw [hg', ← hP.2]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]; rfl

theorem mul_inUJ (hP : Formalism.MainNotions.S.IsCayley k r ε P) {y : Mat k r} (hy : y ∈ UH (Hpk k r)) :
    P * y * P⁻¹ ∈ UJset ε := by
  show (P * y * P⁻¹)ᴴ * Jm ε * (P * y * P⁻¹) = Jm ε
  have h := (frame_form hP hy).2
  rw [← hP.2] at h
  refine Eq.trans ?_ h
  show (P * y * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * y * P⁻¹) = _
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem per_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hx₀ : x₀ ∈ UJset ε)
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN) (hg : g ∈ UH (Hpk k r))
    (hb : S0.bS k r < a - 1) (ξ : Vp) {Y : Mat k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) (m : D)
    (hm : TmGood ε σ x₀ w a (m : H))
    (hm' : TmGood ε σ x₀ w a ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) :
    HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ w (m : H)) ξ
        (NormedSpace.exp ((t : ℂ) • Y) * g))
      (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
        (coefX σ x₀ w ((actM E ((g * P⁻¹)⁻¹ * Y * (g * P⁻¹)) m : D) : H)) ξ g) 0 := by
  obtain ⟨hR, hJ⟩ := frame_form hP hg
  set R := g * P⁻¹ with hRd
  have hX : inG ε (R⁻¹ * Y * R) := by
    have e1 : Jm ε * (R⁻¹ * Y * R) = Rᴴ * (Hpk k r * Y) * R := by
      rw [← hJ]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hR]
    have e2 : (R⁻¹ * Y * R)ᴴ * Jm ε = Rᴴ * (Yᴴ * Hpk k r) * R := by
      have h2 : (R⁻¹)ᴴ * Rᴴ = 1 := by
        rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hR, conjTranspose_one]
      rw [← hJ]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (R⁻¹)ᴴ, h2, Matrix.one_mul]
    show (R⁻¹ * Y * R)ᴴ * Jm ε + Jm ε * (R⁻¹ * Y * R) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hY, Matrix.mul_zero, Matrix.zero_mul]
  have hRd' : ∀ y ∈ UJset ε, Formalism.REAL.Rd (R⁻¹ * Y * R) (coefX σ x₀ w (m : H)) y =
      coefX σ x₀ w ((actM E (R⁻¹ * Y * R) m : D) : H) y := fun y hy =>
    tmB_rd_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hy) hX w m
  obtain ⟨C, hC⟩ := good_bound hm
  obtain ⟨C', hC'⟩ := good_bound hm'
  have h := (CurveContinuity.deriv_int hP hB hg ξ a hb _ hm.1 C hC _ hX C'
    (fun y hy => by rw [hRd' y hy]; exact hC' y hy)).2
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · have e : NormedSpace.exp ((t : ℂ) • (R⁻¹ * Y * R)) = R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R := by
      rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det R).mpr hR), Matrix.mul_smul,
        Matrix.smul_mul]
    simp only [per, sInt, e]
    congr 1
    funext p
    congr 2
    calc _ = P * (Matrix.of p.1 * Matrix.of p.2) * (NormedSpace.exp ((t : ℂ) • Y) * R) := by
          rw [hRd]; simp only [Matrix.mul_assoc]
      _ = P * (Matrix.of p.1 * Matrix.of p.2) * (R * (R⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * R))) := by
          rw [Matrix.mul_nonsing_inv_cancel_left _ _ hR]
      _ = _ := by
          rw [← Matrix.mul_assoc R⁻¹]
          generalize R⁻¹ * NormedSpace.exp ((t : ℂ) • Y) * R = A
          rw [hRd]; simp only [Matrix.mul_assoc]
  · unfold per sInt
    refine integral_congr_ae ?_
    filter_upwards [CurveContinuity.ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp
    rw [hRd' _ (mul_inUJ hP (TransportGeo.uh_mul (TransportGeo.uh_mul hp.1.1 hp.2.1) hg))]

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

