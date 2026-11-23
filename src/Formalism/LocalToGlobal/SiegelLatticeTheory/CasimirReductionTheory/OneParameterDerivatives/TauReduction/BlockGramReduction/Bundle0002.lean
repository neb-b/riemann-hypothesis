module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0073

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.KsetInvMem
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem kset_inv_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hk

theorem t4 : LatticeRightInvariant := by
  intro I x y k hk
  ext u
  show (I.fmat (x * (y, k)).2⁻¹) *ᵥ _ ∈ I.Lf ↔ (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
  have hk' : ∀ w, w ∈ I.Lf ↔ I.fmat k⁻¹ *ᵥ w ∈ I.Lf := kset_inv_mem I hk
  have e : I.fmat (x * (y, k)).2⁻¹ = I.fmat k⁻¹ * I.fmat x.2⁻¹ := by
    simp only [AutInst.fmat, Prod.snd_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]
  exact (hk' _).symm

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.LatticeFinitelyGeneratedOfCommensurable
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem inclE_mem_intAf (I : AutInst) (c : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) ∈ IntAf I.F I.E := by
  apply Subring.subset_closure
  left
  exact ⟨⟨(c : I.E), c, rfl⟩, rfl⟩

def latSubmodule (I : AutInst) (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := latSet I x
  zero_mem' := by
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have : (fun i : Fin I.n => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
      funext i; simp
    rw [this, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  add_mem' := by
    intro u w hu hw
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((u + w) i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) +
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
      funext i; simp
    rw [h, Matrix.mulVec_add]
    exact I.Lf.add_mem hu hw
  smul_mem' := by
    intro c u hu
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((c • u) i)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) •
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) := by
      funext i
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul]
    have := I.Lf.smul_mem (⟨_, inclE_mem_intAf I c⟩ : IntAf I.F I.E) hu
    exact this

theorem coe_latSubmodule (I : AutInst) (x : I.GA) :
    ((latSubmodule I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = latSet I x := rfl

theorem lattice_finitelyGenerated_of_commensurable (h0 : LatticeCommensurable) : LatticeFinitelyGenerated := by
  intro I x
  obtain ⟨m, hm1, hA, -⟩ := h0 I x
  refine ⟨latSubmodule I x, ?_, coe_latSubmodule I x⟩
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    (((m : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
  have hle : latSubmodule I x ≤ I.L.map φ := by
    intro u hu
    refine ⟨(m : I.E) • u, hA u hu, ?_⟩
    simp [φ, smul_smul, inv_mul_cancel₀ hm0]
  have hfg : (I.L.map φ).FG := I.L_fg.map φ
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  have h1 := IsNoetherian.noetherian ((latSubmodule I x).comap (I.L.map φ).subtype)
  have h2 := h1.map (I.L.map φ).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.LatticeVectorsBoundedBelow
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem one_le_norm_embedding_alt (I : AutInst) (a : 𝓞 I.E) (ha : a ≠ 0) :
    ∃ v, 1 ≤ ‖I.φ v (a : I.E)‖ := by
  set β : I.E := (a : I.E) * star (a : I.E) with hβ
  have hfix : star β = β := by simp [hβ, mul_comm]
  obtain ⟨γ, hγ⟩ := (I.cm.fixed β).1 hfix
  have haI : IsIntegral ℤ (a : I.E) := a.2
  have hsI : IsIntegral ℤ (star (a : I.E)) := IsIntegral.map I.cm.sig haI
  have hβI : IsIntegral ℤ β := haI.mul hsI
  have hγI : IsIntegral ℤ γ := by
    rw [← isIntegral_algebraMap_iff (B := I.E), hγ]
    exact hβI
  have ha0 : (a : I.E) ≠ 0 := by simpa using ha
  have hβ0 : β ≠ 0 := mul_ne_zero ha0 (star_ne_zero.2 ha0)
  let g : 𝓞 I.F := ⟨γ, hγI⟩
  have hg0 : g ≠ 0 := by
    intro h
    apply hβ0
    rw [← hγ]
    have : γ = 0 := congrArg Subtype.val h
    simp [this]
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace I.F, 1 ≤ w (g : I.F) := by
    by_contra h
    push Not at h
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w₀) hg0 (fun z _ => h z)) (not_le.2 (h w₀))
  refine ⟨w, ?_⟩
  have e : w (g : I.F) = ‖I.φ w (a : I.E)‖ ^ 2 := by
    rw [← InfinitePlace.norm_embedding_eq, show (g : I.F) = γ from rfl, ← I.φ_over, hγ, hβ, map_mul,
      I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj, sq]
  rw [e] at hw
  by_contra h
  push Not at h
  nlinarith [norm_nonneg (I.φ w (a : I.E))]

theorem lattice_common_denominator (I : AutInst) : ∃ b : 𝓞 I.E, b ≠ 0 ∧
    ∀ y ∈ I.L, ∀ i, ∃ c : 𝓞 I.E, (c : I.E) = (b : I.E) * y i := by
  first | exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator .. | (apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator I

theorem invertible_matrix_lower_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : Fin n → ℂ) (i : Fin n), ‖w i‖ ^ 2 ≤ C * ∑ k, ‖(A *ᵥ w) k‖ ^ 2 := by
  obtain ⟨U, rfl⟩ := hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  refine ⟨∑ i, ∑ k, ‖B i k‖ ^ 2 + 1, by positivity, fun w i => ?_⟩
  set z := (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w
  have hw : w = B *ᵥ z := by
    simp only [z, B, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h1 : ‖w i‖ ≤ ∑ k, ‖B i k‖ * ‖z k‖ := by
    rw [hw]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 : ‖w i‖ ^ 2 ≤ (∑ k, ‖B i k‖ ^ 2) * ∑ k, ‖z k‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ k, ‖B i k‖ ^ 2 ≤ ∑ i, ∑ k, ‖B i k‖ ^ 2 + 1 := by
    have := Finset.single_le_sum (f := fun i => ∑ k, ‖B i k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))

theorem lattice_vectors_bounded_below (h0 : LatticeCommensurable) : LatticeVectorsBoundedBelow := by
  intro I x
  obtain ⟨m, hm1, hm, -⟩ := h0 I x
  obtain ⟨b, hb0, hb⟩ := lattice_common_denominator I
  have hC : ∀ v, ∃ C : ℝ, 0 < C ∧ ∀ (u : Fin I.n → I.E) (i : Fin I.n),
      ‖I.φ v (u i)‖ ^ 2 ≤ C * ∑ k, ‖coordV I x v u k‖ ^ 2 := fun v => by
    have hU : IsUnit (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) :=
      (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
    obtain ⟨C, hC, hCw⟩ := invertible_matrix_lower_bound _ hU
    exact ⟨C, hC, fun u i => hCw (fun i => I.φ v (u i)) i⟩
  choose C hCpos hCb using hC
  set K : ℝ := ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v :=
      Finset.sum_nonneg fun w _ => by have := hCpos w; positivity
    linarith
  refine ⟨1 / K, by positivity, ?_⟩
  intro u hu hu0
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨c, hc⟩ := hb _ (hm u hu) i
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0' : (b : I.E) ≠ 0 := by simpa using hb0
  have hc0 : c ≠ 0 := by
    intro h
    have : (c : I.E) = 0 := by simp [h]
    rw [hc, Pi.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero hb0' (mul_ne_zero hm0 hi) this
  obtain ⟨v, hv⟩ := one_le_norm_embedding_alt I c hc0
  have e : ‖I.φ v (c : I.E)‖ = ‖I.φ v (b : I.E)‖ * (m : ℝ) * ‖I.φ v (u i)‖ := by
    rw [hc, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_natCast, norm_mul, norm_mul,
      Complex.norm_natCast, mul_assoc]
  set S := ∑ w, ∑ k, ‖coordV I x w u k‖ ^ 2
  have hSv : ∑ k, ‖coordV I x v u k‖ ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun w => ∑ k, ‖coordV I x w u k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ v)
  have hS0 : 0 ≤ S := by positivity
  have h1 : 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := by
    have : 1 ≤ ‖I.φ v (c : I.E)‖ ^ 2 := by nlinarith
    rw [e] at this
    nlinarith
  have h2 : ‖I.φ v (u i)‖ ^ 2 ≤ C v * S := (hCb v u i).trans
    (mul_le_mul_of_nonneg_left hSv (hCpos v).le)
  have h3 : ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v ≤ K := by
    have := Finset.single_le_sum (f := fun w => ‖I.φ w (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C w)
      (fun w _ => by have := hCpos w; positivity) (Finset.mem_univ v)
    linarith
  have h4 : 1 ≤ K * S := by
    have hbm : 0 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 := by positivity
    calc 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := h1
      _ ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * (C v * S) := mul_le_mul_of_nonneg_left h2 hbm
      _ = (‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v) * S := by ring
      _ ≤ K * S := mul_le_mul_of_nonneg_right h3 hS0
  rw [div_le_iff₀ hK0]
  linarith

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.PacketConditionsClosed
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem mulVec_injective_map {E : Type*} [Field E] {n j : ℕ} (f : E →+* ℂ)
    (Bm : Matrix (Fin n) (Fin j) E) (hB : Function.Injective Bm.mulVec) :
    Function.Injective (Bm.map f).mulVec := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Bm)
    (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hB
      simpa [Matrix.toLin'_apply] using hxy)
  have hC : LinearMap.toMatrix' g * Bm = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h1
  have h2 : (LinearMap.toMatrix' g).map f * Bm.map f = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one f (map_zero f) (map_one f)
  intro x y hxy
  have h3 := congrArg ((LinearMap.toMatrix' g).map f).mulVec hxy
  simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h3
  exact h3

theorem gram_det_re_pos (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (hb : LinearIndependent I.E b) : 0 < (gramV I x v b).det.re := by
  classical
  set A : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹ with hA
  set Bm : Matrix (Fin I.n) (Fin j) I.E := Matrix.of fun i a => b a i with hBm
  have hgram : gramV I x v b = (A * Bm.map (I.φ v))ᴴ * (A * Bm.map (I.φ v)) := by
    ext a c
    have e : ∀ a i, coordV I x v (b a) i = (A * Bm.map (I.φ v)) i a := by
      intro a i
      simp [coordV, A, Bm, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    simp only [gramV, e, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hB : Function.Injective Bm.mulVec := by
    intro c c' h
    have hs : ∑ a, (c a - c' a) • b a = 0 := by
      ext i
      have := congrFun h i
      simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        Pi.zero_apply]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this
    funext a
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ hs a)
  have hAu : IsUnit A := (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  have hC : Function.Injective (A * Bm.map (I.φ v)).mulVec := by
    intro w w' h
    simp only [← Matrix.mulVec_mulVec] at h
    exact mulVec_injective_map (I.φ v) Bm hB (Matrix.mulVec_injective_iff_isUnit.2 hAu h)
  have hpos := (Matrix.PosDef.conjTranspose_mul_self _ hC).det_pos
  rw [hgram]
  exact (Complex.pos_iff.1 hpos).1

theorem packet_conditions_closed (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) : HeightsPositive := by
  unfold HeightsPositive
  intro I x s
  unfold ht
  obtain ⟨M, hMfg, hM⟩ := h1 I x
  cases s
  apply div_pos
  · apply Finset.prod_pos
    intro v _
    apply gram_det_re_pos
    assumption
  · rw [Nat.cast_pos]
    refine @Nat.card_pos _ _ (h2 _ _ _ M _ _ hMfg ?_ ?_ ?_ ?_)
    all_goals first
      | assumption
      | (intro y hy; rw [← SetLike.mem_coe, hM]; aesop)
      | aesop

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.SumNormMulVecSqLe
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem norm_add_sq_le_young (p q : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖p + q‖ ^ 2 ≤ (1 + t) * ‖p‖ ^ 2 + (1 + 1 / t) * ‖q‖ ^ 2 := by
  have ha := norm_nonneg p
  have hb := norm_nonneg q
  have h1 : ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le p q
  have h2 : ‖p + q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖p‖ * ‖q‖ ≤ t * ‖p‖ ^ 2 + 1 / t * ‖q‖ ^ 2 := by
    have h4 : 0 ≤ (t * ‖p‖ - ‖q‖) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * ‖p‖ - ‖q‖) ^ 2 / t = t * ‖p‖ ^ 2 - 2 * ‖p‖ * ‖q‖ + 1 / t * ‖q‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith

theorem norm_sum_mul_sq_le {m : ℕ} (d w : Fin m → ℂ) :
    ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2 := by
  have h1 : ‖∑ l, d l * w l‖ ≤ ∑ l, ‖d l‖ * ‖w l‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖d l‖) (fun l => ‖w l‖)
  calc ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ * ‖w l‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem sum_norm_mulVec_sq_le {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      ((1 + t) + (1 + 1 / t) * ∑ i, ∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ i, ‖w i‖ ^ 2 := by
  have hY : ∀ i, (Y *ᵥ w) i = w i + ((Y - 1) *ᵥ w) i := by
    intro i
    simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hc : 0 ≤ 1 + 1 / t := by
    have := one_div_pos.mpr ht
    linarith
  have hi : ∀ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      (1 + t) * ‖w i‖ ^ 2 + (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2) := by
    intro i
    rw [hY]
    refine (norm_add_sq_le_young _ _ ht).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le _ _) hc)
  calc ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ ∑ i, ((1 + t) * ‖w i‖ ^ 2 +
        (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.T7
section
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace Formalism.L2.SG.Pf.Tau

theorem t7 : InfimumContinuousFamily := by
  intro X _ S g hne hpos hloc
  have hbdd : ∀ x, BddBelow (Set.range (g x)) := fun x => ⟨0, by rintro _ ⟨s, rfl⟩; exact hpos x s⟩
  have hinf_nonneg : ∀ x, 0 ≤ ⨅ s, g x s := fun x => by
    haveI := hne x
    exact le_ciInf fun s => hpos x s
  have key : ∀ x y (r : ℝ), 0 ≤ r → (∀ s, ∃ s', g y s' ≤ r * g x s) → (⨅ s, g y s) ≤ r * ⨅ s, g x s := by
    intro x y r hr h
    haveI := hne x
    rw [Real.mul_iInf_of_nonneg hr]
    exact le_ciInf fun s => by
      obtain ⟨s', hs'⟩ := h s
      exact (ciInf_le (hbdd y) s').trans hs'
  have hmin : ∀ a b r : ℝ, 1 ≤ r → 0 ≤ b → a ≤ r * b → min (1 / 2) a ≤ r * min (1 / 2) b := by
    intro a b r hr hb hab
    rcases le_total b (1 / 2) with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hab
    · rw [min_eq_left h]
      nlinarith [min_le_left (1 / 2 : ℝ) a]
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hr : (1 : ℝ) < 1 + ε := by linarith
  filter_upwards [hloc x (1 + ε) hr] with x' hx'
  have h1 := hmin _ _ _ hr.le (hinf_nonneg x) (key x x' _ (by linarith) hx'.1)
  have h2 := hmin _ _ _ hr.le (hinf_nonneg x') (key x' x _ (by linarith) hx'.2)
  have hm1 : min (1 / 2 : ℝ) (⨅ s, g x s) ≤ 1 / 2 := min_le_left _ _
  have hm2 : min (1 / 2 : ℝ) (⨅ s, g x' s) ≤ 1 / 2 := min_le_left _ _
  have hp1 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x s) := le_min (by norm_num) (hinf_nonneg x)
  have hp2 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x' s) := le_min (by norm_num) (hinf_nonneg x')
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end Formalism.L2.SG.Pf.Tau
end
end

