module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.BlockEmbedConjIsUnitaryEmbedding
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.BlockEmb

open PI.UpqRep PI.HwUniqW

theorem blockW_mul_colW {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) :
    PI.UpqRep.blockW m r s * colW m r = colW m r * s := by
  ext i a
  have h1 : (PI.UpqRep.blockW m r s * colW m r) i a = PI.UpqRep.blockW m r s i (bl m r a) := by
    simp [Matrix.mul_apply, colW]
  rw [h1]
  by_cases hi : InB m r i
  · have hp : i.val - r < m := by unfold InB at hi; omega
    have hb := block_mk hi hp
    rw [← hb, blockW_bl, Matrix.mul_apply]
    simp [colW, blockIndex_injective.eq_iff]
  · rw [blockW_out s hi, if_neg (ne_of_inB (inB_bl a) hi).symm, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    simp [colW, (ne_of_inB (inB_bl b) hi).symm]

theorem blockW_mulVec_of_vanish {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) {y : Fin (2 * r + m + 1) → ℂ}
    (hy : ∀ a, y (bl m r a) = 0) : PI.UpqRep.blockW m r s *ᵥ y = y := by
  have hz : ∀ j, InB m r j → y j = 0 := fun j hj => by
    have hp : j.val - r < m := by unfold InB at hj; omega
    rw [← block_mk hj hp]; exact hy _
  funext i
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : InB m r i
  · rw [hz i hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : InB m r j
    · rw [hz j hj, mul_zero]
    · rw [blockW_in_out s hi hj, zero_mul]
  · simp [blockW_out s hi]

theorem isEmb_conj_blockW {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ}
    {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r)
    (hF : Q * colW m r = F * A) (hA : A * Ai = 1) :
    IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  have hFe : F = Q * colW m r * Ai := by rw [hF, Matrix.mul_assoc, hA, Matrix.mul_one]
  refine ⟨?_, fun x hx => ?_⟩
  · calc Q * PI.UpqRep.blockW m r s * Qi * F
        = Q * PI.UpqRep.blockW m r s * (Qi * Q) * colW m r * Ai := by
          rw [hFe]; simp only [Matrix.mul_assoc]
      _ = Q * (PI.UpqRep.blockW m r s * colW m r) * Ai := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Q * colW m r) * s * Ai := by
          rw [blockW_mul_colW]; simp only [Matrix.mul_assoc]
      _ = F * (A * s * Ai) := by
          rw [hF]; simp only [Matrix.mul_assoc]
  · have hy : ∀ a, (Qi *ᵥ x) (bl m r a) = 0 := fun a => by
      have e : (colW m r)ᴴ * PI.UpqRep.Hpk m r * Qi = Aᴴ * (Fᴴ * J) := by
        have hH : PI.UpqRep.Hpk m r = Qᴴ * J * Q := hg.symm
        rw [hH]
        calc (colW m r)ᴴ * (Qᴴ * J * Q) * Qi = (Q * colW m r)ᴴ * J * (Q * Qi) := by
              rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = Aᴴ * (Fᴴ * J) := by
              rw [h1, hF, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [← colW_mulVec (Qi *ᵥ x) a, mulVec_mulVec, e, ← mulVec_mulVec, hx, mulVec_zero]; rfl
    rw [← mulVec_mulVec, ← mulVec_mulVec, blockW_mulVec_of_vanish s hy, mulVec_mulVec, h1, one_mulVec]

end UpperTheory.Lit.Bur.BlockEmb

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding : ∀ {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r) (hF : Q * colW m r = F * A) (hA : A * Ai = 1), IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  first | exact @UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | exact UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | (intros; apply UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.CasselmanWallachContFiniteSumSobolevForms
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.CWCombo

theorem isCWCont_of_sobCont {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v)
    {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp)
    (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp}
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  classical
  have hnn : ∀ (L : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))) (v : H),
      0 ≤ (L.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := fun L v =>
    List.sum_nonneg (by
      intro x hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _)
  have key : ∀ s : Finset ι, ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, ∀ X ∈ w, PI.UpqRep.InLieHpk k r X) ∧
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ‖∑ i ∈ s, l i v • b i‖ ≤
        C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, [], by simp, by simp⟩
    | insert i s hi ih =>
      obtain ⟨C, Ws, hW, hb⟩ := ih
      obtain ⟨S, D, hS, hD⟩ := hl i
      refine ⟨|D| * ‖b i‖ + |C|, S ++ Ws, ?_, ?_⟩
      · intro w hw X hX
        rcases List.mem_append.1 hw with h | h
        · exact hS w h X hX
        · exact hW w h X hX
      · intro v hv
        have e : ‖l i v‖ ≤ D * (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
          have := hD v (hs v hv)
          simpa only [dsigW_eq] using this
        have h1 := hnn S v
        have h2 := hnn Ws v
        have h3 := hb v hv
        rw [Finset.sum_insert hi, List.map_append, List.sum_append]
        set P := (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        set Q := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        have hbn : 0 ≤ ‖b i‖ := norm_nonneg _
        have e1 : ‖l i v • b i‖ ≤ |D| * ‖b i‖ * P := by
          rw [norm_smul]
          calc ‖l i v‖ * ‖b i‖ ≤ (|D| * P) * ‖b i‖ :=
                mul_le_mul_of_nonneg_right (e.trans (mul_le_mul_of_nonneg_right (le_abs_self D) h1)) hbn
            _ = |D| * ‖b i‖ * P := by ring
        have e2 : ‖∑ j ∈ s, l j v • b j‖ ≤ |C| * Q :=
          h3.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h2)
        have a1 : 0 ≤ |D| * ‖b i‖ * Q := mul_nonneg (mul_nonneg (abs_nonneg _) hbn) h2
        have a2 : 0 ≤ |C| * P := mul_nonneg (abs_nonneg _) h1
        calc ‖l i v • b i + ∑ j ∈ s, l j v • b j‖ ≤ ‖l i v • b i‖ + ‖∑ j ∈ s, l j v • b j‖ := norm_add_le _ _
          _ ≤ |D| * ‖b i‖ * P + |C| * Q := add_le_add e1 e2
          _ ≤ (|D| * ‖b i‖ + |C|) * (P + Q) := by nlinarith
  obtain ⟨C, Ws, hW, hb⟩ := key Finset.univ
  exact ⟨C, Ws, hW, fun v hv => by rw [hB v hv]; exact hb v hv⟩

end UpperTheory.Lit.Bur.CWCombo

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms : ∀ {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v) {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp) (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp} (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i), PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  first | exact @UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | exact UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | (intros; apply UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.ContIrredCompactUnitaryGroupRepIsUnitarizable
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace UpperTheory.Lit.Bur.Unitarize

theorem continuousOn_of_dual {X F : Type} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {s : Set X} {f : X → F}
    (h : ∀ l : Module.Dual ℂ F, ContinuousOn (fun x => l (f x)) s) : ContinuousOn f s := by
  let b := Module.finBasis ℂ F
  have e : f = fun x => ∑ i, b.coord i (f x) • b i := by
    funext x
    exact (b.sum_repr (f x)).symm
  rw [e]
  exact continuousOn_finsetSum _ fun i _ => (h (b.coord i)).smul continuousOn_const

theorem exists_invariant_core_of_equiv {G W E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (e : W ≃ₗ[ℂ] E) (r : G → Module.End ℂ W) (h1 : r 1 = 1) (hm : ∀ a b, r (a * b) = r a * r b)
    (hc : ∀ (w : W) (l : Module.Dual ℂ W), Continuous fun g => l (r g w)) :
    ∃ c : InnerProductSpace.Core ℂ W, ∀ g x y, c.inner (r g x) (r g y) = c.inner x y := by
  let A : G → W → E := fun g x => e (r g⁻¹ x)
  have hA : ∀ x, Continuous fun g => A g x := fun x => by
    rw [← continuousOn_univ]
    refine continuousOn_of_dual fun l => ?_
    have h := hc x (l ∘ₗ (e : W →ₗ[ℂ] E))
    exact (h.comp continuous_inv).continuousOn
  let F : W → W → G → ℂ := fun x y g => ⟪A g x, A g y⟫_ℂ
  have hF : ∀ x y, Continuous (F x y) := fun x y => (hA x).inner (hA y)
  have hI : ∀ x y, Integrable (F x y) μ := fun x y =>
    (hF x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hxx : ∀ x, ∫ g, F x x g ∂μ = ((∫ g, ‖A g x‖ ^ 2 ∂μ : ℝ) : ℂ) := fun x => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [F]
    rw [inner_self_eq_norm_sq_to_K]
    simp
  let core : PreInnerProductSpace.Core ℂ W :=
    { inner := fun x y => ∫ g, F x y g ∂μ
      conj_inner_symm := fun x y => by
        show conj (∫ g, F y x g ∂μ) = ∫ g, F x y g ∂μ
        rw [← integral_conj]
        simp only [F, inner_conj_symm]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (∫ g, F x x g ∂μ)
        rw [hxx]
        simpa using integral_nonneg fun g => by positivity
      add_left := fun x y z => by
        show ∫ g, F (x + y) z g ∂μ = ∫ g, F x z g ∂μ + ∫ g, F y z g ∂μ
        rw [← integral_add (hI x z) (hI y z)]
        simp only [F, A, map_add (f := _), inner_add_left]
      smul_left := fun x y a => by
        show ∫ g, F (a • x) y g ∂μ = conj a * ∫ g, F x y g ∂μ
        rw [← integral_const_mul]
        simp only [F, A, map_smul, inner_smul_left] }
  refine ⟨{ core with definite := fun x hx => ?_ }, fun h x y => ?_⟩
  · by_contra hx0
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ)
      (f := fun g => ‖A g x‖ ^ 2) (x := 1) ((hA x).norm.pow 2) (HasCompactSupport.of_compactSpace _)
      (fun g => by positivity) (by simpa [A, h1] using hx0)
    have h0 : ∫ g, F x x g ∂μ = 0 := hx
    rw [hxx] at h0
    exact hpos.ne' (by exact_mod_cast h0)
  · show ∫ g, F (r h x) (r h y) g ∂μ = ∫ g, F x y g ∂μ
    rw [← integral_mul_left_eq_self (F x y) h⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [F, A, _root_.mul_inv_rev, hm]

theorem exists_invariant_core {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (r : G → Module.End ℂ W) (h1 : r 1 = 1) (hm : ∀ a b, r (a * b) = r a * r b)
    (hc : ∀ (w : W) (l : Module.Dual ℂ W), Continuous fun g => l (r g w)) :
    ∃ c : InnerProductSpace.Core ℂ W, ∀ g x y, c.inner (r g x) (r g y) = c.inner x y :=
  exists_invariant_core_of_equiv μ
    (LinearEquiv.ofFinrankEq W (EuclideanSpace ℂ (Fin (Module.finrank ℂ W))) (by simp)) r h1 hm hc

theorem compactSpace_UJ_allPos (k : ℕ) : CompactSpace (PI.UpqRep.UJ (PI.UpqRep.allPos k)) := by
  have hemb := PI.UpqRep.isClosedEmbeddingMatrix k (PI.UpqRep.allPos k)
  rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin k => Set.pi Set.univ fun _ : Fin k => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (X := Matrix (Fin k) (Fin k) ℂ) hc (hemb.2 ▸ hemb.1.isClosed_range) ?_
  intro g hg i _ j _
  have hu : g ∈ Matrix.unitaryGroup (Fin k) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (PI.HwUniqW.mem_UJset_allPos.1 hg)
  simpa using entry_norm_bound_of_unitary hu i j

theorem unitarize : ∀ {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {π : Matrix (Fin k) (Fin k) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH 1) π), ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp) (ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)) (T : W ≃ₗ[ℂ] Wp), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ ∧ (∀ h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∀ w, T (π h w) = ρ h (T w)) ∧ ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro k W _ _ _ π hπ
  obtain ⟨⟨h1, hm⟩, hc, hi⟩ := hπ
  have hset : PI.UpqRep.UJset (PI.UpqRep.allPos k) = Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) :=
    Set.ext fun h => PI.HwUniqW.mem_UJset_allPos.trans GlobalTheory.BesselMapOne.mem_UH_one.symm
  rw [hset]
  have hmem : ∀ g : PI.UpqRep.UJ (PI.UpqRep.allPos k), PI.UpqRep.umat g ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) :=
    fun g => hset ▸ g.2
  have hlift : ∀ g ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∃ u : PI.UpqRep.UJ (PI.UpqRep.allPos k),
      PI.UpqRep.umat u = g := fun g hg => by
    have hg' : g ∈ Set.range (PI.UpqRep.coeMatrixAlt (PI.UpqRep.allPos k)) := by
      rw [PI.UpqRep.range_coeMatrix]
      exact hset.ge hg
    exact hg'
  haveI := compactSpace_UJ_allPos k
  obtain ⟨c, hinv⟩ := exists_invariant_core (PI.UpqRep.muG (PI.UpqRep.allPos k))
    (fun g => π (PI.UpqRep.umat g)) h1 (fun a b => hm _ (hmem a) _ (hmem b))
    (fun w l => (hc w l).comp_continuous (PI.UpqRep.continuous_coeMatrix _) hmem)
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℂ W _ _ _ c
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore c.toCore
  refine ⟨W, inferInstance, inferInstance, ‹_›, fun g => LinearMap.toContinuousLinearMap (π g), LinearEquiv.refl ℂ W, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · ext v
    simp [h1]
  · intro a ha b hb
    ext v
    simp [hm a ha b hb]
  · intro g hg v
    obtain ⟨u, rfl⟩ := hlift g hg
    have := hinv u v v
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => Real.sqrt (RCLike.re z)) this
  · intro v
    exact continuousOn_of_dual fun l => hc v l
  · intro h _ w
    rfl
  · intro S hS
    exact hi S hS

end UpperTheory.Lit.Bur.Unitarize

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.contIrred_compactUnitaryGroup_rep_isUnitarizable : ∀ {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {π : Matrix (Fin k) (Fin k) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH 1) π), ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp) (ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)) (T : W ≃ₗ[ℂ] Wp), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ ∧ (∀ h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∀ w, T (π h w) = ρ h (T w)) ∧ ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  first | exact @UpperTheory.Lit.Bur.Unitarize.unitarize | exact UpperTheory.Lit.Bur.Unitarize.unitarize | (intros; apply UpperTheory.Lit.Bur.Unitarize.unitarize <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.ContragredientConjDefiniteUnitaryIsContIrred
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselContra

theorem isContIrred_contra_conj : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  intro m W _ _ _ J₀ A Ai h1 h2 hA π₀ hπ
  have hJ : Aiᴴ * Ai = J₀ := by
    calc Aiᴴ * Ai = Aiᴴ * (Aᴴ * J₀ * A) * Ai := by rw [hA, Matrix.mul_one]
      _ = (A * Ai)ᴴ * J₀ * (A * Ai) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by simp [h1]
  have hmem : ∀ h, h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) →
      A * hᴴ * Ai ∈ Formalism.QuantumDeterminants.UH J₀ := by
    intro h hh
    have hh' : h * hᴴ = 1 := mul_eq_one_comm.1 (mem_UH_one.1 hh)
    show (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = J₀
    calc (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = Aiᴴ * h * (Aᴴ * J₀ * A) * hᴴ * Ai := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Aiᴴ * (h * hᴴ) * Ai := by
          rw [hA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = J₀ := by rw [hh', Matrix.mul_one, hJ]
  have hadj : ∀ g, g ∈ Formalism.QuantumDeterminants.UH J₀ →
      (Ai * g * A)ᴴ ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro g hg
    have hg' : gᴴ * J₀ * g = J₀ := hg
    refine mem_UH_one.2 (mul_eq_one_comm.1 ?_)
    rw [conjTranspose_conjTranspose]
    calc (Ai * g * A)ᴴ * (Ai * g * A) = Aᴴ * (gᴴ * (Aiᴴ * Ai) * g) * A := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hg', hA]
  have hback : ∀ g : Matrix (Fin m) (Fin m) ℂ, A * ((Ai * g * A)ᴴ)ᴴ * Ai = g := by
    intro g
    rw [conjTranspose_conjTranspose]
    calc A * (Ai * g * A) * Ai = (A * Ai) * g * (A * Ai) := by
          simp only [Matrix.mul_assoc]
      _ = g := by simp [h1]
  obtain ⟨⟨hone, hmul⟩, hc, hi⟩ := hπ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun w l => ?_, fun U hU => ?_⟩
  · have : A * (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * Ai = 1 := by simp [h1]
    beta_reduce
    rw [this, hone]
    ext l x
    simp
  · have e : A * (a * b)ᴴ * Ai = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by
      calc A * (a * b)ᴴ * Ai = A * bᴴ * (Ai * A) * aᴴ * Ai := by
            rw [h2, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by simp only [Matrix.mul_assoc]
    beta_reduce
    rw [e, hmul _ (hmem b hb) _ (hmem a ha)]
    ext l x
    simp
  · obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective l
    have hφ : Continuous fun h : Matrix (Fin m) (Fin m) ℂ => A * hᴴ * Ai :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    exact (hc x w).comp hφ.continuousOn hmem
  · have hs : ∀ g ∈ Formalism.QuantumDeterminants.UH J₀, ∀ v ∈ U.dualCoannihilator,
        π₀ g v ∈ U.dualCoannihilator := fun g hg v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have := hv _ (hU _ (hadj g hg) l hl)
      beta_reduce at this
      rw [hback] at this
      simpa using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]
    rcases hi _ hs with h | h
    · rw [h]; exact Or.inr Submodule.dualAnnihilator_bot
    · rw [h]; exact Or.inl Submodule.dualAnnihilator_top

end UpperTheory.Lit.Bur.BesselContra

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  first | exact @UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | exact UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | (intros; apply UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HermitianFormPosCongruentIdentity
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.HermCongr


open scoped ComplexOrder in
theorem posDef_of_herm_re_pos {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) : J₀.PosDef := by
  have hA : J₀.IsHermitian := hH
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA ?_
  intro x hx
  have hre : 0 < (star x ⬝ᵥ J₀ *ᵥ x).re := hp x hx
  have him : (star x ⬝ᵥ J₀ *ᵥ x).im = 0 := hA.im_star_dotProduct_mulVec_self x
  exact Complex.pos_iff.2 ⟨hre, him.symm⟩

theorem exists_congr_one {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) :
    ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  have hP := posDef_of_herm_re_pos hH hp
  have hA : J₀.IsHermitian := hH
  have hd : ∀ i, 0 < hA.eigenvalues i := hP.eigenvalues_pos
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hJ : J₀ = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  let s : Fin m → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)
  let t : Fin m → ℂ := fun i => (((Real.sqrt (hA.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one]
  have htdt : diagonal t * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h0 : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    have h1 : Real.sqrt (hA.eigenvalues i) * Real.sqrt (hA.eigenvalues i) = hA.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have h2 : (Real.sqrt (hA.eigenvalues i))⁻¹ * hA.eigenvalues i * (Real.sqrt (hA.eigenvalues i))⁻¹ = 1 := by
      have h3 : ∀ r : ℝ, r ≠ 0 → r⁻¹ * (r * r) * r⁻¹ = 1 := by
        intro r hr
        field_simp
      have h4 := h3 _ h0
      rwa [h1] at h4
    simp only [t]
    exact_mod_cast h2
  have htH : (diagonal t)ᴴ = diagonal t := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [t]
  refine ⟨U * diagonal t, diagonal s * star U, ?_, ?_, ?_⟩
  · calc U * diagonal t * (diagonal s * star U) = U * (diagonal t * diagonal s) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hts, Matrix.mul_one, hUU']
  · calc diagonal s * star U * (U * diagonal t) = diagonal s * (star U * U) * diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hst]
  · rw [conjTranspose_mul, htH, ← star_eq_conjTranspose]
    calc diagonal t * star U * J₀ * (U * diagonal t)
        = diagonal t * star U * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U)
            * (U * diagonal t) := by rw [← hJ]
      _ = diagonal t * (star U * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
            * (star U * U) * diagonal t := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, Matrix.mul_one, htdt]

end UpperTheory.Lit.Bur.HermCongr

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity : ∀ {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀) (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re), ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  first | exact @UpperTheory.Lit.Bur.HermCongr.exists_congr_one | exact UpperTheory.Lit.Bur.HermCongr.exists_congr_one | (intros; apply UpperTheory.Lit.Bur.HermCongr.exists_congr_one <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SylvesterInertiaSignFormCongrSplitHermitian
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.Inertia

theorem card_plus_of_congr_Hpk : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool)
    {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r),
    (Finset.univ.filter fun i => ε i = true).card = m + r := by
  intro m r ε Q Qi h1 h2 hg
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  have hc : Formalism.MainNotions.S.IsCayley m r ε Q := ⟨hu, hg⟩
  exact (ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA.cayley_signature' hc).1

end UpperTheory.Lit.Bur.Inertia

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool) {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r), (Finset.univ.filter fun i => ε i = true).card = m + r := by
  first | exact @UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | exact UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | (intros; apply UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk <;> assumption)
end

