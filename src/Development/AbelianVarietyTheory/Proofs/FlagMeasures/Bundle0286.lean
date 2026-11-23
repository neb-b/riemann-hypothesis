module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwDelta

variable {n : ℕ}

theorem exists_cont_detOn (V : Submodule ℂ (Fin n → ℂ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ → ℝ, Continuous D ∧
      ∀ X, (∀ y ∈ V, X *ᵥ y ∈ V) → detOn X V = D X := by
  obtain ⟨U, hVU⟩ := Submodule.exists_isCompl V
  let p := Submodule.projectionOnto V U hVU
  let b := Module.finBasis ℂ V
  refine ⟨fun X => ‖(Matrix.of fun i k => b.repr (p (X *ᵥ (b k : Fin n → ℂ))) i).det‖, ?_, ?_⟩
  · apply Continuous.norm
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i k
    have hlin : Continuous fun y : Fin n → ℂ => b.repr (p y) i :=
      ((b.coord i).comp p).continuous_of_finiteDimensional
    exact hlin.comp (continuous_id.matrix_mulVec continuous_const)
  · intro X hX
    have h' : ∀ y ∈ V, Matrix.toLin' X y ∈ V := fun y hy => by
      simpa [Matrix.toLin'_apply] using hX y hy
    have e : ∀ k, p (X *ᵥ (b k : Fin n → ℂ)) = (Matrix.toLin' X).restrict h' (b k) := by
      intro k
      have hp : p (X *ᵥ (b k : Fin n → ℂ)) = ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩ :=
        Submodule.projectionOnto_apply_left hVU ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩
      rw [hp]
      apply Subtype.ext
      simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
    rw [detOn, dite_eq_left h', ← LinearMap.det_toMatrix b]
    congr 2
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.of_apply, e k]

theorem detOn_one (V : Submodule ℂ (Fin n → ℂ)) : detOn (1 : Matrix (Fin n) (Fin n) ℂ) V = 1 := by
  have h' : ∀ y ∈ V, Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) y ∈ V := fun y hy => by simpa using hy
  rw [detOn, dite_eq_left h']
  have hid : (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ)).restrict h' = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by simp [LinearMap.restrict_apply])
  rw [hid, LinearMap.det_id, norm_one]

private theorem detOn_le_one_of_unitary_of_invariant (U : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ))
    (hU : Uᴴ * U = 1) (hV : ∀ y ∈ V, U *ᵥ y ∈ V) : detOn U V ≤ 1 := by
  obtain ⟨D, hDc, hD⟩ := exists_cont_detOn V
  have hKc : IsCompact {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} := by
    have hcl : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
        Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin n) (Fin n) ℂ)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset hcl ?_
    intro X hX
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i k
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hX) i k
  have hUg : U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hU
  have hpow : ∀ k : ℕ, (∀ y ∈ V, U ^ k *ᵥ y ∈ V) ∧ detOn (U ^ k) V = detOn U V ^ k := by
    intro k
    induction k with
    | zero => exact ⟨fun y hy => by simpa using hy, by simpa using detOn_one V⟩
    | succ k ih =>
      have hs : ∀ y ∈ V, U ^ (k + 1) *ᵥ y ∈ V := fun y hy => by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih.1 _ (hV y hy)
      refine ⟨hs, ?_⟩
      rw [pow_succ, GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ V ih.1 hV, ih.2, pow_succ]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hDc.continuousOn
  by_contra hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have hmem : (U ^ k)ᴴ * U ^ k = 1 := Matrix.mem_unitaryGroup_iff'.1 (pow_mem hUg k)
  have hb := hC (U ^ k) hmem
  rw [← hD _ (hpow k).1, (hpow k).2, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (GlobalTheory.FlagMeas.SizeMove.detOn_nonneg U V) k)] at hb
  linarith

theorem detOn_le_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) ≤ 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  exact detOn_le_one_of_unitary_of_invariant _ _ hl.1 (fun y hy => (hl2 i y hy).1)

theorem detOn_eq_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) = 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  have hU : (uMat l)ᴴ * uMat l = 1 := hl.1
  have hU' : (uMat l)ᴴᴴ * (uMat l)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have h1 := detOn_le_one hl i
  have h2 := detOn_le_one_of_unitary_of_invariant _ (W i) hU' (fun y hy => (hl2 i y hy).2)
  have hprod : detOn ((uMat l)ᴴ) (W i) * detOn (uMat l) (W i) = 1 := by
    rw [← GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ _ (fun y hy => (hl2 i y hy).2) (fun y hy => (hl2 i y hy).1), hU,
      detOn_one]
  have h3 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg (uMat l) (W i)
  have h4 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg ((uMat l)ᴴ) (W i)
  exact le_antisymm h1 (by nlinarith)

theorem measurable_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n 1 j τ id := by
  unfold layerProd
  fun_prop

theorem continuousAt_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Filter.Tendsto (fun τ : Fin a → ℝ => layerProd n 1 j τ id) (nhds 1) (nhds 1) := by
  have hc : ContinuousAt (fun τ : Fin a → ℝ => layerProd n 1 j τ id) 1 := by
    unfold layerProd
    fun_prop (disch := simp)
  have h1 : layerProd n 1 j (1 : Fin a → ℝ) id = 1 := by simp [layerProd]
  simpa [h1] using hc.tendsto

open scoped Matrix.Norms.Frobenius in
theorem exists_ball {s : Set (Matrix (Fin n) (Fin n) ℂ)} (hs : s ∈ nhds 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ X, nrm (X - 1) < t → X ∈ s := by
  obtain ⟨t, ht, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨t, ht, fun X hX => hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← nrm_eq]
  exact hX

theorem dlt_props : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  intro n ε a j W
  refine ⟨?_, ?_, ?_⟩
  · unfold dlt
    exact ENNReal.measurable_ofReal.comp ((measurable_layerProd j).comp
      (Measurable.of_eval fun i => measurable_locSize_uMat n ε a j W i))
  · intro l hl m hm
    have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hmul : uMat (m * l) = uMat m * uMat l := rfl
    have hloc : locSize j W (uMat (m * l)) = locSize j W (uMat m) := by
      funext i
      simp only [locSize]
      rw [hmul,
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.succ) (fun y hy => (hm2 i.succ y hy).1)
          (fun y hy => (hl2 i.succ y hy).1),
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.castSucc) (fun y hy => (hm2 i.castSucc y hy).1)
          (fun y hy => (hl2 i.castSucc y hy).1),
        detOn_eq_one hl i.succ, detOn_eq_one hl i.castSucc, mul_one, mul_one]
    unfold dlt
    rw [hloc]
  · intro η hη
    choose D hDc hD using fun i : Fin (a + 1) => exists_cont_detOn (W i)
    have hD1 : ∀ i, D i 1 = 1 := fun i => by
      rw [← hD i 1 (fun y hy => by simpa using hy), detOn_one]
    set G : Matrix (Fin n) (Fin n) ℂ → Fin a → ℝ :=
      fun X i => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i) with hGdef
    have hG : Filter.Tendsto G (nhds 1) (nhds 1) := by
      rw [tendsto_pi_nhds]
      intro i
      have hc : ContinuousAt (fun X => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i)) 1 :=
        ((hDc _).continuousAt.div (hDc _).continuousAt (by simp [hD1])).rpow_const
          (Or.inl (by simp [hD1]))
      have ht := hc.tendsto
      simp only [hD1, div_one, Real.one_rpow] at ht
      exact ht
    have hF := (continuousAt_layerProd (n := n) j).comp hG
    have hpos : 0 < 1 + η := by linarith
    have hU : Set.Ioo (1 / (1 + η)) (1 + η) ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds ((div_lt_one hpos).2 (by linarith)) (by linarith)
    obtain ⟨t, ht, hball⟩ := exists_ball (Filter.tendsto_def.1 hF _ hU)
    refine ⟨t, ht, fun m hm hmt => ?_⟩
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hin := hball _ hmt
    have hGm : G (uMat m) = locSize j W (uMat m) := by
      funext i
      simp only [hGdef, locSize]
      rw [hD i.succ _ (fun y hy => (hm2 i.succ y hy).1), hD i.castSucc _ (fun y hy => (hm2 i.castSucc y hy).1)]
    simp only [Set.mem_preimage, Function.comp_apply, hGm, Set.mem_Ioo] at hin
    obtain ⟨hlo, hhi⟩ := hin
    unfold dlt
    refine ⟨ENNReal.ofReal_le_ofReal hhi.le, ?_⟩
    rw [← ENNReal.ofReal_mul hpos.le, ENNReal.one_le_ofReal]
    rw [div_lt_iff₀ hpos] at hlo
    linarith [mul_comm (layerProd n 1 j (locSize j W (uMat m)) id) (1 + η)]

end GlobalTheory.IwDelta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeSumTypes
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.TypeDecomp

theorem lintegral_biUnion_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (A : ι → Set α) (f : α → ENNReal) :
    ∫⁻ x in ⋃ i ∈ s, A i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in A i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem hasType_cast (I : AutInst) (x : I.GA) {a a' : ℕ} (h : a' = a) (j : Fin a → ℕ) (τ : Fin a → ℝ)
    (H : HasType I x j τ) : ∃ τ', HasType I x (fun i : Fin a' => j (Fin.cast h i)) τ' := by
  subst h
  exact ⟨τ, H⟩

theorem sum_diff (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ)
    (h : ∀ i, r i.succ = r i.castSucc + j i) : r (Fin.last a) = r 0 + ∑ i, j i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have key := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => by
      have := h i.castSucc
      rwa [Fin.succ_castSucc] at this)
    have hl := h (Fin.last a)
    rw [Fin.succ_last] at hl
    simp only [Fin.castSucc_zero] at key
    rw [Fin.sum_univ_castSucc, hl, key]
    ring

theorem exists_type (B : RowsAut) (p q : ℕ) (hs : SigIs B p q) (hn : 1 ≤ B.I.n) (x : B.I.GA)
    (hx : least B.I x < 1 / 2) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, ∃ τ, HasType B.I x c.blocksFun τ := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hprop⟩ := GlobalTheory.PointFlag.flag_spec B.I x
  obtain ⟨hsteps, hlast⟩ := hprop a S τ hF
  have hlt : ∀ i : Fin a, Formalism.HN.rkK (S i.castSucc) < Formalism.HN.rkK (S i.succ) := fun i => (hsteps i).2.1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hj
  have hstep : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hjpos : ∀ i, 0 < j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hT : HasType B.I x j τ := ⟨S, hF, hstep⟩
  have hsum : Formalism.HN.rkK (S (Fin.last a)) = Formalism.HN.rkK (S 0) + ∑ i, j i :=
    GlobalTheory.TypeDecomp.sum_diff a (fun i => Formalism.HN.rkK (S i)) j hstep
  have ha : a ≠ 0 := by
    intro h0
    have := (hlast hn).1.mp h0
    linarith
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  have hiso : Formalism.HN.rkK (stepLt B.I x (1 / 2)) ≤ rkR (B.I.ε v) := (GlobalTheory.FlagIso.flag_isotropic B.I x).2.1 v
  have hq : rkR (B.I.ε v) ≤ q := (min_le_right _ _).trans (hs v).2.le
  have hSl : S (Fin.last a) = stepLt B.I x (1 / 2) := hF.2.2.1
  have h1 : 1 ≤ ∑ i, j i := by
    have := Finset.single_le_sum (f := j) (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero ha⟩)
    have := hjpos ⟨0, Nat.pos_of_ne_zero ha⟩
    omega
  have h2 : ∑ i, j i ≤ q := by
    rw [hSl] at hsum
    omega
  let c : Composition (∑ i, j i) :=
    ⟨List.ofFn j, fun {b} hb => by
      simp only [List.mem_ofFn, Set.mem_range] at hb
      obtain ⟨k, rfl⟩ := hb
      exact hjpos k, by simp [List.sum_ofFn]⟩
  have hlen : c.length = a := by simp [c, Composition.length]
  have hc : c.blocksFun = fun i => j (Fin.cast hlen i) := by
    funext i
    show (List.ofFn j).get i = j (Fin.cast hlen i)
    first
      | rw [List.get_ofFn]
      | simp [List.get_eq_getElem, Fin.cast]
  obtain ⟨τ', h'⟩ := GlobalTheory.TypeDecomp.hasType_cast B.I x hlen j τ hT
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨h1, h2⟩, c, τ', ?_⟩
  rw [hc]
  exact h'

theorem lintegral_le_sum_types : ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 1 ≤ B.I.n → ∀ Φ : B.I.GA → ENNReal, (∀ x, 1 / 2 ≤ least B.I x → Φ x = 0) → ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf) ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) := by
  intro B p q hs hn Φ hΦ
  have hT : ∀ (J : ℕ) (c : Composition J),
      MeasurableSet {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} := fun J c => by
    obtain ⟨s, -, h, -⟩ := GlobalTheory.FlagMeas.type_measurable B.I c.length c.blocksFun
    exact h
  set P : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} with hP
  set U : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund with hU
  have hPm : MeasurableSet P :=
    Finset.measurableSet_biUnion _ fun J _ => Finset.measurableSet_biUnion _ fun c _ => hT J c
  have hcover : B.fund ⊆ U ∪ Pᶜ := by
    intro x hx
    by_cases hxP : x ∈ P
    · left
      simp only [hP, hU, Set.mem_iUnion, Set.mem_inter_iff] at hxP ⊢
      obtain ⟨J, hJ, c, hc, hxc⟩ := hxP
      exact ⟨J, hJ, c, hc, hxc, hx⟩
    · exact Or.inr hxP
  have hzero : ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) = 0 := by
    have hae : ∀ᵐ x ∂((B.I.muA B.μf).restrict Pᶜ), Φ x = 0 := by
      rw [ae_restrict_iff' hPm.compl]
      refine ae_of_all _ fun x hx => hΦ x ?_
      by_contra hlt
      push_neg at hlt
      obtain ⟨J, hJ, c, τ, hτ⟩ := GlobalTheory.TypeDecomp.exists_type B p q hs hn x hlt
      apply hx
      simp only [hP, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨J, hJ, c, Finset.mem_univ c, τ, hτ⟩
    rw [lintegral_congr_ae hae, lintegral_zero]
  calc ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf)
      ≤ ∫⁻ x in U ∪ Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) + ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_union_le _ _ _
    _ = ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) := by rw [hzero, add_zero]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∫⁻ x in ⋃ c ∈ (Finset.univ : Finset (Composition J)),
          {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _
    _ ≤ _ := Finset.sum_le_sum fun J _ => GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _

end GlobalTheory.TypeDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTypeLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPush

open GlobalTheory.FlagMeas

theorem simplex_meas (a : ℕ) : MeasurableSet (simplexH a) := by
  have h : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, {τ : Fin a → ℝ | i < k → τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ | τ i < 1 / 2}) := by
    ext τ
    simp only [simplexH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 hik, fun i => h2 i⟩,
      fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 i k hik, fun i => h2 i⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_)
    (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  by_cases hik : i < k
  · simpa [hik] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · simp [hik]

theorem dens_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) : Measurable (FlagMeas.dens n f j) := by
  show Measurable fun τ => FlagMeas.dens n f j τ
  simp only [FlagMeas.dens, layerProd, id]
  fun_prop

theorem mem_simplex {I : AutInst} {x : I.GA} {a : ℕ} {j : Fin a → ℕ} {τ : Fin a → ℝ}
    (h : HasType I x j τ) : τ ∈ simplexH a := by
  obtain ⟨S, ⟨-, -, -, hmono, hτ, -⟩, -⟩ := h
  exact ⟨hmono, fun i => ⟨(hτ i).1, (hτ i).2.1⟩⟩

theorem lintegral_type_le : GlobalTheory.FlagMeas.FlagMeasureBound → ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 2 * q + 2 ≤ B.I.n → ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∀ (G : (Fin a → ℝ) → ENNReal) (Φ : B.I.GA → ENNReal), Measurable G → (∀ x τ, HasType B.I x j τ → Φ x ≤ G τ) → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
  intro hFMB B p q hSig hn a j ha hj hsum G Φ hG hΦ
  have := B.haar
  have := B.sf
  obtain ⟨s, hs, hT, hsτ⟩ := GlobalTheory.FlagMeas.type_measurable B.I a j
  set T : Set B.I.GA := {x | ∃ τ, HasType B.I x j τ} with hTdef
  set μ := B.I.muA B.μf with hμ
  set K : ENNReal := μ B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) with hK
  set ρ : Measure (Fin a → ℝ) := (volume.restrict (GlobalTheory.FlagMeas.simplexH a)).withDensity
    (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) with hρ
  have hd : Measurable (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) :=
    (dens_meas B.I.n B.I.f j).ennreal_ofReal

  have h1 : ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := by
    rw [← Measure.restrict_restrict hT]
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hT).2 (Filter.Eventually.of_forall ?_)
    rintro x ⟨τ, hx⟩
    rw [hsτ x τ hx]
    exact hΦ x τ hx

  have h2 : Measure.map s (μ.restrict (T ∩ B.fund)) ≤ K • ρ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply hs hA, Measure.restrict_apply (hs hA), Measure.smul_apply, smul_eq_mul,
      hρ, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hsub : s ⁻¹' A ∩ (T ∩ B.fund) ⊆
        GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund := by
      rintro x ⟨hxA, ⟨τ, hx⟩, hxf⟩
      refine ⟨⟨τ, ⟨?_, mem_simplex hx⟩, hx⟩, hxf⟩
      have hxs : s x = τ := hsτ x τ hx
      rw [← hxs]
      exact hxA
    obtain ⟨-, h0, htop, hle⟩ := hFMB B.I B.μf B.fund B.fund_spec p q hSig hn a j ha hj hsum
      (A ∩ GlobalTheory.FlagMeas.simplexH a) (hA.inter (simplex_meas a)) Set.inter_subset_right
    calc μ (s ⁻¹' A ∩ (T ∩ B.fund))
        ≤ μ (GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund) := measure_mono hsub
      _ ≤ ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            (∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) *
            μ B.fund := (ENNReal.div_le_iff h0.ne' htop.ne).1 hle
      _ = K * ∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
          rw [hK]; ring
  calc ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := h1
    _ = ∫⁻ τ, G τ ∂(Measure.map s (μ.restrict (T ∩ B.fund))) := (lintegral_map hG hs).symm
    _ ≤ ∫⁻ τ, G τ ∂(K • ρ) := lintegral_mono' h2 le_rfl
    _ = K * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
        rw [lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hd hG, smul_eq_mul]
        congr 1
        exact lintegral_congr fun τ => mul_comm _ _

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAdaptedIsometryFrameUpperTriangularExpansio
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Sloc.AdaptExpand

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem exists_coeff {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ l : Fin D.R.rS → D.host.E, (∀ i, b.val ≤ i.val → l i = 0) ∧ x = ∑ i, l i • F.fl.e i := by
  have hx' : x ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < b.val}) := hx
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx'
  obtain ⟨l, hl, rfl⟩ := hx'
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra h
    have := hl (Finsupp.mem_support_iff.2 h)
    simp only [Set.mem_setOf_eq] at this
    omega
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

theorem exists_coeff_frame {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ u : Fin (D.R.rS + 1) → D.host.E, (∀ c, b ≤ c → u c = 0) ∧ x = ∑ c, u c • frame F c := by
  obtain ⟨l, hl, rfl⟩ := exists_coeff F b x hx
  refine ⟨Fin.snoc (α := fun _ => D.host.E) l 0, fun c hc => ?_, ?_⟩
  · induction c using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hl i (by simpa [Fin.le_def] using hc)
  · rw [Fin.sum_univ_castSucc]
    simp [frame_castSucc]

theorem adapt_expand : ∀ (D : D7) {T : D.host.E} (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F0 F → ∀ (Z : LocDat D) (p : PlF D) (Af : Fin (D.R.rS + 1) → Vp D p), Af = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) → ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = Ring.inverse (frFac Z.δ p a)) ∧ ∀ b, baseChange₂ D p (g (frame F0 b)) = ∑ a, B a b • Af a := by
  intro D T F0 F g hg Z p Af hAf
  subst hAf
  have hu := fun c => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p c
  choose u hu0 hux using fun b => exists_coeff_frame F b _ (hg.2 b)
  refine ⟨fun a b => ((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a),
    fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp [hu0 b a hab.le, (ne_of_lt hab).symm]
  · simp [hu0 a a le_rfl]
  · have e1 : g (frame F0 b) = frame F b + ∑ c, u b c • frame F c := by
      rw [← hux b]; abel
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_add (f := _), map_sum]
    simp only [baseChange_smul₂]
    have e2 : ∀ a, (((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a)) •
        (frFac Z.δ p a • baseChange₂ D p (frame F a)) =
        (D.s.atP p).ιE (u b a) • baseChange₂ D p (frame F a) + if a = b then baseChange₂ D p (frame F a) else 0 := by
      intro a
      rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel _ (hu a), mul_one, add_smul]
      split_ifs <;> simp
    simp only [e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel

end GlobalTheory.Sloc.AdaptExpand
end

