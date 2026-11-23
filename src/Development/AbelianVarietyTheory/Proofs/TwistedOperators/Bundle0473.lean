module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierEqFiniteFourierSumDepth
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Pointwise

noncomputable section
namespace GlobalTheory.ColFourier

section Lemmas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem mem_maxIdeal_pow_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (n : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl

theorem natDatum_setCols_eq {ϖ : kˣ} {n : ℕ} {Φ : Matrix A C k → ℂ} (hΦ : IsNatDatum ϖ n Φ) (P : Finset C)
    (Y : Matrix A C k) {U V : Matrix A P k} (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) :
    Φ (setCols P Y U) = Φ (setCols P Y V) := by
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hZ : setCols P 0 (U - V) ∈ matLat A ((ϖ ^ n) • stdLat k C) := by
    rw [mem_matLat]
    intro i
    rw [mem_smul_lat, mem_stdLat]
    intro j
    by_cases hj : j ∈ P
    · have h1 := h i ⟨j, hj⟩
      simp only [cball, Set.mem_setOf_eq] at h1
      simp only [Pi.smul_apply, Matrix.row, setCols, of_apply, dif_pos hj, Matrix.sub_apply, Units.smul_def,
        smul_eq_mul]
      rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
      exact h1
    · simp [Matrix.row, setCols, hj]
  have := hΦ.2 (setCols P Y V) _ hZ
  rw [← this]
  congr 1
  ext i j
  by_cases hj : j ∈ P <;> simp [setCols, hj]

theorem psi_pairCols_eq {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} {n : ℕ} (P : Finset C)
    {Y : Matrix A C k} (hY : ∀ i, ∀ j ∈ P, ((ϖ ^ n : kˣ) : k) * Y i j ∈ 𝒪[k]) {U V : Matrix A P k}
    (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) : ψ (pairCols P Y U) = ψ (pairCols P Y V) := by
  have h1 : pairCols P Y U = pairCols P Y V + pairCols P Y (U - V) := by
    simp only [pairCols, ← Finset.sum_add_distrib, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, AddChar.map_add_eq_mul, hψ.eq_one (y := pairCols P Y (U - V)) ?_, mul_one]
  show valuation k _ ≤ valuation k ((1 : kˣ) : k)
  rw [Units.val_one, map_one]
  refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => ?_
  have h2 := h i j
  have h3 := hY i j j.2
  rw [cball, Set.mem_setOf_eq] at h2
  rw [Valuation.mem_integer_iff, map_mul] at h3
  rw [map_mul, Matrix.sub_apply]
  exact (mul_le_mul' h2 le_rfl).trans (by rw [mul_comm] at h3 ⊢; exact h3)

end Lemmas

theorem fourierInt_eq_fourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A]
    [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k) (ϖ : kˣ), IsUnif ϖ → HasConductor ψ 1 → IsUnitVol m →
    ∀ (P : Finset C) (n : ℕ) (Φ : Matrix A C k → ℂ), IsNatDatum ϖ n Φ →
      fourierInt ψ m P Φ = fourierSum ψ ϖ n P Φ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m ϖ hϖ hψ hm P n Φ hΦ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · rw [fourierInt]
    set F : Matrix A P k → ℂ := fun U => Φ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ) with hF
    let S : (A → P → Res k n) → Set (Matrix A P k) := fun T =>
      Set.univ.pi fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n)
    have hmemS : ∀ T U, U ∈ S T ↔ ∀ i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) := by
      intro T U
      exact ⟨fun h i j => by simpa [sub_eq_add_neg] using h i trivial j trivial,
        fun h i _ j _ => by simpa [sub_eq_add_neg] using h i j⟩
    have hS : ∀ T, MeasurableSet (S T) := fun T =>
      MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j =>
        (isOpen_cball _).measurableSet.preimage (measurable_add_const _)
    have hcb : m (cball (ϖ ^ n)) = (distribHaarChar k (ϖ ^ n) : ENNReal) := by
      rw [measure_cball, hm.2, mul_one]
    have hvolE : ∀ T, (volM m A P) (S T) = (distribHaarChar k (ϖ ^ n) : ENNReal) ^ (Fintype.card A * P.card) := by
      intro T
      simp only [volM, S]
      refine (Measure.pi_pi (fun _ : A => Measure.pi fun _ : P => m)
        (fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n))).trans ?_
      simp only [Measure.pi_pi, measure_preimage_add_right, hcb, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← pow_mul]
      rw [mul_comm]
    have hnabs : nabs k (ϖ ^ n) = ((resCard k : ℝ) ^ n)⁻¹ := by
      have h1 : ∀ l : ℕ, nabs k (ϖ ^ l) = nabs k ϖ ^ l := by
        intro l; induction l with
        | zero => simp [nabs_one]
        | succ l ih => rw [pow_succ, nabs_mul, ih, pow_succ]
      rw [h1, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, inv_pow]
    have hvol : ∀ T, (volM m A P).real (S T) = ((resCard k : ℝ) ^ (n * Fintype.card A * P.card))⁻¹ := by
      intro T
      rw [Measure.real, hvolE, ENNReal.toReal_pow, ENNReal.coe_toReal]
      have : ((distribHaarChar k (ϖ ^ n) : NNReal) : ℝ) = nabs k (ϖ ^ n) := rfl
      rw [this, hnabs, inv_pow, ← pow_mul, mul_assoc]
    have hfin : ∀ T, (volM m A P) (S T) ≠ ⊤ := fun T => by
      rw [hvolE]; exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hpt : ∀ U, F U = ∑ T, (S T).indicator (fun _ => F (liftRes T)) U := by
      intro U
      by_cases hU : ∀ i j, U i j ∈ 𝒪[k]
      · let T0 : A → P → Res k n := fun i j => Ideal.Quotient.mk _ ⟨U i j, hU i j⟩
        have key1 : ∀ T i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) ↔ T i j = T0 i j := by
          intro T i j
          have e : T i j = T0 i j ↔ (⟨U i j, hU i j⟩ - Quotient.out (T i j) : 𝒪[k]) ∈
              IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
            conv_lhs => rw [← Ideal.Quotient.mk_out (T i j)]
            rw [eq_comm]
            exact Ideal.Quotient.eq
          rw [e, mem_maxIdeal_pow_iff hϖ]
          rfl
        have key : ∀ T, U ∈ S T ↔ T = T0 := by
          intro T
          rw [hmemS]
          simp only [key1]
          exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => by rw [h]⟩
        rw [Finset.sum_eq_single T0 (fun T _ hT => Set.indicator_of_notMem (fun h => hT ((key T).1 h)) _)
          (by simp), Set.indicator_of_mem ((key T0).2 rfl)]
        have hd := (hmemS T0 U).1 ((key T0).2 rfl)
        simp only [hF]
        rw [natDatum_setCols_eq hΦ P Y hd, psi_pairCols_eq hψ P hY hd]
      · push_neg at hU
        obtain ⟨i, j, hij⟩ := hU
        have hz : F U = 0 := by
          simp only [hF]
          rw [hΦ.1 _ ?_, zero_mul]
          intro hm'
          apply hij
          have := mem_matLat_stdLat.1 hm' i j
          simpa [setCols, j.2] using this
        rw [hz]
        symm
        refine Finset.sum_eq_zero fun T _ => Set.indicator_of_notMem (fun h => hij ?_) _
        have h1 : valuation k (U i j - liftRes T i j) ≤ valuation k ((ϖ ^ n : kˣ) : k) := (hmemS T U).1 h i j
        have h2 : U i j - liftRes T i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff]
          refine le_trans h1 ?_
          rw [Units.val_pow_eq_pow_val, map_pow]
          exact pow_le_one' (hϖ.mem) n
        simpa using add_mem h2 (liftRes_mem T i j)
    rw [show F = fun U => ∑ T, (S T).indicator (fun _ => F (liftRes T)) U from funext hpt]
    rw [integral_finsetSum _ (fun T _ => (integrable_indicator_iff (hS T)).2
      (integrableOn_const (lt_top_iff_ne_top.2 (hfin T)).ne)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [integral_indicator_const _ (hS T), hvol, Complex.real_smul]
    push_cast
    rfl
  · rw [fourierInt_eq_pi]
    refine GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi _ hψ (s := ϖ ^ n) (fun t ht x => ?_) ?_
    · exact natDatum_setCols_eq hΦ P Y fun i j => by simpa using ht ⟨i, j⟩ trivial
    · intro hmem
      apply hY
      intro i j hj
      have h1 : valuation k (Y i j) ≤ valuation k ((((1 : kˣ) * (ϖ ^ n)⁻¹ : kˣ)) : k) := hmem ⟨i, ⟨j, hj⟩⟩ trivial
      rw [one_mul, Units.val_inv_eq_inv_val, map_inv₀] at h1
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j)
          ≤ valuation k ((ϖ ^ n : kˣ) : k) * (valuation k ((ϖ ^ n : kˣ) : k))⁻¹ := mul_le_mul' le_rfl h1
        _ = 1 := mul_inv_cancel₀ h0.ne'

end GlobalTheory.ColFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierMemSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A C : Type} [Fintype A] [DecidableEq C]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem setCols_eq_add_offBlock (P : Finset C) (Y Y' : Matrix A C k) (T : Matrix A P k) :
    setCols P Y' T = setCols P Y T + setCols P (Y' - Y) 0 := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem setCols_of_add (P : Finset C) (Y : Matrix A C k) (x t : (Σ _ : A, P) → k) :
    setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩) =
      setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) + setCols P 0 (Matrix.of fun i j => t ⟨i, j⟩) := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_left (P : Finset C) (T : Matrix A P k) :
    Continuous fun Y : Matrix A C k => setCols P Y T := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]; exact continuous_const
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_id.matrix_elem i j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × ((Σ _ : A, P) → k) =>
      setCols P q.1 (Matrix.of fun i j => q.2 ⟨i, j⟩) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨i, ⟨j, h⟩⟩ : (Σ _ : A, P))).comp continuous_snd
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_fst.matrix_elem i j

omit [DecidableEq C] in
theorem continuous_pairCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × Matrix A P k => pairCols P q.1 q.2 := by
  unfold pairCols
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_snd.matrix_elem i j).mul (continuous_fst.matrix_elem i (j : C))

end GlobalTheory.ColFourier

theorem GlobalTheory.ColFourier.fourierInt_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ m P Ξ ∈ SB (Matrix A C k) := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have hinv := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant hΞ
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun Y => ?_, ?_⟩
  · have hK : IsCompact (restrictCols P '' tsupport Ξ) := hΞ.2.image (continuous_restrictCols P)
    have h1 : ∀ᶠ Y' in 𝓝 Y, ∀ X, Ξ (X + setCols P (Y' - Y) 0) = Ξ X := by
      have hc : Continuous (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) :=
        (continuous_setCols_left P 0).comp (continuous_id.sub continuous_const)
      have h0 : setCols P (Y - Y) (0 : Matrix A P k) = 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have ht : Filter.Tendsto (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) (𝓝 Y) (𝓝 0) := by
        convert hc.tendsto Y using 2
        exact h0.symm
      exact ht.eventually hinv
    have h2 : ∀ᶠ Y' in 𝓝 Y, ∀ T ∈ restrictCols P '' tsupport Ξ,
        ψ (pairCols P Y' T) = ψ (pairCols P Y T) := by
      refine hK.eventually_forall_of_forall_eventually fun T _ => ?_
      have h3 : IsLocallyConstant fun q : Matrix A C k × Matrix A P k =>
          (ψ (pairCols P q.1 q.2), ψ (pairCols P Y q.2)) :=
        (hψ.isLocallyConstant.comp_continuous (continuous_pairCols_pair P)).prodMk
          (hψ.isLocallyConstant.comp_continuous
            ((continuous_pairCols_pair P).comp (continuous_const.prodMk continuous_snd)))
      filter_upwards [h3.eventually_eq (Y, T)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1, h2] with Y' hY1 hY2
    unfold fourierInt
    congr 1
    funext T
    rw [setCols_eq_add_offBlock P Y Y' T, hY1]
    by_cases hT : setCols P Y T ∈ tsupport Ξ
    · rw [hY2 T ⟨_, hT, restrictCols_setCols P Y T⟩]
    · simp [image_eq_zero_of_notMem_tsupport hT]
  · have hc : Continuous fun t : (Σ _ : A, P) → k =>
        setCols P (0 : Matrix A C k) (Matrix.of fun i j => t ⟨i, j⟩) :=
      (continuous_setCols_pair P).comp (continuous_const.prodMk continuous_id)
    have h0 : setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩) = 0 := by
      ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
    have hU : {Z : Matrix A C k | ∀ X, Ξ (X + Z) = Ξ X} ∈
        𝓝 (setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩)) := by
      rw [h0]; exact hinv
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (hc.continuousAt.preimage_mem_nhds hU)
    refine HasCompactSupport.intro ((hΞ.2.prod (FourierPi.isCompact_box (1 * s⁻¹))).image
      (continuous_setCols_pair P)) fun Y hY => ?_
    rw [fourierInt_eq_pi]
    by_cases hy : (fun p : (Σ _ : A, P) => Y p.1 p.2) ∈ FourierPi.box (Σ _ : A, P) (1 * s⁻¹)
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      have hback : setCols P (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
          (Matrix.of fun i j => (fun p : (Σ _ : A, P) => Y p.1 p.2) ⟨i, j⟩) = Y := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have hX : setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) ∉ tsupport Ξ := fun hX =>
        hY ⟨(_, fun p => Y p.1 p.2), ⟨hX, hy⟩, hback⟩
      simp [image_eq_zero_of_notMem_tsupport hX]
    · refine FourierPi.fourier_eq_zero_pi (Measure.pi fun _ : (Σ _ : A, P) => m) hψ (s := s)
        (f := fun x => Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))) (fun t ht x => ?_) hy
      show Ξ (setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩)) = Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
      rw [setCols_of_add]
      exact hs ht _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace : ∀ (D : D7) (S T : HSp D) (ε : AE D), IsSplitIdem D ε → ∀ g : GA D T, SuppAt ε T g → GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) = (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) * (GlobalTheory.SplitIdx.halfLat S T (cA D ε)).relIndex ((GlobalTheory.SplitIdx.halfLat S T (cA D ε)).map (GlobalTheory.SplitIdx.actL S T g)) := by
  first | exact @GlobalTheory.SplitIdxDec.idx_dec | exact GlobalTheory.SplitIdxDec.idx_dec | (intros; apply GlobalTheory.SplitIdxDec.idx_dec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowVertex

open GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def firstIx (D : D7) : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩

def rowShift0 (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)) :
    (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (firstIx D) D.R.m) (G.toPair (.chi (firstIx D) D.R.m)
    ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)

theorem rowShift0_theta (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    {f : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ}
    (h : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (rowShift0 S k f) :=
  (W.om_is _ (inRange_chi (firstIx D))).om_pres _ _ h

def movedRow (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) :
    ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ :=
  Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D)))

theorem rowMapV_update_zero (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid 0 D.R.m))
    (hg : IsThetaFunO W.ψ (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) (gs (firstIx D))) :
    rowMapV S gs (Function.update y 0 (y 0 * k)) = rowMapV S (movedRow S k gs) y := by
  unfold rowMapV movedRow
  refine congrArg (fun F => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) F D.R.m) _) ?_
  funext i
  by_cases hi : i < D.R.m
  · simp only [dif_pos hi]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [Function.update_self, Function.update_of_ne (show (0 + 1 : ℕ) ≠ 0 by omega)]
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨0, hi⟩ = rowShift0 S k (gs (firstIx D)) :=
        Function.update_self _ _ _
      have hm : y 0 * k * S.N.u (.grid 0 D.R.m) =
          (y 0 * S.N.u (.grid 0 D.R.m)) * ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)) := by group
      rw [hu, hm]
      exact congrArg _ (GlobalTheory.KerTrans.fockComp_mul_fin W S.N.frC (inRange_chi (firstIx D)) _ hg _ _ _)
    · have h2 : (⟨i, hi⟩ : Fin D.R.m) ≠ firstIx D := by
        intro h; have := congrArg Fin.val h; simp [firstIx] at this; omega
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨i, hi⟩ = gs ⟨i, hi⟩ :=
        Function.update_of_ne h2 _ _
      have hy1 : Function.update y 0 (y 0 * k) i = y i := Function.update_of_ne (by omega) _ _
      have hy2 : Function.update y 0 (y 0 * k) (i + 1) = y (i + 1) := Function.update_of_ne (by omega) _ _
      rw [hu, hy1, hy2]
  · simp only [dif_neg hi]

theorem prod_update_smul {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (F : ∀ i, X i → ℂ) (i₀ : ι) (h : X i₀ → ℂ)
    (c : ℂ) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (c • h) i (ys i) = c * ∏ i, Function.update F i₀ h i (ys i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end GlobalTheory.FirstRowVertex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FramesExistLev

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

theorem selfDual_frames_normal_at_level_places_of_charFrame : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (Pg : Finset (Pl D.host.E)),
    (∀ PP, PP ∈ Pg ↔ ∃ l, C.P.Div l PP) → FramesExistDiagonal D Pg := by
  intro D C Pg hPg
  let L : LevCh D Empty :=
    { C := C, xiH := fun t => t.elim, mu0 := fun _ => 1, eta := 1, xi := fun t => t.elim, Pg := Pg,
      Q := fun t => t.elim, chi := fun _ _ => 1, xiR := fun t => t.elim,
      ΛY := fun _ => ⊥, ΛX := ⊥, ΛV := fun _ => ⊥, ΛW := fun _ => ⊥,
      βY := fun _ => 1, βX := 1, βV := fun _ => 1, βW := fun _ => 1 }
  have hP : ∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP := hPg
  have hQ : ∀ t, Formalism.IndefR.Lev.IsTwistPlaces D.host.g (L.Q t) := fun t => t.elim
  have hbase (j : ℕ) := GlobalTheory.StdFrames.exists_base (D.sp.X j)
  choose γ hγ using hbase
  have hγ' : ∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0) := fun j _ => by
    rw [hγ j]; exact GlobalTheory.StdFrames.isFrame_lat _
  have hex : ∀ j, ∃ (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V), j < D.R.m → IsAuxiliaryHeckeCharacter D j E Ev z := fun j => by
    by_cases hj : j < D.R.m
    · obtain ⟨E, Ev, z, h⟩ := GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D j hj
      exact ⟨E, Ev, z, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hj⟩
  choose E₁ Ev₁ z₁ hA₁ using hex
  let E : ∀ j, ℕ → (D.sp.Y j).V := fun j => match j with
    | 0 => fun i => if h : i < D.R.rS then D.sp.hypE ⟨i, h⟩ else 0
    | j + 1 => E₁ (j + 1)
  let Ev : ∀ j, ℕ → (D.sp.Y j).V := fun j => match j with
    | 0 => fun i => if h : i < D.R.rS then D.sp.hypF ⟨i, h⟩ else 0
    | j + 1 => Ev₁ (j + 1)
  let z : ∀ j, (D.sp.Y j).V := fun j => match j with
    | 0 => D.sp.zm
    | j + 1 => z₁ (j + 1)
  have hAux : ∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j) := by
    intro j hj
    cases j with
    | zero => exact isAuxiliaryHyperbolicPart_initialChainSpace
    | succ j => exact hA₁ (j + 1) hj
  have hE0 : ∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩ := fun i hi =>
    ⟨dif_pos hi, dif_pos hi⟩
  have hz0 : z 0 = D.sp.zm := rfl
  obtain ⟨L', hS, hF, hSh⟩ := GlobalTheory.StdFrames.framesStdExist D Empty L hP hQ γ E Ev z hγ'
  have hPg' : L'.Pg = Pg := hS.2.2.2.2.2.1
  have hP' : ∀ PP, PP ∈ L'.Pg ↔ ∃ l, L'.C.P.Div l PP := by
    rw [hS.1]; exact hS.2.2.2.2.2.1 ▸ hP
  obtain ⟨⟨e, ev, z', κ, s, h1, h2⟩, hX⟩ :=
    GlobalTheory.NormalFramesStd.normalFrames_of_stdShape L' hP' γ E Ev z hγ' hAux hE0 hz0 hSh
  have hV : ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L'.βY 0) (L'.βW i) eW ι L'.Pg := fun i =>
    GlobalTheory.VertexFromTransport.vertexAt_of_levTransport L' hP' i (hSh.2.2.2.2 i)
  rw [← hPg']
  exact ⟨L'.ΛY, L'.ΛX, L'.ΛV, L'.ΛW, L'.βY, L'.βX, L'.βV, L'.βW, hF, ⟨e, ev, z', κ, s, ⟨h1, h2⟩, hV⟩, hX⟩

end GlobalTheory.FramesExistLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceChartFramesConjMaximalCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_chart_frames_conj_maximalCompact : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∃ φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε ∧ (∃ BS, GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS) ∧ ∃ BT, GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT ∧ ∃ ψ : Fv D.host.F v ≃+* w.adicCompletion D.host.E, (∀ a, Valued.v (ψ a) = Valued.v a) ∧ qV D.host.F v = qV D.host.E w ∧ ∃ κ ∈ KGL v (n := T.rank), ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT (embV T v (e.symm x)) = κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x * κ := by
  first | exact @GlobalTheory.SplitChartLink.link | exact GlobalTheory.SplitChartLink.link | (intros; apply GlobalTheory.SplitChartLink.link <;> assumption)
end

