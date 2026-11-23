module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowth
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff Pointwise

namespace GlobalTheory.RadVol

private theorem measure_slice_le_measure_mul_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] {N : Set G} {ν : Measure G} (hnull : ν Nᶜ = 0)
    (hleft : ∀ m ∈ N, Measure.map (fun x => m * x) ν = ν) {K S : Set G} (hK : IsCompact K) (g : G) :
    ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν (K * K⁻¹) := by
  by_cases h0 : ∃ s₀ ∈ N, s₀⁻¹ * g ∈ K
  · obtain ⟨s₀, hs₀, hk₀⟩ := h0
    have hKK : MeasurableSet (K * K⁻¹) := (hK.mul hK.inv).isClosed.measurableSet
    have hpre : MeasurableSet ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := hKK.preimage (measurable_const_mul _)
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          apply measure_mono
          intro s hs
          simp only [Set.mem_preimage]
          rw [show s₀⁻¹ * s = (s₀⁻¹ * g) * (s⁻¹ * g)⁻¹ by group]
          exact Set.mul_mem_mul hk₀ (Set.inv_mem_inv.mpr hs.2)
      _ = Measure.map (fun x => s₀ * x) ν ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹)) := by
          rw [hleft s₀ hs₀]
      _ = ν ((fun x => s₀ * x) ⁻¹' ((fun x => s₀⁻¹ * x) ⁻¹' (K * K⁻¹))) :=
          Measure.map_apply (measurable_const_mul _) hpre
      _ = ν (K * K⁻¹) := by
          congr 1
          ext x
          simp
  · push_neg at h0
    have hsub : {s | s ∈ S ∧ s⁻¹ * g ∈ K} ⊆ Nᶜ := fun s hs hsN => h0 s hsN hs.2
    calc ν {s | s ∈ S ∧ s⁻¹ * g ∈ K} ≤ ν Nᶜ := measure_mono hsub
      _ = 0 := hnull
      _ ≤ ν (K * K⁻¹) := bot_le

theorem measure_mul_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {N : Set G} {ν : Measure G} (hν : IsHaarSub N ν) {K S T : Set G} (hK : IsCompact K) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ T) : ν S * μ K ≤ ν (K * K⁻¹) * μ T := by
  classical
  obtain ⟨-, hfc, hnull, hleft⟩ := hν
  haveI : IsFiniteMeasureOnCompacts ν := hfc
  haveI : SigmaFinite ν := inferInstance
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set E : Set (G × G) := {p | p.1 ∈ S ∧ p.1⁻¹ * p.2 ∈ K} with hEd
  have hE : MeasurableSet E :=
    (measurable_fst hS).inter ((measurable_fst.inv.mul measurable_snd) hKm)

  have h1 : ν.prod μ E = ν S * μ K := by
    rw [Measure.prod_apply hE]
    have hsl : ∀ s, μ (Prod.mk s ⁻¹' E) = S.indicator (fun _ => μ K) s := by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_apply, if_pos hs, ← measure_preimage_mul μ s⁻¹ K]
        congr 1
        ext x
        simp [hEd, hs]
      · rw [Set.indicator_apply, if_neg hs]
        have h0 : Prod.mk s ⁻¹' E = ∅ := by
          ext x
          simp [hEd, hs]
        rw [h0, measure_empty]
    simp_rw [hsl]
    rw [lintegral_indicator_const hS, mul_comm]

  have h2 : ν.prod μ E ≤ ν (K * K⁻¹) * μ T := by
    rw [Measure.prod_apply_symm hE]
    calc ∫⁻ g, ν ((fun s => (s, g)) ⁻¹' E) ∂μ
        ≤ ∫⁻ g, T.indicator (fun _ => ν (K * K⁻¹)) g ∂μ := by
          apply lintegral_mono
          intro g
          by_cases hg : g ∈ T
          · rw [Set.indicator_apply, if_pos hg]
            exact (le_of_eq (by rw [hEd]; rfl)).trans
              (measure_slice_le_measure_mul_inv (S := S) hnull hleft hK g)
          · rw [Set.indicator_apply, if_neg hg]
            have h0 : (fun s => (s, g)) ⁻¹' E = ∅ := by
              ext s
              simp only [hEd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                not_and]
              intro hs hk
              apply hg
              simpa using h s hs _ hk
            exact le_of_eq (by show ν ((fun s => (s, g)) ⁻¹' E) = 0; rw [h0, measure_empty])
      _ = ν (K * K⁻¹) * μ T := lintegral_indicator_const hT _
  calc ν S * μ K = ν.prod μ E := h1.symm
    _ ≤ ν (K * K⁻¹) * μ T := h2

private theorem dOp_nonneg_subadditive_continuous {n : ℕ} (ε : Fin n → Bool) :
    (∀ g : UJ ε, 0 ≤ dOp (umat g)) ∧
      (∀ g g' : UJ ε, dOp (umat (g * g')) ≤ dOp (umat g) + dOp (umat g')) ∧
      Continuous (fun g : UJ ε => dOp (umat g)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = 0 := by
      intro g
      have hz : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ = 0 := by
        refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
        rw [zero_mul, EuclideanSpace.norm_eq]
        simp
      simp only [dOp, hz, Real.log_zero]
    simp only [h0]
    exact ⟨fun _ => le_rfl, fun _ _ => by norm_num, continuous_const⟩
  · obtain ⟨-, h2, -, -, h5⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
    exact ⟨fun g => (h2 g 1 hn).1, fun g g' => (h2 g g' hn).2.2.1, h5⟩

theorem radical_volume_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)),
    IsIsoC ε W → IsHaarSub (NW ε W) ν →
    (∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r))) ∧
    ∀ b : ℝ, 4 * n * rkR ε < b → Integrable (fun m : UJ ε => Real.exp (-(b * dOp (umat m)))) ν := by
  intro n ε W ν _ hν
  obtain ⟨hP, hM, hD⟩ := dOp_nonneg_subadditive_continuous ε
  haveI : (muG ε).IsHaarMeasure := by
    first
    | infer_instance
    | (unfold muG; infer_instance)
  have hgrowth : ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      ν {m | dOp (umat m) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
    obtain ⟨C, -, hball⟩ := GlobalTheory.BallVol.ballVol n ε
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : UJ ε)
    have hμK : 0 < muG ε K := by
      first
      | exact measure_pos_of_mem_nhds (μ := muG ε) hK1
      | exact (muG ε).measure_pos_of_mem_nhds hK1
      | exact Measure.measure_pos_of_mem_nhds (muG ε) hK1
    have hμKt : muG ε K < ⊤ := by
      first
      | exact hKc.measure_lt_top (μ := muG ε)
      | exact IsCompact.measure_lt_top hKc
    have hνKK : ν (K * K⁻¹) < ⊤ := by
      haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
      exact (hKc.mul hKc.inv).measure_lt_top
    obtain ⟨B, hB⟩ := hKc.bddAbove_image hD.continuousOn
    refine ⟨(ν (K * K⁻¹)).toReal * C * Real.exp (4 * n * rkR ε * max B 0) / (muG ε K).toReal,
      fun r hr => ?_⟩

    have hmul : ∀ s ∈ {m : UJ ε | dOp (umat m) ≤ r}, ∀ k ∈ K,
        s * k ∈ {m : UJ ε | dOp (umat m) ≤ r + max B 0} := by
      intro s hs k hk
      have hkB : dOp (umat k) ≤ B := hB (Set.mem_image_of_mem _ hk)
      have hs' : dOp (umat s) ≤ r := hs
      show dOp (umat (s * k)) ≤ r + max B 0
      linarith [hM s k, le_max_left B 0]
    have key := measure_mul_le (muG ε) hν (S := {m : UJ ε | dOp (umat m) ≤ r})
      (T := {m : UJ ε | dOp (umat m) ≤ r + max B 0}) hKc (measurableSet_le hD.measurable measurable_const)
      (measurableSet_le hD.measurable measurable_const) hmul
    have hT : muG ε {m : UJ ε | dOp (umat m) ≤ r + max B 0} ≤
        ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * (r + max B 0))) :=
      hball _ (add_nonneg hr (le_max_right B 0))
    have hm : 0 < (muG ε K).toReal := ENNReal.toReal_pos hμK.ne' hμKt.ne
    have key2 : ν {m : UJ ε | dOp (umat m) ≤ r} * ENNReal.ofReal (muG ε K).toReal ≤
        ENNReal.ofReal ((ν (K * K⁻¹)).toReal * (C * Real.exp (4 * n * rkR ε * (r + max B 0)))) := by
      rw [ENNReal.ofReal_toReal hμKt.ne, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hνKK.ne]
      exact key.trans (by gcongr)
    have key3 := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hm).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr key2
    rw [← ENNReal.ofReal_div_of_pos hm] at key3
    refine key3.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [mul_add, Real.exp_add]
    ring
  refine ⟨hgrowth, fun b hb => ?_⟩
  obtain ⟨C, hC⟩ := hgrowth
  exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) ν (fun m => dOp (umat m)) (4 * n * rkR ε) b C
    hD.measurable hP hC hb

end GlobalTheory.RadVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.PermGroup
variable {n : ℕ}

lemma memLp_equiv {ε ε' : Fin n → Bool} (e : UJ ε' ≃ₜ* UJ ε) (F : UJ ε → ℂ) (p : ENNReal) :
    MemLp F p (muG ε) ↔ MemLp (fun g => F (e g)) p (muG ε') := by
  have hE : (Measure.map e (muG ε')).IsHaarMeasure := e.isHaarMeasure_map (muG ε')
  have hc : Measure.map e (muG ε') =
      Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) • muG ε := Measure.isMulLeftInvariant_eq_smul _ _
  set c : ENNReal := ((Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) : NNReal) : ENNReal)
    with hcdef
  have hc' : Measure.map e (muG ε') = c • muG ε := by rw [hcdef, ← ENNReal.smul_def]; exact hc
  have hT : c ≠ ⊤ := ENNReal.coe_ne_top
  have h0 : c ≠ 0 := by
    intro hz
    have hz' : Measure.map e (muG ε') = 0 := by rw [hc', hz, zero_smul]
    rw [Measure.map_eq_zero_iff
      (show AEMeasurable (⇑e) (muG ε') from (map_continuous e).measurable.aemeasurable)] at hz'
    exact NeZero.ne _ hz'
  have hm := (e.toHomeomorph.toMeasurableEquiv).memLp_map_measure_iff (g := F) (p := p) (μ := muG ε')
  change MemLp F p (Measure.map e (muG ε')) ↔ MemLp (F ∘ e) p (muG ε') at hm
  change MemLp F p (muG ε) ↔ MemLp (F ∘ e) p (muG ε')
  rw [← hm, hc']
  constructor
  · intro h
    exact h.smul_measure hT
  · intro h
    have h' := h.smul_measure (ENNReal.inv_ne_top.2 h0)
    rwa [smul_smul, ENNReal.inv_mul_cancel h0 hT, one_smul] at h'

def homUJ {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) : UJ ε' →* UJ ε :=
  ((Units.map φ).comp (UJ ε').subtype).codRestrict (UJ ε) fun g => h _ g.2

lemma homUJ_cont {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (hc : Continuous φ) : Continuous (homUJ φ h) := by
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  exact ⟨hc.comp (Units.continuous_val.comp continuous_subtype_val),
    hc.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

lemma memLp_hom {ε ε' : Fin n → Bool} (φ ψ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (h' : ∀ g ∈ UJset ε, ψ g ∈ UJset ε')
    (hc : Continuous φ) (hc' : Continuous ψ) (h1 : ∀ g, ψ (φ g) = g) (h2 : ∀ g, φ (ψ g) = g)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal) :
    MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔
      MemLp (fun g : UJ ε' => f (φ (umat g))) p (muG ε') := by
  let e : UJ ε' ≃ₜ* UJ ε :=
    { toFun := homUJ φ h
      invFun := homUJ ψ h'
      left_inv := fun g => Subtype.ext (Units.ext (h1 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      right_inv := fun g => Subtype.ext (Units.ext (h2 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      map_mul' := fun a b => map_mul (homUJ φ h) a b
      continuous_toFun := homUJ_cont φ h hc
      continuous_invFun := homUJ_cont ψ h' hc' }
  exact memLp_equiv e (fun g => f (umat g)) p

def perm (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ ≃+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ s).toRingEquiv

lemma perm_apply (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    perm s g = g.submatrix s.symm s.symm := rfl

lemma perm_cont (s : Equiv.Perm (Fin n)) : Continuous (perm s) := by
  have h : ⇑(perm s) = fun g => g.submatrix s.symm s.symm := funext (perm_apply s)
  rw [h]
  exact continuous_id.matrix_submatrix _ _

lemma perm_ct (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : (perm s g)ᴴ = perm s gᴴ := rfl

lemma perm_Jm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Jm ε = perm s (Jm (ε ∘ s)) := by
  rw [perm_apply]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Jm]
  · have hij' : s.symm i ≠ s.symm j := fun h => hij (s.symm.injective h)
    simp [Jm, hij, hij']

lemma perm_UJ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ UJset (ε ∘ s) ↔ perm s g ∈ UJset ε := by
  simp only [UJset, Set.mem_ofPred_eq, inUJ]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul]
  exact (perm s).injective.eq_iff.symm

lemma perm_K (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Kset (ε ∘ s) ↔ perm s g ∈ Kset ε := by
  simp only [Kset, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, EmbeddingLike.map_eq_one_iff, (perm s).injective.eq_iff]

lemma perm_P (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    inP (ε ∘ s) g ↔ inP ε (perm s g) := by
  simp only [inP, inG]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, ← map_add (f := _), ← map_neg, EmbeddingLike.map_eq_zero_iff,
    (perm s).injective.eq_iff]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
lemma perm_exp (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (perm s g) = perm s (NormedSpace.exp g) := (NormedSpace.map_exp (perm s) (perm_cont s) g).symm

def permM (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.submatrix s.symm s.symm
  map_one' := map_one (perm s)
  map_mul' := map_mul (perm s)

lemma permM_symm (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s.symm (permM s g) = g := by
  show (g.submatrix s.symm s.symm).submatrix s.symm.symm s.symm.symm = g
  ext i j
  simp

lemma permM_symm' (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s (permM s.symm g) = g := by
  show (g.submatrix s.symm.symm s.symm.symm).submatrix s.symm s.symm = g
  ext i j
  simp

def conj : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.map star
  map_one' := FormF.map_star_one
  map_mul' := FormF.map_star_mul

lemma conj_cont : Continuous (conj (n := n)) := by
  show Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.map star
  exact continuous_id.matrix_map continuous_star

theorem permGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  intro n ε s
  have hpm : ∀ (t : Equiv.Perm (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ), permM t x = perm t x :=
    fun t x => (perm_apply t x).symm
  have hcont : ∀ t : Equiv.Perm (Fin n), Continuous (permM t) := fun t => by
    have h : ⇑(permM t) = ⇑(perm t) := funext (hpm t)
    rw [h]
    exact perm_cont t
  refine ⟨fun g => ⟨?_, ?_, ?_, ?_⟩, fun f p => ⟨?_, ?_⟩⟩
  · rw [← perm_apply]; exact perm_UJ ε s g
  · rw [← perm_apply]; exact perm_K ε s g
  · rw [← perm_apply]; exact perm_P ε s g
  · rw [← perm_apply, ← perm_apply]; exact perm_exp s g
  · refine memLp_hom (permM s) (permM s.symm) (fun g hg => ?_) (fun g hg => ?_) (hcont s)
      (hcont s.symm) (permM_symm s) (permM_symm' s) f p
    · rw [hpm]; exact (perm_UJ ε s g).1 hg
    · apply (perm_UJ ε s _).2
      rw [← hpm, permM_symm']
      exact hg
  · exact memLp_hom GlobalTheory.Dec.PermGroup.conj GlobalTheory.Dec.PermGroup.conj (fun g hg => FormF.UJ_star hg)
      (fun g hg => FormF.UJ_star hg) conj_cont conj_cont (fun g => FormF.map_star_star g)
      (fun g => FormF.map_star_star g) f p

end GlobalTheory.Dec.PermGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VPSubOfLocalBound
section
open Formalism.MainNotions.S NumberField GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.StepTens

theorem dAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (P : ℕ) (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) (u : ∀ v, B.H v)
    (hu : ∀ v, u v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) (P + 1)) ∧
      dAct B (atPlace B v X) (B.tens u) = B.tens u' := by
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hloc := (GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v)
    (hd v) P).2.1 X.1 X.2 (u v) (hu v)
  have h1 : ∀ v, B.σ v 1 = 1 := fun v => (hU v).1.1
  set y := GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v) with hy
  have hder : ∀ v', HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (atPlace B v X v').1 (u v'))
      ((Pi.single v y : ∀ v, B.H v) v') 0 := by
    intro v'
    by_cases h : v' = v
    · subst h
      simpa [atPlace] using hloc.1
    · have h0 : atPlace B v X v' = 0 := by
        simp [atPlace, h]
      rw [h0, Pi.single_eq_of_ne h]
      have : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u v') = fun _ => u v' := by
        funext t
        simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
      rw [this]
      exact hasDerivAt_const _ _
  have hT := (GlobalTheory.TensDer.hasDerivAt_orbit_tens B (atPlace B v X) u _ hder h1).deriv
  refine ⟨Function.update u v y, ?_, ?_⟩
  · intro v'
    by_cases h : v' = v
    · subst h
      simpa using hloc.2
    · rw [Function.update_of_ne h]
      exact GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ (Nat.le_succ P) (hu v')
  · unfold dAct
    rw [hT, Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]
    · intro v' _ h
      rw [Pi.single_eq_of_ne h, ← hm]
      exact m.map_coord_zero v' (by simp)
    · simp

theorem wordAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (u : ∀ v, B.H v) (hu : ∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v))
    (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) l.length) ∧
      wordAct B l (B.tens u) = B.tens u' := by
  induction l with
  | nil =>
    refine ⟨u, fun v => ?_, rfl⟩
    rw [List.length_nil, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_zero]
    exact hu v
  | cons X l ih =>
    obtain ⟨u', h1, h2⟩ := ih
    obtain ⟨u'', h3, h4⟩ := dAct_tens_of_diff B hU hd l.length X.1 X.2 u' h1
    refine ⟨u'', h3, ?_⟩
    rw [← h4, ← h2]
    rfl

theorem stepSpan_le_of_differentiable (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w) (P : ℕ) :
    ∀ w ∈ VP B P, ∃ (k : ℕ) (u : Fin k → ∀ v, B.H v),
      (∀ l v, u l v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) ∧ w = ∑ l, B.tens (u l) := by
  classical
  intro w hw
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, u, hl, hu, rfl⟩ := hx
    obtain ⟨u', h1, h2⟩ := wordAct_tens_of_diff B hU hd u hu l
    exact ⟨1, fun _ => u', fun _ v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ hl (h1 v), by simp [h2]⟩
  | zero => exact ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨k', u', hu', rfl⟩ := hy
    refine ⟨k + k', Fin.append u u', ?_, ?_⟩
    · intro l
      refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · simpa using hu i
      · simpa using hu' i
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    refine ⟨k, fun l => Function.update (u l) v₀ (c • u l v₀), ?_, ?_⟩
    · intro l v
      by_cases h : v = v₀
      · subst h
        simpa using Submodule.smul_mem _ c (hu l v)
      · simpa [Function.update_of_ne h] using hu l v
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hm, ← hm, m.map_update_smul, Function.update_eq_self]

end GlobalTheory.StepTens
end

