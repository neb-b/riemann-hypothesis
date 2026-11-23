module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0009

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstPush
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def FrameIndependentAtInfinity : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Y0 X u' ∈ IndI X

def ProperOrb : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K → K ⊆ IndI X →
      ∃ N ∈ 𝓝 (1 : MfI X), ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ b ∈ N, ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • rmulT X b (Y0 X u') ∈ K → g ∈ C

theorem continuous_smul_left {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem continuous_rmulT {D : D7} (X : HidaSetting D) (Y : TupI X) : Continuous (fun b : MfI X => rmulT X b Y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun b => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ => (continuous_apply_apply c b).mul continuous_const

theorem pushCont_of (hY : FrameIndependentAtInfinity) (hPr : ProperOrb) : PushCont := by
  intro D X u' ψ hT μinf νinf fibInf hH a ha1 hac
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : SecondCountableTopology (MfI X) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (HmI X) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hY0 := hY X u' ψ hT μinf νinf fibInf hH
  obtain ⟨V, hVo, hYV, hVc, -⟩ := exists_open_between_and_isCompact_closure isCompact_singleton (isOpen_IndI X)
    (Set.singleton_subset_iff.2 hY0)
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact isCompact_singleton hVo.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hYV)
  have hsupp : Function.support f ⊆ V := fun y hy => by
    by_contra h; exact hy (hf0 h)
  have htsupp : tsupport f ⊆ IndI X := (closure_mono hsupp).trans hVc
  have hfY : f (Y0 X u') = 1 := hf1 (Set.mem_singleton _)
  obtain ⟨N, hN, C, hC, hNC⟩ := hPr X u' ψ hT μinf νinf fibInf hH (tsupport f) hfc.isCompact htsupp
  have hbound : ∀ b ∈ N, ∀ g, ENNReal.ofReal (f (g • rmulT X b (Y0 X u'))) ≤ C.indicator 1 g := by
    intro b hb g
    by_cases hg : f (g • rmulT X b (Y0 X u')) = 0
    · rw [hg, ENNReal.ofReal_zero]; exact bot_le
    · have hgC : g ∈ C := hNC b hb g (subset_tsupport _ hg)
      rw [Set.indicator_of_mem hgC, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hfI _).2
  have h1N : (1 : MfI X) ∈ N := mem_of_mem_nhds hN
  have hCfin : ∫⁻ g, C.indicator 1 g ∂X.measG.μGinf < ⊤ :=
    lt_of_le_of_lt (lintegral_indicator_one_le C) hC.measure_lt_top
  refine ⟨f, f.continuous, f.continuous.measurable, hfc, htsupp, fun y => (hfI y).1, ?_, ?_, ?_⟩
  · have hm : Measurable fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => ENNReal.ofReal (f (g • Y0 X u')) :=
      ENNReal.measurable_ofReal.comp (f.continuous.comp (continuous_smul_left X (Y0 X u'))).measurable
    rw [lintegral_pos_iff_support hm]
    have hOo : IsOpen ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y}) :=
      (isOpen_lt continuous_const f.continuous).preimage (continuous_smul_left X (Y0 X u'))
    have h1O : (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
        (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {y | 0 < f y} := by
      show 0 < f ((1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) • Y0 X u')
      rw [one_smul, hfY]; exact one_pos
    refine lt_of_lt_of_le (hOo.measure_pos _ ⟨1, h1O⟩) (measure_mono fun g hg => ?_)
    exact (ENNReal.ofReal_pos.2 hg).ne'
  · refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hCfin
    have := hbound 1 h1N g
    rwa [rmulT_one] at this
  · have hev : ∀ᶠ T in 𝓝 (TI X u' hT), a T ∈ N := hac.preimage_mem_nhds (by rw [ha1]; exact hN)
    refine tendsto_lintegral_filter_of_dominated_convergence (C.indicator 1) ?_ ?_ hCfin.ne ?_
    · exact Eventually.of_forall fun T => ENNReal.measurable_ofReal.comp
        (f.continuous.comp (continuous_smul_left X _)).measurable
    · exact hev.mono fun T hT' => Eventually.of_forall fun g => hbound _ hT' g
    · refine Eventually.of_forall fun g => ?_
      exact (ENNReal.continuous_ofReal.comp (f.continuous.comp ((continuous_smul_tupI X g).comp
        (continuous_rmulT X (Y0 X u'))))).continuousAt.comp hac

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.S Matrix

def wF {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Fin (D.R.rS + 1 + D.R.rS) → (VS D).V :=
  Fin.append (Fin.snoc X.eX (X.zu u')) X.fY

theorem tupH_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    tupH (frameOf X u') = fun i => X.crd (wF X u' i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tupH, F0, wF, Fin.append_left]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp only [Fin.snoc_castSucc]; rfl
  · simp only [tupH, wF, Fin.append_right]; rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (i j : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j = X.ιE.symm ((VS D).hT (wF X u' i) (wF X u' j)) := by
  rw [tupH_eq, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X, RingEquiv.symm_apply_apply]
  rfl

theorem hT_fe {D : D7} (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  have h := (VS D).herm.eq (X.eX b) (X.fY a)
  rw [X.ef] at h
  rw [← h]
  split_ifs <;> simp

theorem hT_ze {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : Fin D.R.rS) :
    (VS D).hT (X.zu u') (X.eX a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u')
  rw [(X.zu_orth u' a).1] at h
  rw [← h]; simp

theorem hT_zf {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : Fin D.R.rS) :
    (VS D).hT (X.zu u') (X.fY a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u')
  rw [(X.zu_orth u' a).2] at h
  rw [← h]; simp

theorem row_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : Fin (D.R.rS + 1 + D.R.rS) → X.B.I.E)
    (i : Fin (D.R.rS + 1 + D.R.rS)) :
    X.ιE ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) *ᵥ v) i) =
      ∑ j, (VS D).hT (wF X u' i) (wF X u' j) * X.ιE (v j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, gram_eq, map_sum, map_mul, RingEquiv.apply_symm_apply]

theorem detNZ_holds : DetNZ := by
  intro D X u' ψ hT μinf νinf fibInf _
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have row : ∀ i, ∑ j, (VS D).hT (wF X u' i) (wF X u' j) * X.ιE (v j) = 0 := by
    intro i
    rw [← row_eq, hv]
    simp
  have hTne : ((((D.mem u').A.T : ℕ) : D.host.E)) ≠ 0 := by
    exact_mod_cast (D.mem u').A.T_prime.ne_zero
  have he : ∀ a, v (Fin.castAdd D.R.rS (Fin.castSucc a)) = 0 := by
    intro a
    have h := row (Fin.natAdd (D.R.rS + 1) a)
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, hT_fe, X.ff,
      (X.zu_orth u' _).2] at h
    exact h
  have hf : ∀ a, v (Fin.natAdd (D.R.rS + 1) a) = 0 := by
    intro a
    have h := row (Fin.castAdd D.R.rS (Fin.castSucc a))
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ef,
      (X.zu_orth u' _).1] at h
    exact h
  have hz : v (Fin.castAdd D.R.rS (Fin.last D.R.rS)) = 0 := by
    have h := row (Fin.castAdd D.R.rS (Fin.last D.R.rS))
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, hT_ze, hT_zf,
      X.zu_norm, hTne] at h
    exact h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact hz
    · exact he k
  · exact hf j

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacCut
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem rmulT_rmulT {D : D7} (X : HidaSetting D) (a b : MfI X) (Y : TupI X) :
    rmulT X b (rmulT X a Y) = rmulT X (a * b) Y := by
  funext d i
  simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem smul_rmulT {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (a : MfI X)
    (Y : TupI X) : g • rmulT X a Y = rmulT X a (g • Y) := by
  funext b i
  change Matrix.mulVec (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).1 (rmulT X a Y b) i =
    ∑ c, a c b * Matrix.mulVec (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).1 (Y c) i
  simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def BoxT {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X)
    (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : Set (HmI X)) : Set (TupI X) :=
  {y | ∃ T ∈ W, ∃ g ∈ V, y = g • rmulT X (a T) (Y0 X u')}

def TubeG {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
    Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  {g | ∃ g' ∈ V, g • Y0 X u' = g' • Y0 X u'}

def ChartPred : Type 1 := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word),
    (∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) →
    Measure (TupI X) → Measure (HmI X) → (HmI X → MfI X) → Prop

def JacOneFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ J : HmI X → ℝ, J (TI X u' hT) = 1 → ContinuousAt J (TI X u' hT) →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c₀ : ENNReal,
      PolId X u' μinf νinf a Ω₂ (fun T => c₀ * ENNReal.ofReal (J T)) → c₀ = (ENNReal.ofReal (KVal X u'))⁻¹

def LocRatioFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal /
        ((νinf (W n)).toReal * (X.measG.μGinf (TubeG X u' (V n))).toReal)) atTop (𝓝 (KVal X u')⁻¹)

theorem pre_box {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    {Ω : Set (HmI X)} {a : HmI X → MfI X} (hC : IsChart X u' hT Ω a)
    (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) {W : Set (HmI X)} (hW : W ⊆ Ω)
    (hU : ∀ T ∈ W, IsUnit (a T)) (T : HmI X) (hTW : T ∈ W) :
    {g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J | g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a V W} =
      TubeG X u' V := by
  ext g
  constructor
  · rintro ⟨T₁, hT₁, g', hg', e⟩
    have hG : T = T₁ := by
      apply Subtype.ext
      have h2 := congrArg (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) e
      rw [gramR_smul, gramR_smul, hC.2.2.2 T (hW hTW), hC.2.2.2 T₁ (hW hT₁)] at h2
      exact h2
    subst hG
    refine ⟨g', hg', ?_⟩
    obtain ⟨w, hw⟩ := hU T hTW
    rw [smul_rmulT, smul_rmulT] at e
    have h3 := congrArg (rmulT X (↑w⁻¹ : MfI X)) e
    rwa [rmulT_rmulT, rmulT_rmulT, ← hw, Units.mul_inv, rmulT_one, rmulT_one] at h3
  · rintro ⟨g', hg', e⟩
    refine ⟨T, hTW, g', hg', ?_⟩
    rw [smul_rmulT, smul_rmulT, e]

def SplitAsymFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)) (p : ℕ → ℝ),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤ ∧ 0 < p n) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (X.measG.μGinf (TubeG X u' (V n))).toReal / p n) atTop
        (𝓝 (Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F))) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal / (p n * (νinf (W n)).toReal)) atTop
        (𝓝 (Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F))))

theorem locRatioFor_of {Pr : ChartPred} (hK : KPos) (hS : SplitAsymFor Pr) : LocRatioFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  obtain ⟨V, W, p, hVW, hsh, hG, hTup⟩ := hS X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  refine ⟨V, W, fun n => ?_, hsh, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hVW n
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  set g0 : ℝ := Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F)
    with hg0
  set t0 : ℝ := Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) with ht0
  have hKe : KVal X u' = g0 * t0⁻¹ := by
    simp only [KVal, hg0, ht0, zpow_neg, zpow_natCast]
  have hg0ne : g0 ≠ 0 := by
    intro h; rw [hKe, h, zero_mul] at hK0; exact lt_irrefl _ hK0
  have ht0ne : t0 ≠ 0 := by
    intro h; rw [hKe, h, inv_zero, mul_zero] at hK0; exact lt_irrefl _ hK0
  have hlim := hTup.div hG hg0ne
  have hval : t0 / g0 = (KVal X u')⁻¹ := by
    rw [hKe, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  rw [hval] at hlim
  refine hlim.congr fun n => ?_
  obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt, hp⟩ := hVW n
  have hBr : 0 < (νinf (W n)).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have hMr : 0 < (X.measG.μGinf (TubeG X u' (V n))).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
  simp only [Pi.div_apply]
  field_simp

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbRepOf
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem orbRep_of (hK : KerMeas) (hU : HaarUniqInf) (hR : RegI) (hF : HinfFin) : OrbRep := by
  intro D X u' ψ hT μinf νinf fibInf hP ν hinv hsupp hlf
  obtain ⟨hb, FdN, FdN', u, hX⟩ := hP.1
  obtain ⟨horb, hsm, hmul, hhm, hcpt, hW, hInd⟩ := hR X u' ψ hT μinf νinf fibInf hP
  have hk := hK X u' ψ hT μinf νinf fibInf hP
  let μH : Measure (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := (X.measW u').μHinf
  have hH : μH.IsHaarMeasure := (X.measW_norm u').2.1
  have hfin : μH Set.univ < ⊤ := hF X hb FdN FdN' u u' hX
  have hne : μH Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μH Set.univ_nonempty
  have hne0 : μH ≠ 0 := fun h => hne (by rw [h]; rfl)
  have hae : ∀ᵐ y ∂ν, ∃ g : GI X, orbM X u' g = y := by
    rw [ae_iff]
    exact measure_mono_null (fun y hy => fun h => hy (hW h)) hsupp

  have kapp : ∀ y A, MeasurableSet A →
      kerI X u' y A = μH ((fun h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') =>
        sect X u' y * (h : GI X)) ⁻¹' A) := fun y A hA => Measure.map_apply (hhm _) hA
  set m : Measure (GI X) := ν.bind (kerI X u') with hm

  have minv : ∀ g : GI X, m.map (fun x => g * x) = m := by
    intro g
    ext A hA
    have hA' : MeasurableSet ((fun x => g * x) ⁻¹' A) := hmul g hA
    rw [Measure.map_apply (hmul g) hA, hm, Measure.bind_apply hA' hk.aemeasurable,
      Measure.bind_apply hA hk.aemeasurable]
    have hFm : Measurable fun y => kerI X u' y A := (Measure.measurable_coe hA).comp hk
    calc ∫⁻ y, kerI X u' y ((fun x => g * x) ⁻¹' A) ∂ν = ∫⁻ y, kerI X u' (g • y) A ∂ν := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          obtain ⟨h0, e⟩ := sect_smul X u' g y hy
          show kerI X u' y ((fun x => g * x) ⁻¹' A) = kerI X u' (g • y) A
          rw [kapp _ _ hA, kapp _ _ hA', e]
          have hS : MeasurableSet ((fun h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') =>
              sect X u' y * (h : GI X)) ⁻¹' ((fun x => g * x) ⁻¹' A)) := hhm _ hA'
          rw [← muH_preimage X u' μH hne0 h0 _ hS]
          congr 1
          ext h
          simp only [Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
      _ = ∫⁻ y, kerI X u' y A ∂(ν.map fun y => g • y) := (lintegral_map hFm (hsm g)).symm
      _ = ∫⁻ y, kerI X u' y A ∂ν := by rw [hinv g]

  have mfin : ∀ C : Set (GI X), IsCompact C → m C < ⊤ := by
    intro C hC
    obtain ⟨hCm, hCc, hCim⟩ := hcpt C hC
    rw [hm, Measure.bind_apply hCm hk.aemeasurable]
    calc ∫⁻ y, kerI X u' y C ∂ν ≤ ∫⁻ y, μH Set.univ * (orbM X u' '' C).indicator 1 y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyC : y ∈ orbM X u' '' C
          · rw [Set.indicator_of_mem hyC, Pi.one_apply, mul_one, kapp _ _ hCm]
            exact measure_mono (Set.subset_univ _)
          · rw [Set.indicator_of_notMem hyC, mul_zero, kapp _ _ hCm, nonpos_iff_eq_zero]
            convert measure_empty (μ := μH)
            ext h
            simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hh
            exact hyC ⟨_, hh, orbM_sect_mul X u' y hy h⟩
      _ = μH Set.univ * ν (orbM X u' '' C) := by
          rw [lintegral_const_mul _ (measurable_one.indicator hCim), lintegral_indicator_one hCim]
      _ < ⊤ := ENNReal.mul_lt_top hfin
          (hlf _ hCc ((Set.image_subset_range _ _).trans hInd))
  obtain ⟨c, hc, hmc⟩ := hU X u' ψ hT μinf νinf fibInf hP m minv mfin
  refine ⟨c / μH Set.univ, ENNReal.div_ne_top hc hne, Measure.ext fun B hB => ?_⟩
  have e : μH Set.univ * ν B = c * X.measG.μGinf.map (orbM X u') B := by
    rw [Measure.map_apply horb hB, show c * X.measG.μGinf (orbM X u' ⁻¹' B) =
        (c • X.measG.μGinf) (orbM X u' ⁻¹' B) by rw [Measure.smul_apply, smul_eq_mul], ← hmc, hm,
      Measure.bind_apply (horb hB) hk.aemeasurable, ← lintegral_indicator_one hB, ← lintegral_const_mul _
        (measurable_one.indicator hB)]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    show μH Set.univ * B.indicator 1 y = kerI X u' y (orbM X u' ⁻¹' B)
    symm
    rw [kapp _ _ (horb hB)]
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB, Pi.one_apply, mul_one]
      congr 1
      ext h
      simp only [Set.mem_preimage, Set.mem_univ, iff_true, orbM_sect_mul X u' y hy h]
      exact hyB
    · rw [Set.indicator_of_notMem hyB, mul_zero]
      convert measure_empty (μ := μH)
      ext h
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, orbM_sect_mul X u' y hy h]
      exact hyB
  rw [Measure.smul_apply, smul_eq_mul]
  calc ν B = (μH Set.univ)⁻¹ * (μH Set.univ * ν B) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne hfin.ne, one_mul]
    _ = (μH Set.univ)⁻¹ * (c * X.measG.μGinf.map (orbM X u') B) := by rw [e]
    _ = c / μH Set.univ * X.measG.μGinf.map (orbM X u') B := by rw [div_eq_mul_inv]; ring

end PI.AprimeInfW
end
end

