module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharacters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0330
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.FJConv

theorem iterated_integrableOn {G N : Type} [TopologicalSpace G] [FirstCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
    {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N} (hμ : μ 𝓕 ≠ ⊤) (hν : ν 𝓝 ≠ ⊤) {P : G → N → ℂ}
    (hP : Continuous fun q : G × N => P q.1 q.2) {M : ℝ} (hM : ∀ g n, ‖P g n‖ ≤ M) :
    (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ := by
  have h1 : ∀ g, Continuous (P g) := fun g => hP.comp (Continuous.prodMk_right g)
  have h2 : ∀ n, Continuous fun g => P g n := fun n => hP.comp (Continuous.prodMk_left n)
  have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hν
  refine ⟨fun g => Measure.integrableOn_of_bounded (M := M) hν (h1 g).measurable.aestronglyMeasurable
    (.of_forall (hM g)), ?_⟩
  have hc : Continuous fun g => ∫ n in 𝓝, P g n ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun g => (h1 g).measurable.aestronglyMeasurable)
      (fun g => .of_forall (hM g)) (integrable_const M) (.of_forall h2)
  exact Measure.integrableOn_of_bounded (M := M * ν.real 𝓝) hμ hc.measurable.aestronglyMeasurable
    (.of_forall fun g => norm_setIntegral_le_of_norm_le_const hν.lt_top fun n _ => hM g n)

end GlobalTheory.Per.FJConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorsAreCuspFormsSingleLowestKType
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCuspKType

private theorem one_mem_Kg_flag_measures (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show (1 : I.Gf) ∈ I.Kset
    simp only [AutInst.Kset, Set.mem_ofPred_eq, OneMemClass.coe_one]
    exact one_mem _
  · simp only [AutInst.fmat, OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_mulVec, smul_zero]

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  obtain ⟨h1, hm, hn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  set π : B.I.Gf → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) := fun g => B.R (1, g) with hπ
  have p1 : π 1 = 1 := h1
  have pm : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    have : ((1 : B.I.Ginf), a * b) = ((1 : B.I.Ginf), a) * (1, b) := by simp
    simp only [hπ, this, hm]
  have pn : ∀ g v, ‖π g v‖ = ‖v‖ := fun g v => hn _ v
  have he : ∀ g, B.e (k * g) = B.e g := by
    intro g
    have := B.e_adm.2.2.2.2.2.1 g k hk 1 (one_mem_Kg_flag_measures B.I B.g)
    simpa using this
  ext1 y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  change inner ℂ x (π k (B.Re y)) = _
  rw [GlobalTheory.IdemProj.inner_rep π p1 pm pn, B.Re_spec.2, B.Re_spec.2]
  have key : ∀ g, B.e g * inner ℂ (π k⁻¹ x) (B.R (1, g) y)
      = (fun g' => B.e g' * inner ℂ x (B.R (1, g') y)) (k * g) := by
    intro g
    have e1 : inner ℂ (π k⁻¹ x) (B.R (1, g) y) = inner ℂ x (π k (π g y)) := by
      rw [GlobalTheory.IdemProj.inner_rep π p1 pm pn k x]
    have e2 : π k (π g y) = B.R (1, k * g) y := by
      show π k (π g y) = π (k * g) y
      rw [pm]; rfl
    simp only [e1, e2, he]
  simp_rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun g' => B.e g' * inner ℂ x (B.R (1, g') y)) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hb, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hcond : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | hpos
    · exact Or.inl h0
    · right
      have hq : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hpos
      have hnr : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
          = Real.sqrt (rkR (B.I.ε v)) * (rkR (B.I.ε v) : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
          Real.rpow_add hq, Real.rpow_one]
      have hs : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.mpr hq
      have hv := hh v
      rw [hpow] at hv
      have hpos' : 0 < Real.sqrt (rkR (B.I.ε v)) * (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) := by positivity
      nlinarith
  have hI := hi 0 le_rfl hcond
  simp only [zero_mul, Real.exp_zero, mul_one] at hI
  exact hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem row_isCuspFn : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro B d h hd hK hg hh hl hbig T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  · intro W hW
    have : IsEmpty (Fin B.I.n) := by rw [hn0]; infer_instance
    exact absurd (Submodule.eq_bot_of_subsingleton) hW.1
  have hn : 1 ≤ B.I.n := hnpos
  have hint := integrable_ph B d h hd hn hh hl
  obtain ⟨-, hcomm, -, hT'⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := (hT' T hT).2.1 A hA
  obtain ⟨A₀, hA₀, hAe⟩ := Submodule.mem_map.mp hA
  have hAe' : A = B.Re.comp A₀ := by rw [← hAe]; rfl
  subst hAe'
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hhom : B.Re.comp A₀ ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, (B.Re.comp A₀).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A₀)
    intro g
    rw [ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ B.I.Kg B.g, B.R (1, k) ((B.Re.comp A₀) (B.tens B.w)) = (B.Re.comp A₀) (B.tens B.w) := by
    intro k hk
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re,
      level_comp_Re B k hk hg]
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf B d hd hK hn hg
  obtain ⟨f, hf, hfb⟩ := hC _ hhom hlev
  have hvan := _root_.GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf B d h hd hK hl hh
  refine (_root_.GlobalTheory.CuspFixed.cusp_of_fixed B d h hd hvan hl hbig T hT _ f (C * ‖(B.Re.comp A₀) (B.tens B.w)‖) ?_ hf ?_).2
  · simpa using hfix
  · intro x
    exact (hfb x).trans_eq (by ring)

end GlobalTheory.RowCuspKType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTerm
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem GFset_eq_one_of_place (I : AutInst) (γ : I.GA) (hγ : γ ∈ I.GFset) (v : InfinitePlace I.F)
    (h : uMat (γ.1 v) = 1) : γ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hγ
  have hdet : ∀ w, IsUnit (I.P w).det := fun w => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit w)
  set M : Matrix (Fin I.n) (Fin I.n) I.E := (g : Matrix (Fin I.n) (Fin I.n) I.E) with hM
  have e1 : (I.P v)⁻¹ * M.map (I.φ v) * I.P v = 1 := (hinf v).symm.trans h
  have e2 : M.map (I.φ v) * I.P v = I.P v := by
    have := congrArg (I.P v * ·) e1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hdet v)] using this
  have e3 : M.map (I.φ v) = 1 := by
    have := congrArg (· * (I.P v)⁻¹) e2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v)] using this
  have hg : M = 1 := by
    apply Matrix.map_injective (I.φ v).injective
    dsimp only
    rw [e3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext (funext fun w => ?_) ?_
  · have hw : uMat (γ.1 w) = 1 := by
      rw [hinf w, hg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (hdet w)]
    exact Subtype.ext (Units.ext (by simpa using hw))
  · have hf : I.fmat γ.2 = 1 := by
      rw [hfin, hg, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (Units.ext (by simpa using hf))

theorem one_mem_GFset_def (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))]
    rfl
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem definite_count_of_finite : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) →
      (B.D : ℝ) = mainTerm B d := by
  intro B d p hH hfin
  have hn : B.I.n = p := hH.rank_eq
  obtain ⟨hDS, hSig, hp, -, hprime, hgt, hsplit⟩ := hH
  have hn1 : 1 ≤ B.I.n := hn ▸ hp

  have hq : ∀ v, (univ.filter fun a => B.I.ε v a = false).card = 0 := fun v => (hSig v).2
  have hrk : ∀ v, rkR (B.I.ε v) = 0 := fun v => by
    unfold rkR
    rw [hq v]
    exact Nat.min_zero _
  have hpos : ∀ v a, B.I.ε v a = true := fun v a => by
    by_contra hne
    have ha : a ∈ univ.filter fun a => B.I.ε v a = false := by simpa using hne
    rw [Finset.card_eq_zero.mp (hq v)] at ha
    exact Finset.notMem_empty a ha
  have hJ : ∀ v, Formalism.REAL.Jm (B.I.ε v) = 1 := fun v => by
    unfold Formalism.REAL.Jm
    simp [hpos v]
  have hunit : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), (uMat g)ᴴ * uMat g = 1 := fun v g => by
    have h0 : (uMat g)ᴴ * Formalism.REAL.Jm (B.I.ε v) * uMat g = Formalism.REAL.Jm (B.I.ε v) := g.2
    rwa [hJ v, Matrix.mul_one] at h0
  have hdHS : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), dHS (uMat g) = 0 := fun v g =>
    (_root_.GlobalTheory.Count.CartanSize.cartan_size B.I.n (B.I.ε v)).2.2.2 (hrk v) g

  have hrad := _root_.GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver B.I.E B.g₀ hprime hsplit
  have hNU := (GlobalTheory.NearElement.near_unipotent B d (1 / 10 ^ 5) (by norm_num) le_rfl hn1 hgt hrad _ _
    rfl rfl).1
  have hkey : ∀ x γ : B.I.GA, γ ∈ B.I.GFset → phe B d (x⁻¹ * γ * x) ≠ 0 → γ = 1 := by
    intro x γ hγ hne
    have hep : (0 : ℝ) ≤ 1 / 10 ^ 5 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) := by positivity
    obtain ⟨-, hu, -⟩ := hNU x γ ⟨hγ, hne, fun v => by rw [hdHS]; exact hep⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    apply GFset_eq_one_of_place B.I γ hγ v
    apply GlobalTheory.unipotent_isometry_definite_eq_one B.I.n B.I.n _ 1 one_ne_zero _ (hu v)
    simpa using hunit v (γ.1 v)

  have hker : ∀ x, kern B.I (phe B d) x x = phe B d 1 := by
    intro x
    unfold kern
    rw [tsum_eq_single (⟨1, one_mem_GFset_def B.I⟩ : B.I.GFset)]
    · simp
    · intro γ hγ
      by_contra hne
      exact hγ (Subtype.ext (hkey x γ.1 γ.2 hne))
  have hph1 : ph B d 1 = ((∏ v, d v : ℝ) : ℂ) := by
    unfold ph
    have hc : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1 := by
      intro v
      have hs : B.σ v (uMat ((1 : B.I.Ginf) v)) = 1 := by
        rw [show uMat ((1 : B.I.Ginf) v) = 1 from rfl]
        exact (hDS v).2.1.2.2.1.1.1
      rw [hs, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, (hDS v).2.2.1.1]
      simp
    rw [Finset.prod_congr rfl (fun v _ => hc v)]
    simp

  have hloc : LocDec B 0 := by
    intro v g
    have hd : decE (rkR (B.I.ε v)) 0 (dOp (uMat g)) = 1 := by simp [decE]
    rw [hd]
    calc ‖⟪B.w v, B.σ v (uMat g) (B.w v)⟫_ℂ‖ ≤ ‖B.w v‖ * ‖B.σ v (uMat g) (B.w v)‖ :=
          norm_inner_le_norm _ _
      _ = 1 := by rw [(hDS v).2.1.2.2.1.2.1 _ g.2 _, (hDS v).2.2.1.1]; norm_num
  have hbig : HBig B 32 0 := by
    intro v
    rw [hrk v]
    simp
  obtain ⟨hcont, hbd, hmaj⟩ := _root_.GlobalTheory.Dec.PhMajProof.phMaj B d 0 hDS hloc
  have hm := hmaj 0 le_rfl (fun v => Or.inl (hrk v))
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  have hint : Integrable (ph B d) (muInf B.I) :=
    hm.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  obtain ⟨T, hT⟩ := (_root_.GlobalTheory.GlobProj.globalProj_holds B d hDS hint).2.2.1
  obtain ⟨-, -, -, -, -, -, -, hD, -⟩ := _root_.GlobalTheory.KernelExpansion.kernelB B d 0 hDS hn1 hloc hbig hfin T hT
  simp_rw [hker] at hD
  rw [setIntegral_const] at hD
  have hphe : phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 := by
    show ph B d (1 : B.I.GA).1 * B.e (1 : B.I.GA).2 = _
    rw [Prod.fst_one, Prod.snd_one, hph1]
  rw [hphe] at hD
  have he1 := (GlobalTheory.rowsAut_idem_elementary B).1
  have hre := congrArg Complex.re hD
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, he1,
    mul_zero, sub_zero, zero_mul, Complex.natCast_re] at hre
  unfold mainTerm AutInst.Dstar AutInst.vol
  rw [← hre, measureReal_def]
  ring

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicCorrectionLevelCharacter
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.level_char_match : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Λ Fr h0 hh0
  obtain ⟨Fr', hFr'⟩ := _root_.GlobalTheory.St.G.FrMap.transport F E n cm.sig J Λ (hat F S.Lb) (gp 0 * gp 1) k h0 hh0 Fr
  obtain ⟨κ, hκ, hκU⟩ := _root_.GlobalTheory.St.G.LvlZero.level_conj_frame F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Fr'
  refine ⟨h0 * κ, ?_, ?_⟩
  · intro x
    have hκi : (κ⁻¹ : UPts cm.sig J (Ad F)).1 ∈ stabGL (hat F S.Lb) := by
      simpa using (stabGL (hat F S.Lb)).inv_mem hκ
    have e : ((h0 * κ)⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x = (κ⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ ((h0⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x) := by
      rw [_root_.mul_inv_rev]; simp [Matrix.mulVec_mulVec]
    rw [e, ← hκi _, hh0]
  · intro y
    have e : ((h0 * κ)⁻¹ * y * (h0 * κ) : UPts cm.sig J (Ad F)) = κ⁻¹ * (h0⁻¹ * y * h0) * κ := by group
    obtain ⟨h1, h2⟩ := hFr' y
    obtain ⟨h3, h4⟩ := hκU (h0⁻¹ * y * h0)
    refine ⟨?_, ?_⟩
    · rw [h1, h3, e]
    · intro hy
      rw [h2]
      have hy' : ((κ⁻¹ * (h0⁻¹ * y * h0) * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U := by rw [← e]; exact hy
      rw [h4 hy']
      have hx : (⟨_, hy'⟩ : S.U) = ⟨_, hy⟩ := Subtype.ext (congrArg (fun z : UPts cm.sig J (Ad F) => z.1) e.symm)
      rw [hx]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfStepsStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps : TieOfCtx → StepChoiceConstantsC → StepAnalyticP → StepAnalyticConstantsP := by
  first | exact @GlobalTheory.NGRow.exists_row_level_analytic | exact GlobalTheory.NGRow.exists_row_level_analytic | (intros; apply GlobalTheory.NGRow.exists_row_level_analytic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualTrace
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

namespace GlobalTheory.TraceSelfDual

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [Field R] [Algebra F R]
  (ι : Type) [Fintype ι]

noncomputable def traceBilin : LinearMap.BilinForm R (ι → R ⊗[F] E) :=
  LinearMap.mk₂ R (fun x y => ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem traceBilin_apply (x y : ι → R ⊗[F] E) :
    traceBilin R ι x y = ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i) := rfl

theorem traceBilin_symm (x y : ι → R ⊗[F] E) : traceBilin R ι x y = traceBilin R ι y x := by
  simp only [traceBilin_apply, mul_comm]

variable [NumberField F] [NumberField E]

theorem eq_zero_of_traceBilin {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : ι → R ⊗[F] E)
    (hx : ∀ y, traceBilin R ι x y = 0) : x = 0 := by
  classical
  funext j
  refine GlobalTheory.SelfDualFinite.eq_zero_of_trace R h _ fun c => ?_
  have := hx (Pi.single j c)
  rw [traceBilin_apply, Finset.sum_eq_single j] at this
  · rwa [Pi.single_eq_same, mul_comm] at this
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form

theorem exists_selfDual_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), (∃ r, psiV F ψ v r ≠ 1) → ∀ (ι : Type) [Fintype ι], ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))) := by
  intro F E _ _ _ _ _ σ h ψ hψ v hne ι _
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  exact (GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne _ (traceBilin (Fv F v) ι)
    (traceBilin_symm _ ι) (eq_zero_of_traceBilin _ ι h)).exists

end GlobalTheory.TraceSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem genusMatch_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), GenusMatch D F := by
  intro D F X u wt ιA hW hA
  obtain ⟨hT, -, -, hdeg, -, hH, hdet⟩ := record_facts D u
  have hM := (GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator D X u wt hW).1
  have hL := stepLevel_tLat (S := (F u).cls0.lev)
  have hE := (_root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hA).1
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.St.G.tlat_one_genus D.host.F D.host.E D.sp.cm (D.R.N 0) _ hH hdet (D.mem u).A.T D.R.f
    (F u).cls0.lev.Lb (Mq wt) (D.mem u).A.T_prime hT hdeg hL hM
  exact ⟨h, fun x => (hh x).trans (hE x)⟩

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HtDelta
section
namespace GlobalTheory.DiffModProd

theorem htDelta : Formalism.L2.SG.NGHTie.HTDelta := by
  unfold Formalism.L2.SG.NGHTie.HTDelta
  exact finprod_modK_localGen

end GlobalTheory.DiffModProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTopStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  first | exact @GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top | exact GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top | (intros; apply GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPower
section
namespace GlobalTheory.HTThetaLeaf

theorem main : Formalism.L2.SG.NGHTie.HTTheta := by
  unfold Formalism.L2.SG.NGHTie.HTTheta
  exact GlobalTheory.TypeUnifProd.main

end GlobalTheory.HTThetaLeaf
end

