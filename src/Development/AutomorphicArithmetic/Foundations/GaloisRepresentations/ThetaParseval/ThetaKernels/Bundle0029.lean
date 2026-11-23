module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFormK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
theorem exists_form_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ e, IsSplitIdemF σ e →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f₀ ≠ 0 →
      ∃ ℓ : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WOF F E nS (nT + nT), (∀ i j, cAF σ e * u i j = u i j) →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            ℓ (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
        (∃ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f ∧ ℓ f ≠ 0) ∧
        ∀ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det → ∃ R : ℝ, 0 < R ∧
          ∀ (f f' : WOF F E nS (nT + nT) → ℂ) (k : ℂ),
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f' →
            (∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
              prof σ JS JT ξ₀ B.ψ ν 𝓕 f' y = k * prof σ JS JT ξ₀ B.ψ ν 𝓕 f (M * y)) →
            ℓ f' = (R : ℂ) * k * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  letI : MeasurableSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := borel _
  haveI : BorelSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := GlobalTheory.SplitInvFormF.conjHalf σ e nS nT)).IsAddHaarMeasure
  have hth := _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f.1 y.1 ∂μ
      map_add' := fun f g => by
        rw [← integral_add (_root_.GlobalTheory.SplitLagrF.prof_integrable_k hB hS hT hξ hσξ hν h𝓕 he μ f.2)
          (_root_.GlobalTheory.SplitLagrF.prof_integrable_k hB hS hT hξ hσξ hν h𝓕 he μ g.2)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => _root_.GlobalTheory.SplitLagrF.prof_add_k hB hν h𝓕 f.2 g.2 y.1)
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_smul ν 𝓕 c f.1 y.1) }
  obtain ⟨ℓ, hℓ0⟩ := LinearMap.exists_extend L
  have hℓ : ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
      ℓ f = ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1 ∂μ :=
    fun f hf => LinearMap.congr_fun hℓ0 ⟨f, hf⟩
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun M hM => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp (σ := σ) (e := e) hu
    rw [hℓ _ (hth _ _ hf), hℓ f hf,
      GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ ha) (mul_mem_conjHalf _ hb),
      ← integral_add_right_eq_self (μ := μ)
        (fun y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1) ⟨b, hb⟩]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ = prof σ JS JT ξ₀ B.ψ ν 𝓕 f (y.1 + b)
    simp only
    rw [_root_.GlobalTheory.SplitLagrF.prof_heis_dC_k hB hS hT hξ hσξ hν h𝓕 (hth _ _ hf), GlobalTheory.SplitVacF.commF_half he y.2 (add_mem ha ha), one_mul,
      prof_heis_aC ν 𝓕 he f y.2 hb]
  · by_contra hall
    push Not at hall
    exact hne (_root_.GlobalTheory.SplitLagrF.lagrInt_eq_zero_k hB hS hT hξ hσξ hν h𝓕 he μ hf₀ fun u => by
      rw [← hℓ _ (hth u _ hf₀)]; exact hall _ (hth u _ hf₀))
  · obtain ⟨r, hr, hm⟩ := integral_mul_left e μ M hM
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← hm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)
end GlobalTheory.SplitLagrF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNhdsOneWeilFixesPureTensor
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
section Left
open PositivityTheory.ThKEst PositivityTheory.ThKEst.levelStructure PositivityTheory.ThKEst.LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
private theorem schr_left_pk {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), levelStructure.IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (mat u * z)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun p : UA σ X.J × Ten F E n d => M.co.e ((mat p.1 - 1) * p.2) :=
    he.comp ((((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_mul
      continuous_snd)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ X.J))
    (P := fun u c => M.co.e ((mat u - 1) * c) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1) = mat u - 1 := hu
  have e : mat u * z = z + (mat u - 1) * c := by
    have e1 : (mat u - 1) * c = (mat u - 1) * z := by
      rw [← hu', Matrix.smul_mul, ← Matrix.mul_smul, ← hz, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  rw [e, map_add (f := _)]
  exact h1 c hc (by rw [← map_smul, ← Matrix.smul_mul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f
end Left
theorem UpperTheory.exists_nhds_one_weil_fixes_pure_tensor :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = pureA F f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := PositivityTheory.ThKEst.ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := _root_.PositivityTheory.ThKEst.coefBd_of_k PositivityTheory.ThKEst.coefReal_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := schr_left_pk M hp.base.std hφ hCc
  have := PositivityTheory.ThKEst.LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ X.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin n) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ X.J => ‖om (u, 1) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (PositivityTheory.ThKEst.levelStructure.ev_adm y) _ (mem f₀)).comp (continuous_id.prodMk continuous_const)).div_const _).sub
      continuous_const).norm
  have h3 := PositivityTheory.ThKEst.levelStructure.pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := PositivityTheory.ThKEst.levelStructure.isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (u, 1) (pureA F f φ) x * (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine PositivityTheory.ThKEst.fourierInj_of F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [_root_.PositivityTheory.ThKEst.coefEq_of_k F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), PositivityTheory.ThKEst.ParityOfCoefficients.mat_one_inv,
      Matrix.transpose_one, Matrix.mul_one]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (mat u⁻¹ * z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [← h1 hu _ a', ← Matrix.mul_assoc, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.one_mul]
    have b := hb f f₀ z
    have b' := hb f f₀ (mat u⁻¹ * z)
    rw [PositivityTheory.ThKEst.maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [PositivityTheory.ThKEst.maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (u ^ k, 1) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((u ^ k * u, 1) : UA σ X.J × UA σ W.J) = (u ^ k, 1) * (u, 1) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
end Gen
structure Tools_k : Prop where
  swFull : _root_.GlobalTheory.ThK.Dbl.SWFullX_k
  boxSec : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k
  dbl : _root_.GlobalTheory.ThK.Dbl.DblX_k
  stab2 : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k
  cpt : _root_.GlobalTheory.ThK.Dbl.CptAll_k
  basic : _root_.GlobalTheory.ThK.ThetaBasic_k
  polSch : _root_.GlobalTheory.ThK.Dbl.PolSch_k
  unfold0 : _root_.GlobalTheory.ThK.Dbl.Unfold0_k
  pairEx : _root_.PositivityTheory.ThKG.Tow.PairEx_k
  split : _root_.GlobalTheory.ThK.Dbl.SplitModel_k
  vacFix : _root_.GlobalTheory.ThK.Dbl.VacFix2_k
  acts : _root_.GlobalTheory.ThK.ActsEx_k
  lie1 : GlobalTheory.RealLift.LieFirst
  lie2 : GlobalTheory.RealLift.LieSecond
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end CM
def TLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), _root_.UpperTheory.TP.W.GoodK (cj E) B →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
        GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ), IsLift B χX χW mX mW lam U U'
def HgtFst_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∃ t₀ : ℝ, ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → ∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) μ
def Rallis_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∀ φ, IsFn φ →
      Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ ∧
        (lift M om Φ φ = 0 → ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ = 0)
def Decomp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 → ∀ S : Finset (Pl F),
    (∃ j : gInf σ X × gAt σ X S × gOff σ X S ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1) ∧
    IsCompact (gInf σ X : Set (UA σ X.J)) ∧ IsClosed (gAt σ X S : Set (UA σ X.J)) ∧ IsClosed (gOff σ X S : Set (UA σ X.J)) ∧
    IsCompact {g : UA σ X.J | IntAll g} ∧ IsOpen {g : UA σ X.J | IntAll g} ∧ (∀ g ∈ gInf σ X, IntAll g) ∧
    (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧
      ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) ∧
    ∀ g : UA σ X.J, {v | ¬ IntAt v g}.Finite
def BumpAny_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 2 * n ≤ d →
    ∀ v, ∀ N ∈ 𝓝 (1 : UA σ X.J), ∃ H φ, IsBump B M om v H φ ∧ (H : Set (UA σ X.J)) ⊆ N
def Datum_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ S : Finset (Pl F), UnrOff χW (S : Set (Pl F)) →
    ∀ (H : Pl F → Subgroup (UA σ X.J)) φ, IsFin M φ → (∀ v ∈ S, IsBump B M om v (H v) (φ v)) → (∀ v ∉ S, φ v = M.vac v) →
    ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → coef om ν (pure f₀ φ) 1 ≠ 0 ∧
      ∀ x ∈ gInf σ X, ∀ b ∈ gAt σ X S, ∀ c ∈ gOff σ X S, (b ∉ ⨆ v ∈ S, H v → coef om ν (pure f₀ φ) (x * b * c) = 0) ∧
        ∃ s : ℂ, ‖s‖ = a (e (c, 1)) ^ ((d : ℝ) / 2) ∧ (IntAll c → s = 1) ∧
          ∀ x' ∈ gInf σ X, ∀ b' ∈ ⨆ v ∈ S, H v, coef om ν (pure f₀ φ) (x' * b' * c) = s * coef om ν (pure f₀ φ) x'
def Tail_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ (μ : Measure (UA σ X.J)) (t : ℝ), μ.IsHaarMeasure → Integrable (fun g => a (e (g, 1)) ^ t) μ → ∀ S₀ : Finset (Pl F),
      ∃ S : Finset (Pl F), S₀ ⊆ S ∧ ∀ μC : Measure (gOff σ X S), μC.IsHaarMeasure →
        ∫⁻ c in {c : gOff σ X S | ¬ IntAll c.1}, ENNReal.ofReal (a (e (c.1, 1)) ^ t) ∂μC < μC {c | IntAll c.1}
def RealPair_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → n ≤ d →
    ∀ (δ : E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ), X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) → HasExp B.emb χX mX →
    HasExp B.emb χW mW → ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
      GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
      (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∃ φ ∈ U, φ ≠ 0 ∧ SameType om e U f₀ φ ∧
        ∀ w, ∃ lam', IsLiftWt (lam w) (mX w) (mW w) lam' ∧ HasType B M om e' f₀ w lam'
def SchurStep_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀, f₀ ≠ 0 → ∀ φ, φ ≠ 0 → SameType om e U f₀ φ →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ φf, IsFin M φf → ∀ μA : Measure (gInf (cj E) X), μA.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ c ∈ gOff (cj E) X ∅, ∫ x, coef om ν (pure f₀ φf) x.1 * star (mc M (φ ∘ e.symm) (x.1 * c)) ∂μA =
      κ * coef om ν (pure f₀ φf) 1 * star (mc M (φ ∘ e.symm) c)
def NonVan_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → 2 * n ≤ d →
    ∀ K a (ε : UA (cj E) X.J × UA (cj E) X.J →* G2 (cj E) X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (ε (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (ε (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → ∀ φ, φ ≠ 0 →
      SameType om e U f₀ φ → ∃ φf, IsFin M φf ∧ lift M om (pure f₀ φf) (φ ∘ e.symm) ≠ 0
def LiftAut_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∃ Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ),
      ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
        ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
          Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ)
def ReadLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ))
      (pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → GlobalTheory.UnitaryBC.IsAutRepU U' →
      (∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f)) →
      ∀ f₀ ∈ M.Pol B.ψ B.emb, ∀ φ ∈ U, ∀ φf, IsFin M φf → pr (lift M om (pure f₀ φf) (φ ∘ e.symm) ∘ e') ≠ 0 →
      (∀ w lam', HasType B M om e' f₀ w lam' → GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam') ∧
      ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ', CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' →
        LocPair t χX χW τ τ'
theorem tLift_of_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) (h1 : BrEx) (h2 : _root_.UpperTheory.TP.HgtFst_k) (h3 : _root_.UpperTheory.TP.RealPair_k) (h4 : _root_.UpperTheory.TP.NonVan_k) (h5 : _root_.UpperTheory.TP.LiftAut_k) (h6 : ProjEx)
    (h7 : _root_.UpperTheory.TP.ReadLift_k) : _root_.UpperTheory.TP.TLift_k := by
  intro E _ _ _ B hB n hn X hXJ hX
  obtain ⟨⟨K, a, hK, ha, -⟩, ε, -, hε⟩ := hH _ E (cj E) B n X n 0 hB (Or.inl hX)
  obtain ⟨t₀, ht₀⟩ := h2 _ E (cj E) B n X hB hX K a ε hK ha hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * t₀)
  refine ⟨max N (2 * n), fun d hd W δ hWJ hW χX χW mX mW hχX hχW rX rW eX eW U lam hU hwt hdom => ?_⟩
  have hd1 : 2 * n ≤ d := (le_max_right _ _).trans hd
  have hd2 : t₀ < (d : ℝ) / 2 := by
    have : (N : ℝ) ≤ d := by exact_mod_cast (le_max_left _ _).trans hd
    linarith
  have hδ : δ ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    obtain ⟨-, A, hA⟩ := hW.sig w
    have := congrFun (congrFun hA (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    simp [hWJ] at this
  obtain ⟨⟨M, hM⟩, hom⟩ := T.pairEx _ E (cj E) B hB n d X W n 0 d 0 hX hW
  obtain ⟨om, hP⟩ := hom χX χW hχX hχW rX rW M hM
  obtain ⟨e, he⟩ := h1 E n X 1 one_ne_zero (by rw [hXJ, one_smul])
  obtain ⟨e', he'⟩ := h1 E d W δ hδ hWJ
  obtain ⟨f₀, hf₀, hf0, φ, hφ, hφ0, hS, hT⟩ := h3 E B n d X W M χX χW om hP hn e e' he he' (by omega) δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨φf, hfin, hne⟩ := h4 E B n d X W M χX χW om hP hn e e' he he' hd1 K a ε hK ha hε t₀ (ht₀ M.μ hM.haar) hd2 U hU f₀ hf₀ hf0 φ hφ0 hS
  obtain ⟨Θ, hΘ⟩ := h5 E B n d X W M χX χW om hP hn e e' he he'
  have hmem : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨q1, q2, -⟩ := hΘ ⟨_, hmem⟩ φ (hU.aut φ hφ)
  have hne' : Θ ⟨_, hmem⟩ φ ≠ 0 := by
    rw [q1]
    intro h0
    apply hne
    funext h
    have := congrFun h0 (e'.symm h)
    simpa using this
  obtain ⟨U', pr, hU', hpr, hp⟩ := h6 E d _ q2 hne'
  rw [q1] at hpr
  obtain ⟨r1, r2⟩ := h7 E B n d X W M χX χW om hP hn e e' he he' U U' pr hU hU' hp f₀ hf₀ φ hφ φf hfin hpr
  exact ⟨U', hU', fun w => (hT w).imp fun lam' h => ⟨r1 w lam' h.2, h.1⟩, r2⟩
end UpperTheory.TP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.JHomValK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def jHom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))
theorem jHom_val_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]
theorem jHom_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LintegralEnormSqLatRepApplyEq
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_enorm_sq_latRep_apply_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  first | exact @_root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | exact _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | (intros; apply _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMCut
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def BigT_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
  (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2)),
  IsAdapted d.bs d.A d.Y d.b dd0 →
  (∀ x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E, ∃ y z : Fin d.m × Fin d.n × Fin 2 → F,
      dd0.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∃ (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ))
    (S0' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ), C ≠ 0 ∧
    GlobalTheory.TowU.IsOp2 d.B.ψ (fun w => dd0.e (d.dd.e.symm w)) S0 S0' ∧ ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (crdB d.bs X)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

