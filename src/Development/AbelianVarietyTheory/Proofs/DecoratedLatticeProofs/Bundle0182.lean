module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowCont

theorem reg_star {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : X.B.I.GA) (φ : L2X X) :
    X.B.R g (star φ) = star (X.B.R g φ) := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  obtain ⟨-, hr, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf
  have hP : ∀ a : X.B.I.GA, Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) a := fun a => ⟨measurable_mul_const a, hr a⟩
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map (Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (hP g) (hP g⁻¹)
  have e1 := X.B.R_spec g (star φ)
  have e2 := X.B.R_spec g φ
  have e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)) =
      star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g))) := by
    refine ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_
    rw [h2]
    filter_upwards [Lp.coeFn_star φ] with y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R g φ)] with x a1 a2 a3 a4
  rw [a1, a4, Pi.star_apply, a2]
  exact a3

theorem iotaX_rat_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
    intro I I' e x
    subst e; rfl
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D g).trans (k h.symm _)

theorem exists_conj_multilinear {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.Y 0) S) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (Φ : X.B.Hs →L[ℂ] L2X X) :
    ∃ Ψ : ContinuousMultilinearMap ℂ M.H (L2X X), ∀ y,
      Ψ y = star (Φ (X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm fun τ => c τ (y τ)))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCu : ∀ y τ a, C (Function.update y τ a) = Function.update (C y) (X.pl.symm τ) (c τ a) := by
    intro y τ a
    rw [← GlobalTheory.ConjRowMult.piCongrLeft_update]
    refine congrArg (Equiv.piCongrLeft X.B.H X.pl.symm) (funext fun τ' => ?_)
    exact Function.apply_update (fun i (s : M.H i) => c i s) y τ a τ'
  have hCc : Continuous C := by
    refine continuous_pi fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (c τ).continuous.comp (continuous_apply τ)
  let Ψ₀ : MultilinearMap (RingHom.id ℂ) M.H (L2X X) := MultilinearMap.mk' (fun y => conjL (muX X) (Φ (m (C y))))
    (fun y τ a b => by rw [hCu, hCu, hCu, map_add (f := _), m.map_update_add, map_add (f := _), map_add (f := _)])
    (fun y τ a b => by
      rw [hCu, hCu, LinearIsometryEquiv.map_smulₛₗ, m.map_update_smul, map_smul, LinearIsometryEquiv.map_smulₛₗ,
        starRingEnd_self_apply]
      rfl)
  refine ⟨⟨Ψ₀, (conjL (muX X)).continuous.comp (Φ.continuous.comp (m.cont.comp hCc))⟩, fun y => ?_⟩
  show star (Φ (m (C y))) = _
  rw [hm]


set_option maxHeartbeats 1000000 in
theorem conjMap_cont : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ hrep τ₀ v₀ x₀
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨Ψ, hΨ⟩ := exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, reg_star]
      congr 1
      refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
      obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        exact hc _ a ha _
      · rw [Function.update_of_ne e]
        have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
        rw [q]
        have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
        show _ = X.B.σ (X.pl.symm τ') 1 _
        rw [this]
        rfl)
    (fun y k hk hk' => by
      rw [h3, hΨ, reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((iotaX_rat_iff X h _).2 ?_) _
        have : iotaX X h (T.symm γ) = γ := T.apply_symm_apply γ
        rwa [this]
      · filter_upwards [h4 _ (hN1 u)] with z hz
        rw [← hz, T.apply_symm_apply]
    have r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))
        (fun z => star (N u (T.symm z))) := by
      refine ⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩
      have r3 := r1.2.2
      rw [hΨ] at r3
      filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2
      rw [← a1]
      exact (star_star _).symm.trans (congrArg star a2.symm)
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]
    exact congrArg (N u) (T.symm_apply_apply _)
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hN3 τ₀ v₀ (x₀ * t⁻¹)
  exact ⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩

end GlobalTheory.ConjRowCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.SeeHH

theorem inner_antiunitary_swap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U x, U y⟫_ℂ = ⟪y, x⟫_ℂ := by
  have hI : ∀ z : E, U (Complex.I • z) = (-Complex.I) • U z := by
    intro z; rw [map_smulₛₗ]; simp
  have h1 : ‖U x + U y‖ = ‖y + x‖ := by rw [← map_add (f := _), U.norm_map, add_comm]
  have h2 : ‖U x - U y‖ = ‖y - x‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  have h3 : ‖U x - Complex.I • U y‖ = ‖y - Complex.I • x‖ := by
    have e1 : U x - Complex.I • U y = U (x + Complex.I • y) := by
      rw [map_add (f := _), hI, neg_smul, sub_eq_add_neg]
    have e2 : y - Complex.I • x = (-Complex.I) • (x + Complex.I • y) := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  have h4 : ‖U x + Complex.I • U y‖ = ‖y + Complex.I • x‖ := by
    have e1 : U x + Complex.I • U y = U (x - Complex.I • y) := by
      rw [map_sub, hI, neg_smul, sub_neg_eq_add]
    have e2 : y + Complex.I • x = Complex.I • (x - Complex.I • y) := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  rw [inner_eq_sum_norm_sq_div_four (U x) (U y), inner_eq_sum_norm_sq_div_four y x]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem star_toLp_eq {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hm : MemLp f 2 (muX X))
    (hs : MemLp (fun x => star (f x)) 2 (muX X)) :
    star (hm.toLp f) = hs.toLp (fun x => star (f x)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hs.coeFn_toLp] with x a1 a2 a3
  rw [a1, a3, Pi.star_apply, a2]

theorem re_fix_of_row {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hf : RowFun X f) (hm : MemLp f 2 (muX X)) :
    X.B.Re (star (hm.toLp f)) = star (hm.toLp f) := by
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
  rw [star_toLp_eq X hm hs]
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
  have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
  refine Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) ?_ ?_ hs ?_
  · exact (continuous_star.comp hf.cont).measurable
  · intro γ hγ y
    rw [hf.left γ hγ y]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfun : (fun g => X.B.e g * star (f (y * (1, g)))) =
        X.K2.indicator (fun _ => star (f y) / ((X.B.μf X.K2).toReal : ℂ)) := by
      funext g
      rw [X.e_eq g]
      by_cases hg : g ∈ X.K2
      · have hg' : g ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_pos hg', Set.indicator_of_mem hg, hf.right g hg y]
        have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
        have hc : star (X.chi2 g) * X.chi2 g = 1 := by
          rw [← starRingEnd_apply, Complex.conj_mul', hn]; simp
        have e2 : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd g = X.chi2 g := rfl
        have ev : X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw) = X.B.μf X.K2 := rfl
        rw [e2, ev, star_mul', star_star, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (star (f y) * (((X.B.μf X.K2).toReal : ℂ))⁻¹) * hc
      · have hg' : g ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
    rw [hfun, integral_indicator hKM, setIntegral_const]
    simp only [Measure.real]
    rw [Complex.real_smul]
    have hvc : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
    rw [mul_comm, div_mul_cancel₀ _ hvc]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem real_shift {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (t : GA D (D.sp.Y 0)) (ht : t ∈ GfC (D.sp.Y 0)) (hR : RealSplit X h θ) (v₀ : M.Vec) (g : X.B.I.Ginf) :
    ∃ a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ,
      (∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) ∧
      (∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ)) ∧
      ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) ∧
        ∀ U ∈ Mult θ M J χ, ∀ x, U v₀ ((iotaX X h).symm (x * (g, 1)) * t) = U w ((iotaX X h).symm x * t) := by
  classical
  choose a ha hb using fun τ => hR.2.2.2 τ (g (X.pl.symm τ))
  have hsm : ∀ τ, M.rep τ (a τ) (v₀ τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D (D.sp.Y 0) S M τ (a τ) (ha τ) _ (v₀ τ).2
  let gs : Finset D.what₂.Tau → X.B.I.GA := fun s => ((fun v => if X.pl v ∈ s then g v else 1), 1)
  let ws : Finset D.what₂.Tau → M.Vec := fun s τ => if τ ∈ s then ⟨_, hsm τ⟩ else v₀ τ
  have key : ∀ s : Finset D.what₂.Tau, ∀ U ∈ Mult θ M J χ, ∀ x,
      U v₀ ((iotaX X h).symm (x * gs s) * t) = U (ws s) ((iotaX X h).symm x * t) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro U _ x
      have e1 : gs ∅ = 1 := Prod.ext (funext fun v => by simp [gs]) rfl
      have e2 : ws ∅ = v₀ := funext fun τ => by simp [ws]
      rw [e1, e2, mul_one]
    | insert τ s hτ ih =>
      intro U hU x
      obtain ⟨he2, hoth, -⟩ := hR.2.2.1 τ (a τ) (ha τ)
      have hws : ws s τ = v₀ τ := by simp [ws, hτ]
      have hupd : ws (insert τ s) = Function.update (ws s) τ ⟨_, hsm τ⟩ := by
        funext σ
        by_cases hσ : σ = τ
        · subst hσ; simp [ws]
        · simp [ws, hσ, Function.update_of_ne hσ]
      have hE := Formalism.IndefR.Eqv.KerDiag.mult_equiv θ M J χ hU τ (ha τ) (ws s) ⟨_, hsm τ⟩
        (by simp only [hws])
      have hmul : iotaX X h (atTau θ (D.sp.Y 0) τ (a τ)) * gs s = gs (insert τ s) := by
        refine Prod.ext (funext fun v => ?_) ?_
        · simp only [gs, Prod.fst_mul, Pi.mul_apply]
          by_cases hv : v = X.pl.symm τ
          · subst hv
            have hm : X.pl (X.pl.symm τ) ∈ insert τ s := by simp
            have hn : X.pl (X.pl.symm τ) ∉ s := by simpa using hτ
            rw [if_pos hm, if_neg hn, hb τ, mul_one]
          · have hpv : X.pl v ≠ τ := fun e => hv (by rw [← e, Equiv.symm_apply_apply])
            rw [hoth v hv, one_mul]
            simp [Finset.mem_insert, hpv]
        · simp only [gs, Prod.snd_mul, he2, mul_one]
      rw [hupd, hE]
      show U v₀ ((iotaX X h).symm (x * gs (insert τ s)) * t) =
        U (ws s) ((iotaX X h).symm x * t * atTau θ (D.sp.Y 0) τ (a τ))
      rw [mul_assoc, ← GlobalTheory.HeckeParts.comm_atTau ht τ (a τ), ← mul_assoc]
      have hι : (iotaX X h).symm x * atTau θ (D.sp.Y 0) τ (a τ) =
          (iotaX X h).symm (x * iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))) := by
        rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
      rw [hι, ← ih U hU, mul_assoc, hmul]
  have eu : gs Finset.univ = (g, 1) := Prod.ext (funext fun v => by simp [gs]) rfl
  refine ⟨a, ha, hb, ws Finset.univ, fun τ => by simp [ws], fun U hU x => ?_⟩
  rw [← key Finset.univ U hU x, eu]

theorem coef_eq {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) (hCV : ConjVec X h θ M v₀) (g : X.B.I.Ginf)
    (a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (ha : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (hb : ∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ))
    (w : M.Vec) (hw : ∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) :
    ∏ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = Formalism.L2.SG.ProjRows.mInf X.B.I X.B.σ X.B.w g := by
  obtain ⟨c, hc1, hc2⟩ := hCV
  have e : ∀ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ =
      ⟪X.B.w (X.pl.symm τ), X.B.σ (X.pl.symm τ) (uMat (g (X.pl.symm τ))) (X.B.w (X.pl.symm τ))⟫_ℂ := by
    intro τ
    rw [← inner_antiunitary_swap (c τ) (v₀ τ : M.H τ) (w τ : M.H τ), hw τ,
      hc1 τ (a τ) (ha τ), hb τ, hc2 τ]
  simp_rw [e]
  exact Fintype.prod_equiv X.pl.symm _ _ (fun _ => rfl)

end GlobalTheory.Core.Mi.SeeHH


open GlobalTheory.Core.Mi.SeeHH in
theorem GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  intro hP D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hCV T hT φ hφ
  obtain ⟨-, -, -, -, -, hL⟩ := GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap
  have hR := _root_.GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hIdE
  have hTm : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  obtain ⟨hRow, hMem⟩ := _root_.GlobalTheory.Core.Mi.rowFun_evS hP D X h θ S M J χ t hθ hMat T hT (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) x =
      (PiTensorProduct.lift.symm T) v₀ ((iotaX X h).symm x * t) := fun x => rfl
  generalize PiTensorProduct.lift.symm T = U at hTm hfx
  generalize evS X h t (T (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hφ hfx
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t U hTm U hTm
  have hv₀ : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    obtain ⟨c, -, hc2⟩ := hCV
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : M.H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h θ M J χ t hMat.1 hR v₀ g
    have hco := coef_eq X h θ M v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (U w ((iotaX X h).symm x * t)) * U v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh U hTm x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi.ConjEquiv

open GlobalTheory.ConjRowMult Formalism.L2.SG.EvalTOntoRep

theorem conjMap_equiv : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  intro _hcl D X h θ S M J χ t c _hS hθ _hgap hιE hM hc Φ hΦ hrep τ g hg v w hw
  obtain ⟨hfin, -, hreal, -⟩ := _root_.GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  set a := iotaX X h (atTau θ (D.sp.Y 0) τ g) with ha
  have hvec : vecC X M c (Function.update v τ w) =
      fun p => X.B.σ p (uMat (a.1 p)) (vecC X M c v p) := by
    refine vecC_eq X M c _ _ fun τ' => ?_
    have e1 : vecC X M c v (X.pl.symm τ') = c τ' (v τ' : M.H τ') := by
      unfold vecC
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    rw [e1]
    by_cases ht : τ' = τ
    · subst ht
      rw [Function.update_self, hw, hc τ' g hg]
    · rw [Function.update_of_ne ht, ha1 (X.pl.symm τ') (fun e => ht (X.pl.symm.injective e))]
      have h1 : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds (X.pl.symm τ')).2.2.1.1.1
      have h2 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ'))) = 1 := rfl
      rw [h2, h1]
      rfl
  have htens : X.B.tens (vecC X M c (Function.update v τ w)) = X.B.σs a.1 (X.B.tens (vecC X M c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have haeq : ((a.1, 1) : X.B.I.GA) = a := Prod.ext rfl ha2.symm
  obtain ⟨T, hT, hTΦ⟩ := Submodule.mem_map.1 hΦ
  have hΦx : ∀ x, Φ x = X.B.Re (T x) := fun x => by rw [← hTΦ]; rfl
  have hcomm := (GlobalTheory.IdemProj.re_orth_proj X.B).2.1 a.1
  have key : ∀ x, Φ (X.B.σs a.1 x) = X.B.R a (Φ x) := by
    intro x
    rw [hΦx, hΦx, ← haeq]
    have e1 := congrArg (fun L => L x) (hT a.1)
    simp only [ContinuousLinearMap.comp_apply] at e1
    rw [e1]
    exact congrArg (fun L => L (T x)) hcomm
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' : IsContRep X (Φ (X.B.tens (vecC X M c (Function.update v τ w)))) (fun x => ψ (x * a)) := by
    rw [htens, key]
    exact contRep_reg X hψ a
  funext y
  rw [conjMap_apply, contRepL_spec X hψ']
  show _ = conjMap X M c Φ h t v (y * atTau θ (D.sp.Y 0) τ g)
  rw [conjMap_apply, contRepL_spec X hψ]
  congr 1
  have hti : (iotaX X h t⁻¹).1 = 1 := by rw [map_inv, Prod.fst_inv, (hfin t).1 hM.1, inv_one]
  rw [map_mul, map_mul, map_mul, ← ha, mul_assoc]
  beta_reduce
  rw [mul_assoc]
  congr 2
  exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hti, one_mul, mul_one])
    (by rw [Prod.snd_mul, Prod.snd_mul, ha2, one_mul, mul_one])

end GlobalTheory.Core.Mi.ConjEquiv
end
end

