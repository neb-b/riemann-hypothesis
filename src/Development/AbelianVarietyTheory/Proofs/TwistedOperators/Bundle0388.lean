module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.ChainFr GlobalTheory.Chain.IoLift GlobalTheory.Chain.IoLift.FockOrbit GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec maxCpt)
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembers

theorem signBlockDeterminant_one {n : ℕ} (ε : Fin n → Bool) (e : Bool) : signBlockDeterminant ε e 1 = 1 := by
  unfold signBlockDeterminant
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : {a // ε a = e} → Fin n) Subtype.val = 1 from by
    ext x y; simp [Matrix.one_apply, Subtype.ext_iff]]
  exact Matrix.det_one

theorem fr_elt_one {D : D7} {V : HSp D} {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr V) (τ : D.what₂.Tau) :
    A.elt θ τ 1 = 1 := by
  rw [Fr.elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)), GlobalTheory.PointAtPlaceHom.atTau_one hθ]

theorem frame_fock_orbit : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (A : GlobalTheory.ChainFr.Fr V) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → GlobalTheory.ChainFr.CompactFockF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), GlobalTheory.Chain.IoLift.IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (GlobalTheory.ChainFr.ptF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') f φ) = ∑ i, c i k • GlobalTheory.ChainFr.ptF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') f (φs i) := by
  intro D V W S' A M' θ ψ ω f τ aS aT hθ hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) :=
    pureTensorO ψ θ V W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f
  have hp : ptF ψ θ A (Fr.ofModel M') f = pt := rfl
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k =>
    signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (A.ε τ) (M'.ε τ) 1 (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [fr_elt_one hθ, signBlockDeterminant_one, signBlockDeterminant_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), hp, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := (hz true).mul (hz false)
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      simp only [ρ, s, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, e,
        subst_one_mul τ (A.ε τ) (M'.ε τ) a.2 b.2, signBlockDeterminant_mul_maximalCompact _ a.2 b.2, mul_zpow]
      congr 1
      ring)
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  refine ⟨n, φs, c, h1, fun k => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hp, key, h2, map_sum]
  simp only [map_smul]


set_option maxHeartbeats 1000000 in
theorem lowVanishFock (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules)
    (h3 : GlobalTheory.Published.CuspRapidDecay) : ∀ D : D7, LowVanishFock D := by
  classical
  intro D
  obtain ⟨X, hX, -, h5, -, -, -, hAR⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta h1 h2
  have hTB := (_root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all h1 h2 D).2
  intro k i V' W M' θ ψ hθ hP hi hs ω' hω ν 𝓕 hν h𝓕 J χ F hF v A f₀ hf P
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  by_cases f0 : f₀ = 0
  · subst f0
    funext g
    simp [Lift.liftInt, thetaKO, ptF_zero]

  have tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ),
      kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a' := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, -, e2⟩ := hP τ
    obtain ⟨-, -, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types _ al be ga de hd.1
    have ht := hd.1.1
    obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W _ M' τ (al.length + de.length + D.R.t) (ga.length + be.length) _ _
      (expS D k τ) ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, congrArg dualPar e2⟩
    obtain ⟨U', hU'⟩ := hU' e' he'
    obtain ⟨hsm, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'
    exact ⟨a', hsm, ha'⟩
  choose a' hsm ha' using tgt
  have h' : KSm M' := hsm
  have hMF : IsMultMap θ M' J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)
  have hM : ∀ F' : MultT θ M' J χ, IsMultMap θ M' J χ (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ))) :=
    fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)
  let pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ) :=
    pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀
  have hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt := rfl
  have hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ
  have L := _root_.GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hint : ∀ F' : MultT θ M' J χ, ∀ φ x g, IntegrableOn
      (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν := fun F' φ x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' J χ) hint
  let G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ) :=
    B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' J χ))
  have hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x) := fun φ x => hB φ x ⟨F, hF⟩
  have hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ w)) := fun w => ⟨hMF.aut w, hMF.cusp w⟩

  have hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z)
      (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ) z) 0 :=
    fun τ Y hY φ z => (_root_.GlobalTheory.LieScalar.lieFockAll D V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (expS D k τ) (expT D k τ) hθ hW
      (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z
  have hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) →
      G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ)
        (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0 := by
    intro τ Y hY φ w u hu
    have e1 := GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu
    rw [Function.update_eq_self] at e1
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) =
        pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ) :=
      funext fun z => (hT τ Y hY φ z).deriv
    funext g
    have := L.derT_add (hpt φ) (hcl w) τ hY g
    rw [e2, add_comm] at this
    rw [Pi.add_apply, hG, hG]
    exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this

  have hav := mem_span_of_average G h' fun τ φ w => by
    obtain ⟨n, φs, c, hc, hφ⟩ := frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (expS D k τ) (expT D k τ) hθ
      (_root_.GlobalTheory.CompactFockAction.compactFockAll D V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩
    funext g
    simp only [hG, Finset.sum_apply]
    exact GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _
      hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g
      (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g

  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨al, be, ga, de, hd, hbig, e1, e2⟩ := hP τ₀
  obtain ⟨p', q', hp', hq', hsig⟩ := hs τ₀
  have hnd : ((al ++ be) ++ (ga ++ de)).Nodup := by simpa only [List.append_assoc] using hd.1.2.2.2.2.2.2.1
  have hcard := signCard_signed (al ++ be) (ga ++ de) (expT D k τ₀) hnd.of_append_left hnd.of_append_right
  have e1' : parB (Ptw D) k τ₀ = dualPar (signed (al ++ be) (ga ++ de) (expT D k τ₀)) := congrArg dualPar e1
  rw [e1', GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, List.length_append] at hp'
  rw [e1', GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, List.length_append] at hq'
  obtain rfl : p' = al.length + be.length - i := by omega
  obtain rfl : q' = ga.length + de.length - i := by omega
  obtain ⟨e, he⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig
  obtain ⟨-, -, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types _ al be ga de hd.1
  have ht := hd.1.1
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W _ M' τ₀ (al.length + de.length + D.R.t) (ga.length + be.length) _ _
    (expS D k τ₀) ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, congrArg dualPar e2⟩
  obtain ⟨U', hU'⟩ := hU' e' he'
  have kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0 := by
    have hz := span_multi (G.compl₂ (inclK h')) fun p y => by
      funext g
      let B := multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))
      let b := LinearMap.mk₂ ℂ (fun x z => B (Function.update p τ₀ x) (Function.update y τ₀ z))
        (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      have hb0 := pairing_eq_zero X h5 hAR D.R.t al be ga de hd hbig i hi (by omega) (by omega) D V' W _ M' τ₀
        (A.ε τ₀) e e' m' (expS D k τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by
          dsimp only [b, LinearMap.mk₂_apply]
          simp only [B, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
            LinearMap.proj_apply]
          have eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q +
              ((expS D k τ₀ : ℂ) * Y.trace) • Q)) =
              fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) +
                ((expS D k τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q) := by
            rw [((_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]
            simp only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul, RingHom.id_apply]
          have eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀
              (a' τ₀ Y (Function.update y τ₀ z τ₀)) := by
            rw [Function.update_idem, Function.update_self]
          rw [eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]
          refine congrFun (hBt τ₀ Y hY _ _ _ ?_) g
          exact ((ha' τ₀).der Y hY _).deriv.symm)
      have := LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)
      dsimp only [b, LinearMap.mk₂_apply] at this
      simpa [B, multi_apply, Function.update_eq_self] using this
    exact fun φ y => LinearMap.congr_fun₂ hz φ y
  have h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)
  rw [Submodule.mem_bot, hG] at h0
  rw [hp]
  exact h0

end GlobalTheory.LowerMembers

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverse
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitPlaceBigCell

theorem splitPlace_bigCell_exists_admissible_inverse : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro hLoc F E _ _ _ _ _ σ d W v hskew h2 π₁ π₂ b₁ b₂ hd hSx g hg
  obtain ⟨hc₁, hc₂, ha₁, ha₂, hinj, hsurj, hlat⟩ := hd
  obtain ⟨S, hSdet, hS⟩ := hSx
  obtain ⟨k11, k12, k21, k22, k11', k12', k21', k22'⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_blocks_keep_lattice σ W v g hg
  have I := fun A hA => GlobalTheory.T.integral_localBasisConjugates_of_keepsLatticeAtPlace W v π₁ π₂ b₁ b₂ hlat hsurj A hA
  have hinv : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := g.1.inv_mul
  obtain ⟨G₁, hG₁, hG₁u⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₁ b₁ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).1 (I _ k12).1 (I _ k21).1 (I _ k22).1 (I _ k11').1 (I _ k12').1 (I _ k21').1 (I _ k22').1
  obtain ⟨G₂, hG₂, -⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₂ b₂ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).2 (I _ k12).2 (I _ k21).2 (I _ k22).2 (I _ k11').2 (I _ k12').2 (I _ k21').2 (I _ k22').2
  have hU := GlobalTheory.T.unitary_at_splitPlace_localBases σ W v π₁ π₂ b₁ b₂ hc₁ g
  have e : ∀ {m n o : Type} [Fintype n] (A : Matrix m n (v.adicCompletionIntegers F))
      (B : Matrix n o (v.adicCompletionIntegers F)),
      (A * B).map (fun x => (x : Fv F v)) = A.map (fun x => (x : Fv F v)) * B.map (fun x => (x : Fv F v)) :=
    fun A B => Matrix.map_mul (f := (v.adicCompletionIntegers F).subtype)
  have hUO : G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) := by
    apply Matrix.map_injective (f := fun x : v.adicCompletionIntegers F => (x : Fv F v)) Subtype.coe_injective
    beta_reduce
    have en : (-S).map (fun x => (x : Fv F v)) = -(S.map (fun x => (x : Fv F v))) := by ext i j; rfl
    have ez : (0 : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)).map (fun x => (x : Fv F v)) = 0 := by
      ext i j; rfl
    rw [e, e, Matrix.transpose_map, Matrix.fromBlocks_map, en, ez, hG₁, hG₂, hS]
    exact hU
  obtain ⟨X₁, X₂, hX, hP₁, hP₂⟩ := hLoc h2 S hSdet G₁ G₂ hG₁u hUO
  obtain ⟨Y, hYat, hY₁, hY₂, hYadm⟩ :=
    GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair σ W v hskew π₁ π₂ b₁ b₂ hc₁ hc₂ hinj hsurj S hS X₁ X₂ hX
  obtain ⟨N₁, hN₁, hN₁i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₁ b₁ ha₁ (GlobalTheory.DblVac.matD g) G₁ hG₁ X₁ hP₁ Y hY₁
  obtain ⟨N₂, hN₂, hN₂i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₂ b₂ ha₂ (GlobalTheory.DblVac.matD g) G₂ hG₂ X₂ hP₂ Y hY₂
  have hK := GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace v (GlobalTheory.DblVac.matD g) Y hg.1 hYat
  obtain ⟨M, hMK, hM₁, hM₂⟩ := GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses v π₁ π₂ hinj hsurj _ hK N₁ N₂ hN₁ hN₂
  have hYi : ∀ (b : GL (Fin d) (Fv F v)) (X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)),
      ∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F := by
    intro b X i j
    have : ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v)) = X.map (fun x => (x : Fv F v)) := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [this]; exact (X i j).2
  refine ⟨Y, hYat, GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat Y ?_ ?_, hYadm, M, hMK,
    GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat M ?_ ?_⟩
  · rw [hY₁]; exact hYi b₁ X₁
  · rw [hY₂]; exact hYi b₂ X₂
  · rw [hM₁]; exact hN₁i
  · rw [hM₂]; exact hN₂i

end GlobalTheory.SplitPlaceBigCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormFockMatrixEqNegSumImRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockOmega

variable {D : D7}

open GlobalTheory.FockTransport

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

theorem jm_eq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε = Matrix.diagonal fun a => ((sg (ε a) : ℝ) : ℂ) := by
  rw [Formalism.REAL.Jm]
  congr 1
  funext a
  cases ε a <;> simp [sg]

theorem gramAt_inv {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) :
    (gramAt D V τ)⁻¹ = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ := by
  have hP := det_fr_unit A τ
  rw [← A.fr_gram τ]
  apply Matrix.inv_eq_left_inv
  have h1 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hP, Matrix.conjTranspose_one]
  calc (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
      = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [jm_mul_self, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem hAt_frame {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X Y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ ((B.fr τ)⁻¹ * X * A.fr τ) ((B.fr τ)⁻¹ * Y * A.fr τ) =
      (Formalism.REAL.Jm (A.ε τ) * (Yᴴ * (Formalism.REAL.Jm (B.ε τ) * X))).trace := by
  have hA := det_fr_unit A τ
  have hB := det_fr_unit B τ
  have cA : ∀ M : Matrix (Fin S.rank) (Fin S.rank) ℂ, ((A.fr τ)⁻¹)ᴴ * ((A.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have cB : ∀ M : Matrix (Fin T.rank) (Fin S.rank) ℂ, ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hB, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [GlobalTheory.VacUnique.hAt, gramAt_inv A τ, ← B.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, cA, cB, Matrix.mul_nonsing_inv_cancel_left _ _ hB]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA]

theorem trace_jm {m n : ℕ} (a : Fin n → Bool) (b : Fin m → Bool) (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (Formalism.REAL.Jm a * (Yᴴ * (Formalism.REAL.Jm b * X))).trace =
      ∑ i, ∑ j, ((sg (a j) : ℝ) : ℂ) * (conj (Y i j) * (((sg (b i) : ℝ) : ℂ) * X i j)) := by
  rw [Finset.sum_comm]
  simp only [jm_eq, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum, Matrix.conjTranspose_apply, RCLike.star_def]

theorem term_re (b a : Bool) (ξ z y : ℂ) (hξ : ξ.re = 0) :
    2 * (ξ * (((sg a : ℝ) : ℂ) * (conj (cf b a y) * (((sg b : ℝ) : ℂ) * cf b a z)))).re =
      -(2 * (ξ.im * (z * conj y).im)) := by
  cases a <;> cases b <;> simp [cf, sg, Complex.mul_re, Complex.mul_im, hξ] <;> ring_nf <;> simp

theorem omO_fockMat (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (Z Y : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S)
      (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) =
      -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  refine (GlobalTheory.VacUnique.omO_apply S T _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show GlobalTheory.VacUnique.omAt S T τ (fockMat A B τ (Z τ)) (fockMat A B τ (Y τ)) = _
  rw [GlobalTheory.VacUnique.omAt, fockMat_eq, fockMat_eq, hAt_frame, trace_jm, Formalism.IndefR.Fock.CCR.norm_embedding_hostFormConstant_eq]
  simp only [Finset.mul_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  exact term_re _ _ _ _ _ (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ)

end GlobalTheory.FockOmega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.EvalAt

theorem theta_eval : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t h Λ hh hht hΛf hhm g L hg hgt hLf hgm a ha Q
  have hΛ0 : C.X.Λ.FG := C.X.Λ_fg
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := _root_.GlobalTheory.Ker.MovLev.mov_mem_lattices D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ hΛ0 hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  have hLl : L ∈ Lv.lats := (hL Lv g L hLf hgm).2.1 hgt
  have hsb : ∀ L ∈ Lv.lats, ∀ Λ ∈ Vset D.host.E S.rank M, SW.IsSB (Lv.phi C.bas hn v₀ L Λ) :=
    fun L hL Λ hΛ => (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      L hL Λ hΛ).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hφ0 := hsb _ hΛl _ hstd
  have hφ := hsb L hLl Λ (hV M h Λ hM hht hΛf hhm)
  have hJ := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hth : ∀ B', C.IsB B' → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B') φ) :=
    fun B' hB' φ hφ => (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hJ B' hB').2.1 φ hφ).1.1
  have hmv := (hJ B hB).2.2.2.2.2
  have hBa : C.IsB (C.mvB a B) := (hmv a).1
  have hgB : C.mvB g B = B := (hmv g).2.2.1 hg
  have hcomm : a * g = g * a := (((_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.2.2.1 a ha).2.2 g hg
  have p1 : ((h, g * a) : GA D S × GA D T) = (1, a) * (h, g) := by
    rw [Prod.mk_mul_mk, one_mul, hcomm]
  obtain ⟨-, -, e3⟩ := hep h Λ g L hh hht hΛf hhm hg hgt hLf hgm
  rw [(_root_.GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ0) Q).2.2.2.2.1, p1, map_mul, Module.End.mul_apply,
    map_smul, GlobalTheory.Ker.Red.om_fvec C om hW h hh g _ (hth B hB _ hφ0) B hB Q, hgB, e3,
    (_root_.GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ) Q).2.2.2.2.1, map_smul, map_smul,
    GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) a _ (hth B hB _ hφ) B hB Q, hz a ha _ hφ,
    (_root_.GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C _ hBa (fun _ => 1) _ (hth _ hBa _ hφ) Q).2.2.2.2.1]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [((_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).2 _ hBa _ hφ).2 Q]
  ring

end GlobalTheory.AdSpan.EvalAt
end

