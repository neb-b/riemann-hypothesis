module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
public import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHold
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

namespace GlobalTheory.Chain.SourceLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isLift_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 := by
  unfold IsLevelLift
  refine ⟨Subgroup.one_mem _, ?_, ?_⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [map_one]
    exact rTup_one

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    levChi V β L 1 = 1 := by
  have h := (levChar D.sp.cm V.gram β L).map_one
  rw [levChar_apply] at h
  have h' : levFn β L 1 = 1 := h
  unfold levChi
  rw [map_one, h', Units.val_one]

theorem isLift_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {κ : GA D V} (h : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  have hm := h
  unfold levG levA at hm
  rw [Subgroup.mem_inf, Subgroup.mem_comap, mem_lev] at hm
  obtain ⟨h1, h2, h3⟩ := hm
  exact ⟨h1, h2, Subgroup.mem_bot.mp h3⟩

private lemma levChi_flag1L_eq_levChi_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) :
    levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  have e1 : ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  have e2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := by
    unfold ext1
    split_ifs <;> rfl
  unfold levChi levFn
  rw [e1, e2]
  rfl

theorem law_of_pair {V W : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (β' : GL (Fin W.rank) (Lev.EAf D)) (L' : LevDat D.host.E ℂ W.rank) {X : Type} [AddCommGroup X] [Module ℂ X]
    {κ : GA D V} {u v : X}
    (h : (levChi V β (flagL L) κ)⁻¹ • u = (levChi W β' (flagL L') 1)⁻¹ • v) :
    u = levChi V β (flag1L L) κ • v := by
  have hne : levChi V β (flagL L) κ ≠ 0 := by
    unfold levChi
    exact Units.ne_zero _
  rw [levChi_one W β' (flagL L'), inv_one, one_smul] at h
  rw [levChi_flag1L_eq_levChi_flagL, ← h, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem lawsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → LawsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hIs hθ hωY hωX hvY hvX
  have hInf : R.models_inf := hθ
  refine ⟨?_, ?_⟩
  · intro t k hk κ hκ
    have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) 1 κ := isLift_of_mem _ _ _ hκ
    have hl' := isLift_one (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv)
    have key := GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hIs hInf hωY hvY t k hk 1 κ 1 hl hl'
    have e : flag1L (R.datYt t k R.triv) = R.datYt t k R.triv := rfl
    have hlaw := law_of_pair (R.βY k) (R.datYt t k R.triv) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩
  · intro t κ hκ
    have hl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) 1 κ :=
      isLift_of_mem _ _ _ hκ
    have hl' := isLift_one D.sp.X' R.βX (R.datXt t)
    have key := _root_.GlobalTheory.StepLaw.last_step_law R hIs hInf hωX hvX t 1 κ 1 hl hl'
    have e : flag1L (R.datYt t (D.R.m - 1) R.triv) = R.datYt t (D.R.m - 1) R.triv := rfl
    have hlaw := law_of_pair (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) R.βX (R.datXt t) key
    rw [e] at hlaw
    exact ⟨hl.1, hlaw⟩

end GlobalTheory.Chain.SourceLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZero
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem tprod_ne_zero_of_ne {κ : Type} [Fintype κ] {V : κ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {v : ∀ j, V j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem tmul_ne_zero_of_ne {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} {y : Q}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h0
  have := congrArg ((TensorProduct.rid ℂ P).toLinearMap ∘ₗ LinearMap.lTensor P l) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero, hl,
    one_smul] at this
  exact hx this

theorem pure_neg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (-f) φ = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, neg_mul]

theorem exists_not_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ¬ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  classical
  haveI := hM.real.nontriv
  obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
  obtain ⟨f, hfP, hfy⟩ : ∃ f ∈ G.M.Pol Bs.ψ Bs.emb, R.p f = y := by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    exact Submodule.mem_map.1 this
  have hloc : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v φ ≠ 0 := fun v => by
    haveI := hM.fin.nontriv v
    obtain ⟨z, hz⟩ := exists_ne (0 : Rf.Pi v)
    have : z ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := (hM.fin.onto v) ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 this
    exact ⟨φ, hφ, hz⟩
  choose ψ0 hψ0 hψ0ne using hloc
  have hvac := hM.triple.geo.hM.vac
  let φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun v => if v ∈ Xc.T then ψ0 v else G.M.vac v
  have hφSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0 v
    · simp only [φ, h, if_false]; exact (hvac v).1
  have hφout : ∀ v ∉ Xc.T, φ v = G.M.vac v := fun v h => by simp [φ, h]
  have hφne : ∀ v, Rf.p v (φ v) ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0ne v
    · simp only [φ, h, if_false]; exact (hM.fin.sph v h).2
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, ?_, ?_⟩
  · have := sum_pure_mem_algD G.M Bs.ψ Bs.emb Xc.T (m := 1) (fun _ => f) (fun _ => φ) (fun _ => ⟨hfP, hφSB, hφout⟩)
    simpa using this
  · rintro ⟨T, hT, m, f', φ', hf', hΦ, hsum⟩
    let g : Fin (m + 1) → SInf F (Fin a × Fin (a + a')) := Fin.cons (-f) f'
    let χ : Fin (m + 1) → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := Fin.cons φ φ'
    have h0 : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (χ i) = 0 := by
      simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, pure_neg, ← hΦ, neg_add_cancel]
    have hout : ∀ i, ∀ v ∉ T, χ i v = G.M.vac v := by
      intro i v hv
      induction i using Fin.cases with
      | zero => exact hφout v (fun h => hv (hT h))
      | succ j => exact (hf' j).2.2 v hv
    have key := GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M.vac (fun v => (hvac v).2.1) hM.triple.geo.hM.std R.p Rf.Pi Rf.p T (m + 1) g χ hout h0
    simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, map_neg, TensorProduct.neg_tmul, hsum, add_zero,
      neg_eq_zero] at key
    exact tmul_ne_zero_of_ne (hfy ▸ hy) (tprod_ne_zero_of_ne fun v : T => hφne v.1) key

end GlobalTheory.PolKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)

theorem base_isGood {D : D7} (B : Base D.host.F D.host.E) (hψ : IsStdChar D B.ψ (-1))
    (hP : ∀ v ∈ B.P, ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) : B.IsGood D.sp.cm.sig := by
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := by
             intro v w hw
             have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
               rintro ⟨w1, w2, hne, h1, h2⟩
               apply hne
               have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
                 have hle : w.asIdeal ≤ u.asIdeal := by
                   rw [← hw]
                   exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
                 exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
               rw [key w1 h1, key w2 h2]
             obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
             exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
           psiP := fun v hv => GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v fun hle => hP v hv (Ideal.dvd_iff_le.2 hle) }

theorem exists_good_place (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ S ∧ SplitsFully D.host.E v₁ ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  classical
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := mul_ne_zero (mul_ne_zero hn hq) hd
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  refine ⟨v, fun hu => ?_, ?_, ?_⟩
  · refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt v hp ?_ hv
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.TripleDarboux

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialMatchZeroIffPureTensorImageZero
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKer


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem polMatch_zero_iff_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM Φ
  constructor
  · rintro ⟨T, hX, m, m', f, φ, f', φ', h1, h1', hΦ, h0, he⟩
    refine ⟨T, hX, m, f, φ, h1, hΦ, ?_⟩
    rw [he]
    exact GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M'.vac (fun v => (hM.triple.geo.hM'.vac v).2.1) hM.triple.geo.hM'.std R.p' Rf.Pi Rf.p' T m' f' φ'
      (fun j => (h1' j).2.2) h0.symm
  · rintro ⟨T, hX, m, f, φ, h1, hΦ, hz⟩
    refine ⟨T, hX, m, 0, f, φ, Fin.elim0, Fin.elim0, h1, fun j => j.elim0, hΦ, ?_, ?_⟩
    · simp
    · rw [hz]; simp

end GlobalTheory.PolKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow


open Classical in
def extFn {D : D7} {m n : ℕ} (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (t : Mx D m n) : ℂ :=
  if IsHalf (e₀ + e₁) t then Φ (e₀ • t) * halfInd e₁ Λ (e₁ • t) else 0

section Gen
variable {D : D7} {m n : ℕ}

theorem symplO_eq_of_half {S T : HSp D} {e₀ e₁ : AE D} (h01 : e₀ * e₁ = 0) (t y : WO S T)
    (ht : IsHalf (e₀ + e₁) t) (hy : IsHalf (cA D e₀) y) : symplO S T t y = symplO S T (e₀ • t) y := by
  have hw : IsHalf e₁ (t - e₀ • t) := fun i j => by
    have := ht i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [add_mul] at this
    rw [mul_sub, ← mul_assoc, mul_comm e₁ e₀, h01, zero_mul, sub_zero]
    linear_combination this
  have hz : symplO S T (t - e₀ • t) y = 0 := by
    unfold symplO
    rw [GlobalTheory.VecProd.hO_zero' (a := e₁) (b := e₀) h01 hw hy, mul_zero, map_zero]
  have hs := GlobalTheory.VecProd.symplO_sub t (e₀ • t) y
  rw [hz] at hs
  linear_combination -hs

theorem smul_mem_latO_idem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {a : AE D} (ha : a * a = a) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    a • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) _ hu

end Gen

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem selfDual_chi {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) ∧ IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := by
  have hV : ∀ X : Node, X.InRange D.R.m → (G.V X).SigOK ∧ IsSelfDualC (G.V X) (G.Λ X) := fun X hX => by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact ⟨(G.isV hX h0).sigOK, (G.isV hX h0).sd⟩
    · push Not at h0
      obtain ⟨j, rfl⟩ := h0
      exact ⟨(GlobalTheory.ChiGrid.colY_isV D T L μ₀ hL j hX.2).sigOK, (GlobalTheory.ChiGrid.colY_isV D T L μ₀ hL j hX.2).sd⟩
  exact ⟨isSelfDualC_neg (hV (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).2, (hV (.grid i 0) ⟨hi.le, Nat.zero_le _⟩).2⟩

end Grid

end GlobalTheory.CosetRow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceRead
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeGeoRead

theorem theta_trace_read : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ' (h * a) →
    ∀ (Wt' : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) (Y' : UnitAt Wt')
      (e : AE D), IsIdemAt e P → ∀ Δ : Finset (WO (Vc D i) (Wc D i)),
        GlobalTheory.HeckeVacuum.IsHalfReps (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (cA D e) a Δ →
    ∀ (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z' : Fin (Vc D i).rank → Fin Wt'.g → ℂ),
        (∀ a, z' a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
      Formalism.L2.PjFree.toC (t none : CAt σ) ^ (Vc D i).rank *
                (ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h)) *
                ∏ a, (Complex.exp (-(Real.pi / 2 * hermForm Y'.Hm (z' a) (z' a))) * Y'.θ (z' a)) =
        ∑ x ∈ Δ, R.ωP i A.μ0 (1, γ' * h) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i))
          (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
  intro a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ X z' hz'
  have hfin : ∀ x ∈ Δ, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj he.1) (hΔ.1 x hx).2
  have hex : ∀ x : WO (Vc D i) (Wc D i), ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E)
      (w : WO (Vc D i) (Wc D i)), x.map (infPart D) = 0 →
        (w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
          x = actO (Vc D i) (Wc D i) 1 (γ' * h)⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w) := by
    intro x
    by_cases h0 : x.map (infPart D) = 0
    · obtain ⟨ℓ, w, h1, h2, h3⟩ := _root_.GlobalTheory.FinApprox.exists_rat_approx D G Pl0 T0 A T R hLev hFam hThP i (γ' * h) x h0
      exact ⟨ℓ, w, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' h0⟩
  choose ℓ u hℓu using hex
  rw [GlobalTheory.T.heckePointThetaTrace_eq_phasedTranslateSum D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
    a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ ℓ u (fun x hx => hℓu x (hfin x hx)) X z' hz']
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [_root_.GlobalTheory.HeisRatRead.heis_translate_read D G Pl0 T0 A T R hLev hFam hThP i (γ' * h) x (hfin x hx) (ℓ x) (u x)
    (hℓu x (hfin x hx)).1 (hℓu x (hfin x hx)).2.1 (hℓu x (hfin x hx)).2.2 X]

end GlobalTheory.HeckeGeoRead
end
end

