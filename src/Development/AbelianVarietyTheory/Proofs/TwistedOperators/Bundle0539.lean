module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn

theorem rowTest_setting_dat : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L →
    GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  refine Ev.mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK B f T w Z hX Wt z hOv hG hEx L hsz
  obtain ⟨hHost, hF, -, -, -, -, -, hstdX⟩ := hK (w.st Z) hOv
  have hC := z.pins.char
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hC hEx).1
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  exact
    { size := hsz
      eser := hG.eSerTie Z.V Z.S Z.G
      host := hHost
      hF := hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := z.pins.keep.guard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := z.pins.keep.std
      stdX := hstdX
      betaX := z.pins.keep.beta.2 }

end GlobalTheory.PrimIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarSqSmulMatrixSupportedAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
open GlobalTheory.SplitDblGen

namespace GlobalTheory.SplitDblGen

theorem inlD_mem_closure_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp _ h2 k hk
  obtain ⟨c, hcσ, hcAt, hc2, hcL⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hTr.base v hsp
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ _ G.W v h2 c hcσ hcAt (hcL _ G.W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ _ G.W v h2 c hcσ (hcL _ G.W) k hk
  have hg := GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer F E σ _ G.W v k hk
  have hKK' : mat k * mat k⁻¹ = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (mul_inv_cancel k)
  have hK'K : mat k⁻¹ * mat k = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (inv_mul_cancel k)
  have hAtK : At (evFin F v) (mat k - 1) := hk.1
  have hAtK' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [Matrix.mul_sub, hK'K, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hAtK u hu, Matrix.mul_zero, neg_zero]
  have hc2M : ∀ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), At (evFin F v) M → (c * c) • M = M := by
    intro M hM
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc2 _ (fun u hu => by
      have h0 := congrFun (congrFun (hM u hu) i) j
      simpa using h0)
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k) (mat k⁻¹) hKK' (hc2M _ hAtK)
  have ht' := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k⁻¹) (mat k) hK'K (hc2M _ hAtK')
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E _ c (mat k) (mat k⁻¹) hKK' hK'K (hc2M _ hAtK)
  let T : GL (Fin (a + a')) (AE F E) := ⟨tMat c (mat k), tMat c (mat k⁻¹), ht, ht'⟩
  have hinv : GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD n = 1 := GlobalTheory.DblVacFlip.matD_inv_mul n
  have hq : n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k ∈ GlobalTheory.InertDbl.ParD σ G.W v := by
    refine ⟨GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.inv_mem_KD hn.1) hp.1) hg, T, ?_⟩
    show GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD p * GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ G.W k) *
        diagCols (Fin (a + a')) = diagCols (Fin (a + a')) * tMat c (mat k)
    have h3 := congrArg (fun M => GlobalTheory.InertDbl.matD n⁻¹ * M) hid
    simp only [← Matrix.mul_assoc] at h3
    rw [GlobalTheory.InertDbl.matD_inlD, hpm]
    refine h3.trans ?_
    rw [← hnm, hinv]
    exact congrArg (· * tMat c (mat k)) (Matrix.one_mul _)
  have e : GlobalTheory.InertDbl.inlD σ G.W k = p⁻¹ * n * (n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k) := by group
  rw [e]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (s _ (Or.inl hp))) (s _ (Or.inr hn))) (s _ (Or.inl hq))

end GlobalTheory.SplitDblGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.StabLieAdelic

theorem conjU_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.mp hΦ
  have hg' : ∀ i, ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ (g i : (Fin n × Fin d → AF F) → ℂ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ :=
    fun i => (g i).2
  choose f φ hf hSB hvac hpure using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem _ (hf i), hSB i, hvac i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpure i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.SquareAgree.StabLieAdelic


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaContinuation
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

namespace GlobalTheory.ThetaRealDeriv

theorem schr_comp_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

theorem exists_transpose_mul_equiv {A : Type} [CommRing A] {α β γ : Type} [Fintype β] [DecidableEq β] (e : γ ≃ α)
    {G H : Matrix β β A} (hHG : H * G = 1) :
    ∃ T : Matrix β γ A ≃+ Matrix α β A, (∀ u, T u = uᵀ.submatrix e.symm id * G) ∧
      ∀ u, ((T u * H)ᵀ).submatrix id e = u := by
  have hGH : G * H = 1 := mul_eq_one_comm.1 hHG
  have hl : ∀ u : Matrix β γ A, ((uᵀ.submatrix e.symm id * G * H)ᵀ).submatrix id e = u := fun u => by
    rw [Matrix.mul_assoc, hGH, Matrix.mul_one]
    ext i j
    simp
  refine ⟨⟨⟨fun u => uᵀ.submatrix e.symm id * G, fun x => ((x * H)ᵀ).submatrix id e, hl, fun x => ?_⟩, fun u v => ?_⟩,
    fun _ => rfl, hl⟩
  · show ((((x * H)ᵀ).submatrix id e)ᵀ).submatrix e.symm id * G = x
    have : ((((x * H)ᵀ).submatrix id e)ᵀ).submatrix e.symm id = x * H := by
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [this, Matrix.mul_assoc, hHG, Matrix.mul_one]
  · show (u + v)ᵀ.submatrix e.symm id * G = uᵀ.submatrix e.symm id * G + vᵀ.submatrix e.symm id * G
    rw [← Matrix.add_mul]
    rfl

theorem finPart_realAd_smul (D : D7) (t : ℝ) (y : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • y) = 0 := by
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) = 0 := by
    show ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    exact TensorProduct.zero_tmul _ _
  rw [Algebra.smul_def, map_mul, h0, zero_mul]


set_option maxHeartbeats 1600000 in
theorem exists_line (D : D7) (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hVJ : Vs.J = -S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : ∀ i j, D.sp.cm.sig (Vs.J j i) = Vs.J i j)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (u₀ : Matrix (Fin S.rank) (Fin d) (AE D))
    (Φ Φ₁ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA D.host.F _)
    (h1 : Φ₁ ∈ GlobalTheory.WeilM.schA D.host.F _)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) Φ x) (Φ₁ x) 0) :
    ∃ L : ℝ →+ WO S X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
      GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Φ₁ =
        fun x => deriv (fun t : ℝ => heisO Bs.ψ S X (L t) (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Φ) x) 0 := by
  have hF : IsTotallyReal D.host.F := hBs.cm.1
  have hψc : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hHG : (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (S.gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (S.gram.map (incA D))ᵀ := by
    ext i j
    have h := hV j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (S.gram i j)) = incA D (S.gram j i)
    rw [← h]
    rfl
  obtain ⟨cS, hc, hci⟩ := exists_transpose_mul_equiv e (α := Fin X.rank) hHG
  have hth : ∀ Ψ u, GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Ψ (cS u) = GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u Ψ) :=
    fun Ψ u => congrArg (fun v => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ v Ψ)) (hci u)
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
    (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  have hform : ∀ w w' : Matrix (Fin S.rank) (Fin d) (AE D), symplO S X (cS w) (cS w') =
      (M.co.e w).1 ⬝ᵥ (M.co.e w').2 - (M.co.e w').1 ⬝ᵥ (M.co.e w).2 := by
    intro w w'
    rw [← GlobalTheory.WeilSchrodinger.symp_eq_symplO D S X X.gramᵀ (D.host.xi0 • S.gram⁻¹) 1 rfl
      (one_smul _ _), co.form, hco, hco]
  have hcs : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hc, hc, ← Matrix.smul_mul]
    rfl
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) :=
    (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num)).symm
  refine ⟨AddMonoidHom.mk' (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u₀) fun s t => by
    rw [GlobalTheory.ThetaLineDeriv.realAd_add, add_smul], ?_, fun t => ?_, funext fun x => ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u₀ i j
    exact (GlobalTheory.ThetaLineDeriv.continuous_realAd (F := D.host.F)).fun_smul continuous_const
  · ext i j
    exact finPart_realAd_smul D t (cS u₀ i j)
  obtain ⟨u, rfl⟩ := cS.surjective x
  have hkey : ∀ t : ℝ, heisO Bs.ψ S X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u₀)
      (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Φ) (cS u) =
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) Φ)) := by
    intro t
    rw [← hcs]
    set u' := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀
    have e1 : ∀ x, M.co.rho Bs.ψ u (M.co.rho Bs.ψ u' Φ) x =
        Bs.ψ (⅟(2 : AF D.host.F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2)) *
          M.co.rho Bs.ψ (u + u') Φ x := by
      intro x
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_comp_apply Bs.ψ _ _ _ x
    simp only [heisO]
    rw [← map_add (f := _), hth]
    simp only [GlobalTheory.WeilM.thetaSum, e1, tsum_mul_left]
    rw [symplOH, hform, h2]
  rw [hth]
  have hder := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho M.co Bs.ψ hF hψc u₀ _ hΦ _ h1 hd u
  exact (hder.deriv.symm.trans (congrArg (fun g => deriv g 0) (funext hkey)).symm)


end GlobalTheory.ThetaRealDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProducts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

namespace GlobalTheory.SmallDat.ThBox

theorem isThetaFunO_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S₁ T₁ S₂ T₂ : HSp D} (p₁ : WO S T →+ WO S₁ T₁)
    (p₂ : WO S T →+ WO S₂ T₂) (c₁ : Continuous p₁) (c₂ : Continuous p₂)
    (hs : ∀ x y, symplO S T x y = symplO S₁ T₁ (p₁ x) (p₁ y) + symplO S₂ T₂ (p₂ x) (p₂ y))
    (r₁ : ∀ γ, ∃ γ', p₁ (ratW T S γ) = ratW T₁ S₁ γ') (r₂ : ∀ γ, ∃ γ', p₂ (ratW T S γ) = ratW T₂ S₂ γ')
    (hi : ∀ u, u.map (infPart D) = 0 → (p₁ u).map (infPart D) = 0 ∧ (p₂ u).map (infPart D) = 0)
    (hf : ∀ u, u.map (finPart D) = 0 → (p₁ u).map (finPart D) = 0 ∧ (p₂ u).map (finPart D) = 0)
    {f₁ : WO S₁ T₁ → ℂ} {f₂ : WO S₂ T₂ → ℂ} (h₁ : IsThetaFunO ψ S₁ T₁ f₁) (h₂ : IsThetaFunO ψ S₂ T₂ f₂) :
    IsThetaFunO ψ S T fun u => f₁ (p₁ u) * f₂ (p₂ u) := by
  have hH : ∀ x y, symplOH S T x y = symplOH S₁ T₁ (p₁ x) (p₁ y) + symplOH S₂ T₂ (p₂ x) (p₂ y) := fun x y => by
    unfold symplOH
    rw [hs, mul_add]
  refine ⟨fun γ w => ?_, ?_, (h₁.cont.comp c₁).mul (h₂.cont.comp c₂), fun k L hL hL0 w => ?_⟩
  · obtain ⟨γ₁, e₁⟩ := r₁ γ
    obtain ⟨γ₂, e₂⟩ := r₂ γ
    rw [map_add (f := _), map_add (f := _), hH, e₁, e₂, h₁.quasi, h₂.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, o₁, hU₁⟩ := h₁.level
    obtain ⟨U₂, o₂, hU₂⟩ := h₂.level
    refine ⟨U₁.comap p₁ ⊓ U₂.comap p₂, (o₁.preimage c₁).inter (o₂.preimage c₂), fun u hu h0 => funext fun w => ?_⟩
    have a₁ := congrFun (hU₁ (p₁ u) hu.1 (hi u h0).1) (p₁ w)
    have a₂ := congrFun (hU₂ (p₂ u) hu.2 (hi u h0).2) (p₂ w)
    unfold heisO at a₁ a₂ ⊢
    beta_reduce
    rw [← a₁, ← a₂, hH, map_add (f := p₁), map_add (f := p₂), AddChar.map_add_eq_mul]
    ring
  · simp only [map_add (f := _)]
    exact (h₁.smooth k (p₁.comp L) (c₁.comp hL) (fun t => (hf _ (hL0 t)).1) (p₁ w)).mul
      (h₂.smooth k (p₂.comp L) (c₂.comp hL) (fun t => (hf _ (hL0 t)).2) (p₂ w))

theorem mulG_map_zero {D : D7} {R : Type} [CommRing R] (φ : AE D →+* R) (S : HSp D) {n : ℕ}
    (x : Matrix (Fin n) (Fin S.rank) (AE D)) (h : x.map φ = 0) : (mulG S x).map φ = 0 := by
  rw [GlobalTheory.BigDat.mulG_eq, Matrix.map_mul, h, Matrix.zero_mul]

theorem continuous_mulG {D : D7} (S : HSp D) {n : ℕ} : Continuous (mulG S (n := n)) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact continuous_id.matrix_mul continuous_const

theorem mulG_rat {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) D.host.E) :
    mulG S (x.map (incA D)) = (x * S.gram).map (incA D) := by
  rw [GlobalTheory.BigDat.mulG_eq, Matrix.map_mul]

theorem infPart_cA {D : D7} (x : AE D) :
    infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_cA {D : D7} (x : AE D) :
    finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem maps_map_zero {R : Type} [CommRing R] (φ : AE D →+* R) (hφ : ∀ x, φ x = 0 → φ (cA D x) = 0) (t : T)
    (e : Num G i j) (u : PtS G i j) (h : u.map φ = 0) : (mapA t e u).map φ = 0 ∧ (mapB e u).map φ = 0 := by
  have h0 : ∀ a b, φ (u a b) = 0 := fun a b => congrFun (congrFun h a) b
  refine ⟨mulG_map_zero φ _ _ (Matrix.ext fun a b => h0 _ _), ?_⟩
  have h2 := mulG_map_zero φ (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))
    (Matrix.ext fun a b => hφ _ (h0 _ _))
  exact Matrix.ext fun a b => (map_neg φ _).trans (neg_eq_zero.2 (congrFun (congrFun h2 a) b))

theorem continuous_mapA (t : T) (e : Num G i j) : Continuous (mapA t e) :=
  (continuous_mulG (spW₁ G i j)).comp (continuous_id.matrix_submatrix id fun k => e (.inl k)).matrix_transpose

theorem continuous_mapB (e : Num G i j) : Continuous (mapB e) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact ((continuous_mulG (spV₁ G i j)).comp ((continuous_id.matrix_submatrix id fun k => e (.inr k)).matrix_map
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D))).neg

theorem mapA_rat (t : T) (e : Num G i j)
    (γ : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapA t e (γ.map (incA D)) = ratW (G.pT (.mu t i j)) (G.pS (.mu t i j)) γ' :=
  ⟨_, mulG_rat (spW₁ G i j) (γ.submatrix id fun k => e (.inl k))ᵀ⟩

theorem mapB_rat (e : Num G i j)
    (γ : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapB e (γ.map (incA D)) = ratW (G.pT (.chi i j)) (G.pS (.chi i j)) γ' :=
  ⟨-_, (congrArg Neg.neg (mulG_rat (spV₁ G i j) ((γ.submatrix id fun k => e (.inr k)).map star))).trans
    (Matrix.map_neg _ (map_neg (incA D)) _).symm⟩

theorem thetaS_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ (Φ + Φ') = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ + GlobalTheory.SmallDat.thetaS Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.boxS t e f₁ f₂ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D Bs hT.base _ Γ.V' _ _ hT.geo.hV'
  obtain ⟨hJ, L', hL, h4, h5, h6⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D Bs hT.base _ Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T₀ := GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hT.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))
  let S₀ := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L' hL h6 (fun _ => (0, 0))
  have eA : Γ.V'.J = T₀.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S₀.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hψ : IsStdChar D W.ψ (-1) := h.ψ ▸ _root_.GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT.base.std
  obtain ⟨ha, hi, hs⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := S₀) (T := T₀) Γ.M'.co hψ eA eB hT.geo.hM'.rat
  refine ⟨ha, hi, fun f₁ f₂ hf₁ hf₂ => (hs _).1 ?_⟩
  exact isThetaFunO_mul (S := S₀) (T := T₀) (AddMonoidHom.mk' (mapA t e) (mapA_add t e))
    (AddMonoidHom.mk' (mapB e) (mapB_add e)) (continuous_mapA t e) (continuous_mapB e)
    (fun x y => (GlobalTheory.ThetaTransform.symplO_eq_symp eA eB x y).trans (sympS_eq t e Γ h.JW₁ h.JWW x y))
    (mapA_rat t e) (mapB_rat e)
    (maps_map_zero (infPart D) (fun x hx => by rw [infPart_cA, hx, map_zero]) t e)
    (maps_map_zero (finPart D) (fun x hx => by rw [finPart_cA, hx, map_zero]) t e) hf₁ hf₂

end GlobalTheory.SmallDat.ThBox

end
end

