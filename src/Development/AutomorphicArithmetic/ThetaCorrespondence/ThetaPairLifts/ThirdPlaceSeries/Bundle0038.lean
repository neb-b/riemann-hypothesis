module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBDGam
public import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Formalism.LocalToGlobal.ClassRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Formalism.LocalToGlobal.Divisibility.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRowsEqRecordRows
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
namespace Formalism.L2.N.ExtNRows3
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
section Pin
variable (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
include hp hL h in
open Classical in
theorem base_rows_eq_record_rows_alt : P.S0.D = D.what₂.D0 := by
  obtain ⟨cOf, -, -, h3⟩ := hL
  have e1 := sum_finrank P.S0.Ep (Ep_decomp P h).1 (Ep_decomp P h).2
  rw [Module.finrank_fin_fun] at e1
  have e2 : ∑ c, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = ∑ σ, D.what₂.nRows0 σ :=
    Finset.sum_fiberwise _ _ _
  have e3 : ∑ σ, D.what₂.nRows0 σ = D.what₂.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  rw [← e1, ← e3, ← e2]
  exact Finset.sum_congr rfl fun c _ => (h3 c).symm
include hp hL h in
theorem finrank_Mj_eq_D0 : ∀ j, 1 ≤ j → j ≤ D.R.m → finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := finrank_Mj_eq_dW P ⟨k, by omega⟩
  rw [dW_eq_D P h, _root_.Formalism.L2.N.ExtNRows3.base_rows_eq_record_rows_alt T P hp hL h] at this
  exact this
end Pin
theorem thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) ∧
      finrank ℂ (D.what₂.Zj (P.I.tup t) ((i : ℕ) + 1)) = D.what₂.D0 := by
  have hi : Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) :=
    adjoint_injective _ (thetaP_surj P h hR i t hl)
  refine ⟨hi, ?_⟩
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hi]
  exact _root_.Formalism.L2.N.ExtNRows3.finrank_Mj_eq_D0 T P hp hL h _ (Nat.succ_le_succ (Nat.zero_le _)) i.2
end Formalism.L2.N.ExtNRows3
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvIpAtLeNormAtSq
section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder
namespace GlobalTheory.ColEvNorm
end GlobalTheory.ColEvNorm
namespace GlobalTheory.ColEvNorm
end GlobalTheory.ColEvNorm
theorem GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex _ T P K hpin hmu X0 hX0 v F
  have ht : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu P.A3.fam3.base3.μ0 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
    rw [hmu]
    have h : Formalism.L2.DIV.Qprime ((1 : Formalism.L2.DIV.Tup K.X.F K.X.E D.what₂.LL K.c.Sg) : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
      change Formalism.L2.DIV.Qprime (1 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅
      ext w
      simp [Formalism.L2.DIV.Qprime, MonoidHom.ker_one]
    unfold Formalism.L2.Col.QE
    split_ifs with hf
    · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
      rfl
    · rfl
  obtain ⟨hM, hev⟩ := hpin.columnEvaluationOk
  obtain ⟨ι, h1, h2⟩ := hev D.u₀
  obtain ⟨F', hm, hres, hι1⟩ := h1 _ ht hQ ((Formalism.L2.DIV.rV0 D P.A3.A P.Ps P.ψs P.A3.fam3.base3.μ0).mulVec F)
  obtain ⟨hm2, hι2⟩ := h2 _ ht hQ F
  have hz := hι1.symm.trans hι2
  have hF := congrArg Subtype.val (GlobalTheory.ColEvNorm.zOfRow_injective _ _ _ _ _ _ _ _ hz)
  rw [← hF]
  exact GlobalTheory.ColEvNorm.ipAt_le_of_ties (Xf := fieldsLL D K.X K.e) K.c.Pr K.c.Rk K.c.W K.c.Ch K.c.sel K.c.hX K.c.Lv K.c.Xg
    K.v0 K.TU K.xiVal K.trIv P.A3 P.Ps P.ψs P.Zs K.c.mu K.c.hP K.gEq hpin.grpTie
    (congrArg Ranks.m K.kerTie.2.1) K.plEq K.i0Eq K.tEq K.famEq K.muTie K.ok1 hpin.psTie.1 hpin.psTie.2
    X0 hX0 v F F' hm hres
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwOpenExpRelStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  first | exact @_root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt | exact _root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtOfBuiltStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_integrality_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ big₀ L₀, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁, ∀ L₁, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ i₁, ∃ i₀, ExtOf L₀ L₁ i₀ i₁ := by
  first | exact @_root_.GlobalTheory.CoefDuty.ExtBuilt.extOf_built_alt | exact _root_.GlobalTheory.CoefDuty.ExtBuilt.extOf_built_alt | (intros; apply _root_.GlobalTheory.CoefDuty.ExtBuilt.extOf_built_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GammaSizeOfParameters
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
noncomputable section
namespace Formalism.L2.DIV.Cons
open Formalism.L2.DIV Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
theorem gamma_size_of_sizeData_alt {Tk : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (hR : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Tk P) (hTf : Finite P.T) (hSG : SizeG L)
    (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) :
    DGamSize P.A3.A P.P0 P.ψ0 (ofRecord D L Del h0) Nc hTf 1 (2 + 9 * C) :=
  dGamSize_record_one P.A3.A P.P0 P.ψ0 hTf L hSG hSC Del h0 Nc hNc P.tied.div.grp.card D.u₀ hR.gamDvd.2 C hC hF
end Formalism.L2.DIV.Cons
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemSQ
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GoodOffLoc
theorem good_not_mem_S_Q_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := by
  intro _ hL D P X hA i _ w hG
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 :=
        (MonoidHom.pow_apply ..).symm.trans
          (congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha)
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i :=
      Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hl (dvd_trans (by norm_num) h15)
    have h5 : 5 = D.nd.l i :=
      Nat.prime_eq_prime_of_dvd_pow Nat.prime_five hl (dvd_trans (by norm_num) h15)
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  refine ⟨fun hS => ?_, fun hQ => ?_⟩
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hng 0 h
    · exact hng 1 h
    · exact hnp h
  · rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
end GlobalTheory.GoodOffLoc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HasExpOfLayer
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
namespace GlobalTheory.ExpTiesOfLayer
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem hasExp_of_layer_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.PlugPt.HasExponent' (_root_.GlobalTheory.HeightCounting.defaultExtension hL) ∧ ∀ (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL), (∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.PlugPt.HasExponent' E := by
  intro hL
  have hNE : _root_.GlobalTheory.PlugPt.HasExponent' (_root_.GlobalTheory.HeightCounting.defaultExtension hL) := by
    intro K B f T w Z Wt p0 t nch n xd c y
    have hg := c.row.grp
    refine ⟨⟨⟨⟨⟨y.ser.ex⟩, ⟨fun g => (hg.lvl0 g).symm, ?_⟩, ?_⟩⟩, PUnit.unit⟩⟩
    · intro i b u hu
      obtain ⟨x, hx, hx'⟩ := hg.psi0 u hu i b
      exact ⟨x, hx, hx'⟩
    · intro i j b a _
      rw [y.xd i ((j : ℕ) + 1) b (by omega) (by omega)]
      exact Set.mem_univ _
  exact ⟨hNE, fun E hE K B f T w Z Wt p0 t nch n xd c e => by
    obtain ⟨y⟩ := hE K B f T w Z Wt p0 t nch n xd c e
    exact hNE K B f T w Z Wt p0 t nch n xd c y⟩
end GlobalTheory.ExpTiesOfLayer
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure RecTAlt (ex : Extra D L hT Gi Gl K Y cX) where
  T : _root_.Formalism.L2.TiedDataSKAlt ex
  pin : _root_.Formalism.L2.Rows.RowPinMinAlt T
  joints : _root_.Formalism.L2.JointsSAlt T.toTiedDataS
  host : _root_.Formalism.L2.HostDatumSelfDual T.toTiedDataS
  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W
def ExtraDataRecursive (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.RecTAlt ex)
theorem ExtraDataRecursive.tiedSK {ex : Extra D L hT Gi Gl K Y cX} (h : _root_.Formalism.L2.ExtraDataRecursive ex) : _root_.Formalism.L2.ExtraDataSelfDualKernel ex :=
  let ⟨R⟩ := h; ⟨R.T⟩
end
def SecondLayerFamilyClass : FamClass := fun {_} Fm =>
  (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i)) ∧ _root_.Formalism.L2.LinkedFamiliesAligned' Fm
theorem SecondLayerFamilyClass.c2sk {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.LinkedFamiliesKernelFrame' Fm := by
  obtain ⟨⟨x0, h⟩, _⟩ := h
  exact ⟨x0, fun x hx hx0 i => (h x hx hx0 i).tiedSK⟩
theorem SecondLayerFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm := h.c2sk.c2s
theorem group_compatibility_of_second_layer_family {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : G.GroupCompatibilityFamily Fm := _root_.Formalism.L2.gTiedF_of_C2S_alt Fm h.c2s
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapSharpAmbientTie
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3
theorem lower_map_sharp_ambient_tie_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (T : _root_.Formalism.L2.TiedDataSKAlt ex), (∀ u, LowerMapTieS (T.cols.forms u)) → (∀ u μ (hμ : μ ≠ D.what₂.mu0) (_ : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1) → (∃ J, AmbTie D x.A3.A (RowSide.sharp D) ex.amb x.F.P1 x.F.ψ1 x.Y.tup x.Y.jA J) → ((∀ (t : x.T) (c : (x.A3.A.fam.R t).S.Cl), Fintype.card ((x.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧ ∀ (j : Fin D.R.m) (t : x.T) (c : (x.A3.A.fam.L j t).S.Cl), Fintype.card ((x.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) → _root_.Formalism.L2.Rows.RowSideDeterminedAlt T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro D L hT Gi Gl K Yd cX ex x T hL hLt hA hG
  exact
    { lowerMap := hL
      lowerMapTw := hLt
      buDef := x.Y.bu
      ambS := hA
      faces := ⟨x.F.Dc, x.F.Sp, rfl, HEq.rfl⟩
      gamDvd := hG }
end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RaysOfRayRec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX
  GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Plug.RaysW
theorem rays_of_rayRec_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K),
    RayRec (p.w.D p.Z) p.O.ex.nch → (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Rays := by
  intro hL 𝒮 ν K p hR t
  have hlev := p.x.what₂.r.z.lev
  have hmu := p.x.what₂.mu
  have hn := p.x.n.Q
  change R3.TupU p.w.I (R3.usedOf p.w.I p.T p.x.Wt) at t
  show GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField _ (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.x.what₂.r.z.R.toRealDat t)
  rcases (R3.mem_range_ixOf p.w.I).1 ⟨t, rfl⟩ with h0 | ⟨w, hw, hxi⟩
  ·
    obtain ⟨v⟩ := nonempty_heightOneSpectrum (p.w.D p.Z).what₂.LL
    refine hR ((p.w.D p.Z).plEq.symm v) _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    rw [hlev.xiH t, h0, p.w.ok.trueColumnChoices_heckeChar_reference_eq_one] at hram
    exact absurd (Formalism.L2.Fam.DivCQ.unrAt_one P) hram
  ·
    refine hR w _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    have hpl := (hlev.is.Q_pl t P hP).1
    by_cases hpd : (((p.w.D p.Z).host.pde * (p.w.D p.Z).host.pde' : ℕ) : 𝓞 (p.w.D p.Z).host.E) ∈ P.asIdeal
    · obtain ⟨q, hq, hc, -⟩ := hpl
      exact Or.inl ⟨hpd, hc ▸ hq⟩
    · right
      have hx : p.x.what₂.r.z.R.xiH t = p.T.xiTw p.f w := by
        rw [hlev.xiH t, hxi, p.w.C_eq]
      rw [hx] at hram
      have h1 : ¬ ((p.B.host.pde : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
      have h2 : ¬ ((p.B.host.pde' : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
      have hδ : (if p.B.places.resChar w = p.B.host.pde then p.f.del' else p.f.del).UnrAt P := by
        split_ifs
        · exact p.f.isDel'.unr P h2
        · exact p.f.isDel.unr P h1
      have hψ : ¬ (p.T.psi w).UnrAt P := fun h ↦ hram (Formalism.L2.Host.HChar.UnrAt.mul hδ h)
      have hQ : P ∈ p.T.Q w := by
        by_contra hq
        exact hψ (((p.T.psi_is w).ram P).2 hq)
      refine ⟨fun hm ↦ ?_, (hn w hw).1 ▸ hQ⟩
      have e1 : p.T.xiTw p.f w = 1 := by
        rw [← hmu.tw w, ← hmu.on w hw]
        exact (congrArg p.w.I.xi hm).trans hmu.mu0
      rw [e1] at hram
      exact hram (Formalism.L2.Fam.DivCQ.unrAt_one P)
end GlobalTheory.Plug.RaysW
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWChr
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.PlugPt.side_weight_psi_values_tame_tie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf p.O.ex.nch (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf.W.om := by
  intro hL 𝒮 ν K p
  refine ⟨p.x.n.chrPsi, ?_, ?_⟩
  · intro v _
    show (p.x.n.tp.psi v).ValuesIn 0 _
    rw [p.x.n.psi]
    exact GlobalTheory.twDat_psi_valuesIn_LL p.B p.T p.x.coh v
  · have h := p.x.what₂.grp
    have hf := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
    show GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z).W.om
    rw [hf]
    exact types_of_true (D := p.w.D p.Z) _ h
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamAtInert
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.NJoin.sysParam_at_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  intro _ _ D P X _ _ _ _ i hμ j hj x _ f _ y _ h0 h hh s hs w hw _
  obtain ⟨B, hB⟩ := GlobalTheory.DownLift.Params.paramsV X.R X.given.core j (X.tupT (D.nd.mu i)) h hh s y hs h0
  exact ⟨B w, hB _ hw w rfl⟩
end
end

