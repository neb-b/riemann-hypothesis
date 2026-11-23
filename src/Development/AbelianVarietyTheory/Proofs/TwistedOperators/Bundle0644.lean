module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepPointMulPeriodUnipotentGLMeasurePreserving
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentStepsInvariantVertex
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0635

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.RowVac

set_option synthInstance.maxHeartbeats 400000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

private lemma eToEAf_mem_hatL_of_mem {n : ℕ} (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (s : Fin n → D.host.E) (hs : s ∈ C) :
    (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem fwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (hb _).1 (eToEAf_mem_hatL_of_mem C s hs)


set_option maxHeartbeats 1000000 in
theorem bwd_gen (V : HSp D) (k : Formalism.L2.Theta.GA D V) (C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) C := by
  apply GlobalTheory.MovedHomLat.bwd V k C s
  rw [GlobalTheory.MovedHomLat.mem_globLat_iff]
  apply (hb _).2
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact eToEAf_mem_hatL_of_mem Λ s hs

theorem isVacO_om (W : G.Weil) (p : Pair T) (hp : p.InRange D.R.m) (g : Formalism.L2.Theta.GA D (G.pS p)) (h : Formalism.L2.Theta.GA D (G.pT p))
    (hg : g ∈ GfC (G.pS p)) (hh : h ∈ GfC (G.pT p)) (AS BS : Set (Fin (G.pS p).rank → D.host.E))
    (AT BT : Set (Fin (G.pT p).rank → D.host.E))
    (hact : ∀ w' ∈ latO _ _ BS BT (fun _ => True), ∃ w ∈ latO _ _ AS AT (fun _ => True), actO _ _ g h w = w')
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) AS AT f) :
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) BS BT (W.om p (g, h) f) := by
  have hW := W.om_is p hp
  unfold IsVacO at hf ⊢
  obtain ⟨hstd, hvac⟩ := hf
  obtain ⟨hθ, hth, hlat, hfock, hnrm⟩ := hvac
  obtain ⟨-, -, -, -, -, hpres, hint, -, -, hunit, -⟩ := hW
  have hth' := hpres (g, h) f hth
  have ⟨_, _, hc, _⟩ := hth
  have ⟨_, _, hc', _⟩ := hth'
  refine ⟨hstd, hθ, hth', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hact u hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hint g h _ f hth, hlat.1 w hw]
  · intro e he u hu hhalf
    obtain ⟨w, hw, rfl⟩ := hact u hu
    have hw' : IsHalf e w := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e g⁻¹ h⁻¹ hhalf
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hint g h _ f hth, hlat.2 e he w hw hw']
  · intro τ
    have hg1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hg τ
    have hh1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ hh τ
    have hgi : compAt W.θ τ (Formalism.L2.Theta.mt _ g⁻¹) = 1 := by
      have := GlobalTheory.WeilVacMove.compAt_mt_mul_inv W.θ τ _ g
      rwa [hg1, one_mul] at this
    have key : ∀ z', W.om p (g, h) (Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' f) =
        Formalism.IndefR.Datum.dRho (heisO W.ψ _ _) W.θ τ z' (W.om p (g, h) f) := by
      intro z'
      have := GlobalTheory.WeilVacMove.om_dRho (W.om_is p hp) hθ g h τ z' hth
      rwa [hh1, hgi, Matrix.one_mul, Matrix.mul_one] at this
    have h0 := hfock τ
    unfold IsFockVacAt at h0 ⊢
    intro z
    have h1 := h0 z
    unfold annih at h1 ⊢
    rw [← key, ← key, ← map_smul, ← map_add (f := _), h1, map_zero]
  · refine ⟨hnrm.1, fun a ha => ?_⟩
    have h1 : nrm2 a.1 a.2 f = 1 := hnrm.2 a ha
    show nrm2 a.1 a.2 _ = 1
    unfold IsCovolOne at ha
    obtain ⟨hμ, hF, -⟩ := ha
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc] at h1
    rw [GlobalTheory.WeilVacMove.sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hc', hunit a.1 a.2 hμ hF (g, h) f hth]
    exact h1

theorem neg_mem_GfC (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  unfold GfC at hg ⊢
  rw [MonoidHom.mem_ker] at hg ⊢
  exact hg


set_option maxHeartbeats 1000000 in
theorem moved_isVac (W : G.Weil) (N : Std G U) (Z : Normal W N) (i : ℕ) (hi : i < D.R.m) :
    W.IsVac (.chi i D.R.m) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (N.u (Pair.chi i D.R.m : Pair T).small).1
      (N.u (Pair.chi i D.R.m : Pair T).big).1) (Z.vac (.chi i D.R.m))) := by
  have hdp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hbig : DefNode D.R.m (Node.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
  have hsmall : DefNode D.R.m (Node.grid i D.R.m) := ⟨hi.le, rfl⟩
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := ⟨hi, le_rfl⟩
  have hU := N.u_lat _ hbig
  have hV := N.u_lat _ hsmall
  have hg : negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1 ∈ GfC (negSp (G.V (.grid (i + 1) D.R.m))) :=
    neg_mem_GfC (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).2
  have hh : (N.u (.grid i D.R.m)).1 ∈ GfC (G.V (.grid i D.R.m)) := (N.u (.grid i D.R.m)).2
  have hv := Z.vac_is _ hdp
  have hact : ∀ w' ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (G.latS (.chi i D.R.m) : Set _)
      (G.latT (.chi i D.R.m) : Set _) (fun _ => True), ∃ w ∈ latO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m))
      (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) (fun _ => True),
      actO (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (negGA (G.V (.grid (i + 1) D.R.m)) (N.u (.grid (i + 1) D.R.m)).1)
        (N.u (.grid i D.R.m)).1 w = w' := by
    refine (GlobalTheory.MovedHomLat.actO_latO_onto _ _ _ _ (N.latS (.chi i D.R.m)) (G.latS (.chi i D.R.m))
      (N.latT (.chi i D.R.m)) (G.latT (.chi i D.R.m)) ?_ ?_ ?_ ?_).2
    · intro s hs
      rw [mt_negGA]
      exact fwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact fwd_gen _ _ _ _ hV t ht
    · intro s hs
      rw [← map_inv, mt_negGA]
      exact bwd_gen _ _ _ _ hU s hs
    · intro t ht
      exact bwd_gen _ _ _ _ hV t ht
  exact isVacO_om W (.chi i D.R.m) hp _ _ hg hh _ _ _ _ hact _ hv

private lemma sigOK_and_isSelfDualC_grid {μ₀ : T} (hL : L.Is μ₀) (a b : ℕ) (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) :
    (G.V (.grid a b)).SigOK ∧ IsSelfDualC (G.V (.grid a b)) (G.Λ (.grid a b)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · show (columnBlock L b).sp.SigOK ∧ IsSelfDualC (columnBlock L b).sp (columnBlock L b).lat
    rcases lt_or_eq_of_le hb with hb' | rfl
    · rw [colY_lt L hb']
      exact ⟨D.sp.Y_sig _, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY b hb')⟩
    · rw [colY_m L]
      exact ⟨D.sp.X'_sig, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX⟩
  · have hv := G.isV (X := .grid a b) ⟨ha, hb⟩ (by intro j h; injection h with h1 h2; omega)
    exact ⟨hv.sigOK, hv.sd⟩

theorem isVac_unique (W : G.Weil) {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hp : (Pair.chi i j : Pair T).InRange D.R.m) {f f'}
    (hf : W.IsVac (.chi i j) f) (hf' : W.IsVac (.chi i j) f') : ∃ κ : ℂˣ, f' = (κ : ℂ) • f := by
  unfold GridData.Weil.IsVac at hf hf'
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hs1, hd1⟩ := sigOK_and_isSelfDualC_grid hL (i + 1) j hp1 hp2
  obtain ⟨hs2, hd2⟩ := sigOK_and_isSelfDualC_grid hL i j (by omega) hp2
  have key := VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.GridWeil.sigOK_neg hs1) hs2
    (fun τ => GlobalTheory.ChiGrid.isCartanInv_neg (W.cart_is (.grid (i + 1) j) ⟨hp1, hp2⟩ τ))
    (W.cart_is (.grid i j) ⟨by omega, hp2⟩) _ _
    (isSelfDualC_neg hd1) hd2 f f' hf hf'
  obtain ⟨c, hc, hcf⟩ := key
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  exact ⟨Units.mk0 c hc0, hcf⟩

theorem moved_vac_eq : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ i : ℕ, i < D.R.m → ∃ κ : ℂˣ, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ch.S.N.u (Pair.chi i D.R.m : Pair T).small).1 (ch.S.N.u (Pair.chi i D.R.m : Pair T).big).1) (ch.S.Z.vac (.chi i D.R.m)) = (κ : ℂ) • ch.rm.vX i D.R.m := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch i hi
  have hL : R.toLevCh.Is A.μ0 := by
    obtain ⟨-, -, -, -, hcore, -⟩ := hS
    exact hcore.lev
  exact isVac_unique ch.W hL i D.R.m ⟨hi, le_rfl⟩ (ch.rm.vX_is i D.R.m hi le_rfl)
    (moved_isVac ch.W ch.S.N ch.S.Z i hi)

end GlobalTheory.RowVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowVertexAdjacentStepsTranslateFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.FlatStepVertex

theorem mul_reindex_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix (Fin a ⊕ Fin c) ι' k) :
    g.val * D.reindex (frame h) f = ((frameGL h g).val * D).reindex (frame h) f := by
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

theorem reindex_mul_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix ι' (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

end GlobalTheory.FlatStepVertex

theorem GlobalTheory.flatStep_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {a₀ a₁ a₂ b c c₀ c' : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure] (hc₀ : c₀ = c + 1) (hc' : c' = c + 1)
    (h₁ : a₁ + c₀ = b) (h₂ : a₁ + (c + 1) = b) (h' : a₁ + c' = b) (g : GL (Fin b) k) (κ : GL (Fin a₁) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin a₁) c', frameGL h' g = v * embX c' κ →
    ∀ (x₀ : Matrix (Fin a₁) (Fin a₀) k) (x₁ : Matrix (Fin a₂) (Fin a₁) k),
    ∃ φ₀ : (StepVar (Fin a₁) c₀ (Fin a₀) → k) ≃ᵐ (StepVar (Fin a₁) c₀ (Fin a₀) → k),
      MeasurePreserving φ₀ (stepVol ν (Fin a₁) c₀ (Fin a₀)) (stepVol ν (Fin a₁) c₀ (Fin a₀)) ∧
    ∃ φ₁ : (StepVar (Fin a₂) c (Fin a₁) → k) ≃ᵐ (StepVar (Fin a₂) c (Fin a₁) → k),
      MeasurePreserving φ₁ (stepVol ν (Fin a₂) c (Fin a₁)) (stepVol ν (Fin a₂) c (Fin a₁)) ∧
    ∀ e₀ e₁,
      (∀ {ι : Type} (f : Fin a₀ ⊕ Fin (c₀ + 1) ≃ ι), (g⁻¹).val * (stepPt x₀ e₀).reindex (frame h₁) f =
        (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)).reindex (frame h₁) f) ∧
      (∀ {ι : Type} (f : Fin a₂ ⊕ Fin c ≃ ι), (stepPt x₁ e₁).reindex f (frame h₂) * g.val =
        (stepPt (x₁ * κ.val) (φ₁ e₁)).reindex f (frame h₂)) ∧
      (ch (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) + ch (stepPt (x₁ * κ.val) (φ₁ e₁)) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt (x₁ * κ.val) (φ₁ e₁) (.inr l) (.inl r) else 0) *
            stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0)) ∧
      (Odd c₀ → ∀ (l : Fin c₀) (s : Fin a₀), l.val = c₀ / 2 →
        stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inr l) (.inl s) = stepPt x₀ e₀ (.inr l) (.inl s)) ∧
      (Odd c₀ → ∀ (r : Fin a₂) (i : Fin (c + 1)), i.val = c / 2 →
        stepPt (x₁ * κ.val) (φ₁ e₁) (.inl r) (.inr i) = stepPt x₁ e₁ (.inl r) (.inr i)) := by
  intro k _ _ _ _ _ _ a₀ a₁ a₂ b c c₀ c' ν _ hc₀ hc' h₁ h₂ h' g κ hκ v hv hg x₀ x₁
  subst hc₀ hc'
  obtain ⟨φ₀, hφ₀, H₀⟩ := _root_.GlobalTheory.StepLeft.left_change (n := Fin a₁) (n' := Fin a₀) (c := c + 1) ν v hv κ hκ x₀
  obtain ⟨φ₁, hφ₁, H₁⟩ := _root_.GlobalTheory.TopLevelInv.stepPt_mul_symN_embX (n := Fin a₂) (n' := Fin a₁) (c := c) ν v hv κ hκ x₁
  refine ⟨φ₀, hφ₀, φ₁, hφ₁, fun e₀ e₁ => ?_⟩
  have hg₁ : frameGL h₁ g = v * embX (c + 1) κ := hg
  have hg₂ : frameGL h₂ g = v * embX (c + 1) κ := hg
  obtain ⟨A, B⟩ := _root_.GlobalTheory.PhaseStep.phase_step_inv (n₀ := Fin a₀) (n := Fin a₁) (n₂ := Fin a₂) (c := c) v hv κ x₀ e₀ x₁ e₁
    (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) (stepPt (x₁ * κ.val) (φ₁ e₁)) (H₀ e₀).symm (H₁ e₁).symm
  refine ⟨fun f => ?_, fun f => ?_, A, fun ho l s hl => ?_, fun ho r i hi => ?_⟩
  · rw [GlobalTheory.FlatStepVertex.mul_reindex_gen, map_inv, hg₁, H₀]
  · rw [GlobalTheory.FlatStepVertex.reindex_mul_gen, hg₂, H₁]
  · rw [show l = ⟨(c + 1) / 2, by omega⟩ from Fin.ext hl]
    exact (B ho).1 s
  · rw [show i = ⟨c / 2, by omega⟩ from Fin.ext hi]
    exact (B ho).2 r
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLatticesNonzeroLineVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a b : WO S₀ T) :
    symplO S T (d.ext0 T a) (d.ext0 T b) = symplO S₀ T a b := by
  have h := d.hO_ext T 0 0 0 0 a b
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  rw [symplO, symplO, h]

theorem isHalf_mul_right {k l m : ℕ} {e : AE D} {u : Mx D k l} (p : Mx D l m) (hu : IsHalf e u) : IsHalf e (u ⬝ p) := by
  intro i j
  show e * ∑ r, u i r * p r j = ∑ r, u i r * p r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [← mul_assoc, hu i r]

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


open GlobalTheory.FinPl.VLast.KernPf (wittCoreRestrictionHom wittCoreRestrictionHom_apply wittDecomposition_rankZero_ext_restriction) in
theorem lastLat_rankZero (hψ : IsStdChar D ψ (-1)) (J : JacL D 0) {X T L'' : HSp D} (o : OrthDec X T L'')
    (Γ : AddSubgroup (WO J.W T)) (ΓL : AddSubgroup (WO J.W₀ (negSp L''))) (ΓX : AddSubgroup (WO J.W₀ X))
    (hX : ∀ u, u ∈ ΓX ↔ J.d.ext0 T (o.resT J.W₀ u).1 ∈ Γ ∧ (show WO J.W₀ (negSp L'') from (o.resT J.W₀ u).2) ∈ ΓL)
    (h₁ : ∃ f, VacG ψ J.W T Γ f ∧ f ≠ 0) (h₂ : ∃ f, VacG ψ J.W₀ (negSp L'') ΓL f ∧ f ≠ 0) :
    LastLat ψ J o Γ ΓL ΓX := by
  have s0 := @GlobalTheory.SplitScalar.symplO_zero_right D
  have mA : ∀ a : WO J.W₀ T, J.d.ext0 T a ∈ Γ → (o.resT J.W₀).symm (a, 0) ∈ ΓX := fun a ha => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨ha, zero_mem _⟩
  have mB : ∀ b : WO J.W₀ L'', (show WO J.W₀ (negSp L'') from b) ∈ ΓL → (o.resT J.W₀).symm (0, b) ∈ ΓX := fun b hb => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨by rw [map_zero]; exact zero_mem _, hb⟩
  have n : ∀ a b : WO J.W₀ L'', ψ (symplO J.W₀ L'' a b) = 1 → ψ (symplO J.W₀ (negSp L'') a b) = 1 := fun a b h => by
    have e : symplO J.W₀ (negSp L'') a b = -symplO J.W₀ L'' a b := by
      simp only [symplO, hO, negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
    rw [e, ← GlobalTheory.CjNeg.conj_psi hψ, h, map_one]
  have hA : ∀ e (u : WO J.W₀ T), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (u, 0)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, add_zero]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have hB : ∀ e (u : WO J.W₀ L''), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (0, u)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, zero_add]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have back : ∀ u : WO J.W T, J.d.ext0 T (wittCoreRestrictionHom J.d T u) = u := wittDecomposition_rankZero_ext_restriction J.d T
  refine ⟨fun (w : WO J.W₀ X) hw => ⟨⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun (u : WO J.W₀ L'') hu => n _ _ ?_,
    fun e he (u : WO J.W₀ L'') hu hh => n _ _ ?_⟩, ?_⟩
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.1 _ (mA _ hu')
    rw [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_snd, nsmul_zero, s0, add_zero] at this
    rw [← back u, ← map_nsmul, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.2 e he _ (mA _ hu') (hA e _ (isHalf_mul_right _ hh))
    rw [o.symplO_resT, AddEquiv.apply_symm_apply, s0, add_zero] at this
    rw [← back u, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have := hw.1 _ (mB u hu)
    rwa [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_fst, nsmul_zero, s0, zero_add] at this
  · have := hw.2 e he _ (mB u hu) (hB e u hh)
    rwa [o.symplO_resT, AddEquiv.apply_symm_apply, s0, zero_add] at this
  · obtain ⟨f₁, a₁, b₁⟩ := h₁
    obtain ⟨f₂, a₂, b₂⟩ := h₂
    refine ⟨f₁, f₂, a₁, a₂, b₁, b₂, ?_⟩
    show VacG ψ J.W₀ X _ (o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂))
    refine ⟨o.isThetaFunO_boxT (GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero J.d T a₁.1) (GlobalTheory.CjNeg.theta_negT' hψ a₂.1),
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, map_nsmul (o.resT J.W₀), Prod.smul_fst, Prod.smul_snd, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        map_nsmul (J.d.ext0 T), a₁.2.1 _ h1, GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (a₂.2.1 _ h2)
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        a₁.2.2 e he _ h1 (GlobalTheory.RankZeroVac.isHalf_wittHyperbolicExtendByZero_apply J.d T (GlobalTheory.AscInh.isHalf_mul o.pA hh)), GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))
        (a₂.2.2 e he _ h2 (GlobalTheory.AscInh.isHalf_mul o.pB hh))

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem latCore_zero_split : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (u : WO (G.V (.core 1)) (G.V (.core 0))), u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.resT _ u).1 ∈ latRow G 0 ∧ (F.oz.resT _ u).2 ∈ lineLat F 0 := by
  intro D q T L μ0 hL sc G W M hM F hF h u
  have e1 := _root_.GlobalTheory.ProjCore.proj_mem_latCore D q T L μ0 hL sc G W M hM F hF
  have e2 := GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero D q T L μ0 hL sc G W M hM F hF h
  have hu : F.oz.jA ⬝ (F.oz.pA ⬝ u) + F.oz.jB ⬝ (F.oz.pB ⬝ u) = u := (F.oz.resT _).symm_apply_apply u
  have hl : F.oz.pB ⬝ u ∈ lineLat F 0 ↔ (F.oz.resT _).symm (0, F.oz.pB ⬝ u) ∈ latCore G 0 := Iff.rfl
  show u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.pA ⬝ u) ∈ latRow G 0 ∧ F.oz.pB ⬝ u ∈ lineLat F 0
  rw [hl, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB ⬝ (F.oz.pB ⬝ u)), ← e2]
  constructor
  · intro hm
    have ha := e1 u hm
    refine ⟨ha, ?_⟩
    have hb : F.oz.jB ⬝ (F.oz.pB ⬝ u) = u - F.oz.jA ⬝ (F.oz.pA ⬝ u) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hu
    rw [hb]; exact sub_mem hm ha
  · rintro ⟨ha, hb⟩
    rw [← hu]
    exact add_mem ha hb

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem lastLat_std : OnStd fun {D} _ _ _ {G} W F => (∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (lineLat F ρ) Φ₀ ∧ Φ₀ ≠ 0) ∧ ∀ (v : CoreVol G) h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (lineLat F 0) (latCore G 0) := by
  intro D q T L μ0 hL sc G W M hM F hF
  have hψ := W.ψ_std
  have hline0 : ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := _root_.GlobalTheory.AscFin.LineZero.exists_vacG_lineLat_zero D q T L μ0 hL sc G W M hM F hF
  refine ⟨fun ρ hρ => ?_, fun v h => ?_⟩
  · rcases ρ with _ | σ
    · exact hline0
    · obtain ⟨-, -, h3⟩ := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D q T L μ0 hL sc G W M hM F hF
      exact _root_.GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ hψ _ _ _ _ (G.sp.P_is (2 * (σ + 1) + 1) (by omega)).sd (h3 (σ + 1)) _ le_rfl
  · have hm : 0 < D.R.m := by omega
    have hdep := dep_vac W 0 hm
    refine lastLat_rankZero hψ (F.jac v 0 h) F.oz _ _ _ (latCore_zero_split D q T L μ0 hL sc G W M hM F hF h) ?_ hline0
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (W.vac 0), ⟨GlobalTheory.CjNeg.theta_negS' hψ hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.1 u hu))
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.2 e he u hu hh))
    · intro h0
      apply GlobalTheory.SeeSaw.Inh.vac_ne_zero (W.vac_is 0 hm)
      funext w
      have h1 := congrFun h0 w
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Pi.zero_apply, map_eq_zero] at h1
      exact (map_eq_zero (starRingEnd ℂ)).1 h1

end GlobalTheory.LastSeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0Trivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModulUnit

open GlobalTheory.ChiGrid

theorem exists_int_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have hne : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
    intro v' hv'
    by_contra hc
    push_neg at hc
    have hle : v'.asIdeal ≤ v.asIdeal := fun t ht => hc t ht
    have heq : v'.asIdeal = v.asIdeal := v'.isMaximal.eq_of_le v.isPrime.ne_top hle
    have : v' = v := HeightOneSpectrum.ext heq
    exact hv (this ▸ hv')
  choose! f hf using hne
  refine ⟨∏ v' ∈ P.S0, f v' ^ P.depth sc v', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v', hv', h⟩
    exact (hf v' hv').2 (v.isPrime.mem_of_pow_mem _ h)
  · rw [map_prod, Places.modul]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have e : ((P.w v').under (𝓞 D.host.F)).asIdeal = v'.asIdeal := by rw [P.under_w hv']
    have h1 : f v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := e ▸ (hf v' hv').1
    exact h1

end GlobalTheory.ModulUnit

theorem GlobalTheory.ModulUnit.idV_modul_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  intro D T L P sc v hv
  obtain ⟨t, ht, htm⟩ := GlobalTheory.ModulUnit.exists_int_mem_modul P sc v hv
  apply le_antisymm
  · exact GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v
  · rw [GlobalTheory.SeeSaw.idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hαv, a, ha, rfl⟩
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [GlobalTheory.IdVGen.tmul_eq ht α]
    obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα hαv
    refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * o, Ideal.mul_mem_right _ _ htm, by rw [map_mul]; rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLine
section
open GlobalTheory.RowClaim GlobalTheory.RowReal

theorem GlobalTheory.RowReal.periodsOnLine_big : Big fun ch => PeriodsOnLine ch :=
  big_mono (fun ch h => periodsOnLine_of_invLine GlobalTheory.OneFunctional.oneLine ch h) _root_.GlobalTheory.RowReal.invLine_big
end

