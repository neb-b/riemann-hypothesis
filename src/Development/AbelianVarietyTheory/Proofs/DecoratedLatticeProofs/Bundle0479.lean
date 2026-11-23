module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAvgForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepSplitPlaceValuePeriodGroupInvaria
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblInv

theorem val_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Θ₁ : WO S.B.V S.J.W → ℂ) (Θ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    S.val c₁ c₂ Θ₁ Θ₂ φ f g h₁ h₂ = S.val c₁ c₂ (S.s₁.om (g, h₁) Θ₁) (S.s₂.om (h₁, h₂) Θ₂) φ (rTrans h₂ f) 1 1 1 := by
  unfold Dbl2.val Dbl2.con
  have e3 : rTrans (1 : GA D S.B'.V) (rTrans h₂ f) = rTrans h₂ f := by funext x; simp [rTrans]
  rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
    map_one, map_one, e3]
  rfl


set_option maxHeartbeats 2000000 in
theorem val_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f → ∀ g h₁ h₂, g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v) → h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v) → h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v) → ∀ a x y, ∀ r ∈ RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1), ∀ j ∈ Q.L₁.J, ∀ r' ∈ R Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ j' ∈ Q.L₂.J, S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ (r * x * j)) (h₂ * Q.gl₂ (r' * y * j')) = S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ f₁ f₂ hvac φ f hφ hf hTy g h₁ h₂ hg hh₁ hh₂ a x y r hr j hj r' hr' j' hj'
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hvac
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := _root_.GlobalTheory.hasConductor_one_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨-, -, -, cm₀, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B.V _ Q.F.G₀ Q.gl₀ Q.loc₀
  obtain ⟨-, -, -, cm₁, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.J.W _ Q.F.G₁ Q.gl₁ Q.loc₁
  obtain ⟨-, -, -, cm₂, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂
  have hT₁' := _root_.GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁ T₁ hT₁ g hg h₁ hh₁
  have hT₂' := _root_.GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂ T₂ hT₂ h₁ hh₁ h₂ hh₂
  have hf' : IsContAut S.B'.V (rTrans h₂ f) :=
    ⟨fun γ hγ x => by simp only [rTrans, mul_assoc]; exact hf.1 γ hγ _, hf.2.comp (continuous_mul_const h₂)⟩
  have hTy' : Q.Typed (rTrans h₂ f) := fun j => by
    funext x
    have := congrFun (hTy j) (x * h₂)
    simp only [rTrans, Pi.smul_apply] at this ⊢
    rw [mul_assoc, cm₂ j h₂ hh₂, ← mul_assoc, this]
  obtain ⟨A, τ, T, hsm, hτ, hmem, htri, hval, -⟩ :=
    _root_.GlobalTheory.TriStep.tri D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ _ _ hT₁' hT₂' φ hφ
  set F : A := ⟨rTrans h₂ f, hmem _ hf' hTy'⟩ with hFdef
  let Φa : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
    fun x => ⟨om Q.μ₁ a x Q.Φ₁.1, om_mem_SB Q.μ₁ a x Q.Φ₁.2⟩
  let Φb : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →
      SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x y => ⟨om Q.μ₂ x y Q.Φ₂.1, om_mem_SB Q.μ₂ x y Q.Φ₂.2⟩
  have d1 : comb ψ _ _ Q.D₁ (T₁ O₁) = T₁ Q.Φ₁ := (Q.dat₁.2 T₁ hT₁ O₁ Q.Φ₁ hO₁ rfl).symm
  have d2 : comb ψ _ _ Q.D₂ (T₂ O₂) = T₂ Q.Φ₂ := (Q.dat₂.2 T₂ hT₂ O₂ Q.Φ₂ hO₂ rfl).symm
  have KEY : ∀ x y, S.val c₁ c₂ (comb ψ _ _ Q.D₁ (T₁ O₁)) (comb ψ _ _ Q.D₂ (T₂ O₂)) φ f (g * Q.gl₀ a)
      (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) =
      S.val c₁ c₂ ((S.s₁.om (g, h₁) ∘ₗ T₁) (Φa x)) ((S.s₂.om (h₁, h₂) ∘ₗ T₂) (Φb x y)) φ (τ y F).1 1 1 1 := by
    intro x y
    rw [d1, d2, val_move]
    have m1 : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (Q.gl₀ a, Q.gl₁ x) * S.s₁.om (g, h₁) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₀ a g hg, cm₁ x h₁ hh₁]
    have m2 : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (Q.gl₁ x, Q.gl₂ y) * S.s₂.om (h₁, h₂) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₁ x h₁ hh₁, cm₂ y h₂ hh₂]
    have r : rTrans (h₂ * Q.gl₂ y) f = (τ y F).1 := by
      rw [hτ]; funext z; simp only [rTrans, hFdef]; rw [mul_assoc z (Q.gl₂ y) h₂, cm₂ y h₂ hh₂]
    rw [m1, m2, r, Module.End.mul_apply, Module.End.mul_apply]
    exact _root_.GlobalTheory.QPl.LineCancel.val_om_loc D ψ hψ σ S Q _ _ hT₁' hT₂' c₁ c₂ φ _ a x y Q.Φ₁ (Φa x) Q.Φ₂ (Φb x y) rfl rfl
  have hFty : ∀ j : Q.L₂.J, τ (j : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) F = (Q.L₂.lam j : ℂ) • F := by
    intro j; apply Subtype.ext; rw [hτ, Submodule.coe_smul]; exact hTy' j
  rw [KEY, KEY]
  exact tensorVal_inv hcQ hψc hψ1 hsd Q.open₂ htri F Q.Φ₁ Q.Φ₂ Q.ty₁ Q.ty₂ hFty a x y hr hj hr' hj'
    (hval (Φa _) (Φb _ _) (τ _ F)) (hval (Φa x) (Φb x y) (τ y F))

end GlobalTheory.DblInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroPlace

section Helpers
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod.LevBack
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (framePos)
open GlobalTheory.SymBridge (IsOrd zPos)
open GlobalTheory.AdelicLatMove (finEmb finEmb_mul)
open Formalism.L2.DIV (blockTri blkOf blk2 upperLeftBlock resS oToS idS kP frGL St redFn)

variable {D : D7} {c : Comm D} {v : VCom c}

theorem red_at {PP : Formalism.L2.DIV.Pl D.host.E} (G : GLoc v) {j n : ℕ} (hr : D.R.r ≤ n)
    {e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin n} (he : IsOrd zPos e) (π : Lev.EAf D →+* G.k)
    (h1 : ∀ a, π (toEAf D a) = G.q.pr a) (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[G.k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation G.k (π s) < 1)
    (Y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : ∀ a b, ¬ FreeIx G.S.ρ a b → valuation G.k (π (Y.val (e a) (e b)) - (1 : Matrix _ _ G.k) a b) < 1) :
    Formalism.UG.bc (resS D.host.F PP) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP) Y)) := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hs := G.hs
  obtain ⟨c1, x, c2⟩ := red_of_pattern G.S (by unfold Ranks.r; omega) hr he (resS D.host.F PP)
    (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) h3 h4 Y hy
  refine ⟨c1, x, fun a b a' b' ha hb z hz => ?_⟩
  have := c2 a b a' b' ha hb (oToS D.host.F D.host.E z) ((Formalism.L2.DIV.resS_oToS PP z).trans hz)
  rwa [show (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
    (ofSplit G.q).pr (z : D.host.E) from h1 (incA D (z : D.host.E))] at this


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lev_back {cm : GlobalTheory.ChainOnto.Com D} {st : StAt (c.V 0)} {b : GA D (c.V 0)} {G : cm.Pg → GLoc v}
    (hB : GlobalTheory.LevZero.Bot cm st b G) (PP : cm.Pg) (c' : ℕ) (hc : 0 + c' = (G PP).s + 1) (x : GA D (c.V 0))
    (xk : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin c') (G PP).k)
    (hx : (ofSplit (G PP).q).IsLoc ((G PP).FY 0 c' hc) x xk)
    (hxk : xk ∈ (((G PP).S.T (Fin D.R.t)).lev 0 c' hc).J) :
    b⁻¹ * x * b ∈ levS (c.V 0) st.β st.L := by
  have hs := (G PP).hs
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  replace hL : st.L = _ := hL
  obtain ⟨a, ha⟩ := hB.com.split
  obtain ⟨e, he, hmv⟩ := (hB.loc PP).frame c' hc
  obtain ⟨π, h1, h2, h3, h4⟩ := exists_chart (G PP).q (hB.loc PP).idem
  let L := typeFrame (G PP).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 c' hc)
  obtain ⟨hyK, hyP⟩ := (pattern_iter _ _ _ (G PP).S (Fin D.R.t) 0 (L.conj.symm xk)).1 hxk
  have hmap : ∀ M : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) (AE D),
      (M.map (toEAf D)).map π = M.map (G PP).q.pr := fun M => Matrix.ext fun _ _ => h1 _
  have hγ : GeneralLinearGroup.map π (st.β⁻¹ * Lev.finE (c.V 0) (b⁻¹ * x * b) * st.β) =
      reGL e (L.conj.symm xk) := by
    rw [← conj_frame ((G PP).FY 0 c' hc) L e (GeneralLinearGroup.map π (Lev.finE (c.V 0) b * st.β))
      (GeneralLinearGroup.map π (Lev.finE (c.V 0) x)) (L.conj.symm xk) ?_ ?_]
    · rw [MonoidHom.map_mul (Lev.finE (c.V 0)), MonoidHom.map_mul (Lev.finE (c.V 0)), MonoidHom.map_inv, conj_conj,
        MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
    · have hb : (st.β.val.map (finEmb D)).map (toEAf D) = st.β.val := Matrix.ext fun _ _ => toEAf_finEmb _
      refine Eq.trans ?_ (hmv _ hb)
      refine Eq.trans ?_ (hmap _)
      rw [Matrix.map_mul, hb]
      rfl
    · rw [MulEquiv.apply_symm_apply]
      exact (hmap _).trans hx.2
  obtain ⟨Y, hY, hYv, hY1⟩ := exists_int (G PP).q π h2 (c.V 0) hst.selfDual hst.frame (t := b) hx.1 (by
    rw [hγ, mem_KO, ← map_inv]
    rw [mem_KO] at hyK
    exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
  have hall : ∀ PP' : cm.Pg, Formalism.UG.bc (resS D.host.F PP'.1) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, GlobalTheory.LevZero.Red (G PP') PP'.1 x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP'.1) Y)) := fun PP' => by
    by_cases hne : PP' = PP
    · subst hne
      refine red_at (G PP') hr he π h1 h3 h4 Y fun a₁ b₁ hab => ?_
      have e1 : π (Y.val (e a₁) (e b₁)) = (L.conj.symm xk).val a₁ b₁ := by
        rw [hYv]
        refine (congrArg (fun g : GL _ _ => g.val (e a₁) (e b₁)) hγ).trans ?_
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply]
      rw [e1]
      exact hyP a₁ b₁ hab
    · have hs' := (G PP').hs
      obtain ⟨e', he', -⟩ := (hB.loc PP').frame c' (by omega)
      obtain ⟨π', k1, -, k3, k4⟩ := exists_chart (G PP').q (hB.loc PP').idem
      refine red_at (G PP') hr he' π' k1 k3 k4 Y fun a₁ b₁ _ => ?_
      have e1 := congrArg π' (hY1 (e' a₁) (e' b₁))
      rw [RingHom.map_mul, k1, pr_other (G PP).q (G PP').q ha PP.2 PP'.2 (fun h => hne (Subtype.ext h)) (hB.loc PP).idem
        (hB.loc PP').idem, zero_mul, RingHom.map_sub] at e1
      have e2 : π' ((1 : Matrix _ _ (Lev.EAf D)) (e' a₁) (e' b₁)) = (1 : Matrix _ _ (G PP').k) a₁ b₁ := by
        change π' (if e' a₁ = e' b₁ then 1 else 0) = (if a₁ = b₁ then 1 else 0)
        by_cases h : a₁ = b₁
        · simp only [h, if_true, map_one]
        · simp only [h, e'.injective.ne h, if_false, map_zero]
      rw [← e2, ← e1, Valuation.map_zero]
      exact zero_lt_one
  change _ ∈ Lev.levG _ _ st.L
  rw [hL]
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hB.fin)
    (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G PP).q.split hx.1)) hB.fin, ?_⟩
  change Lev.finE (c.V 0) _ ∈ Formalism.L2.DIV.lev _ _ _ _
  refine ⟨Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, ⟨Y, hY⟩, fun PP' hPP' => ?_,
    fun _ h => absurd h (Finset.notMem_empty _)⟩, ?_⟩
  · rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall ⟨PP', hPP'⟩).1
  · refine (hB.grp _).2 fun PP' => ?_
    change ∃ z, GlobalTheory.LevZero.Red (G PP') PP'.1 z (upperLeftBlock hr (redFn _ PP'.1 _))
    rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall PP').2

theorem finE_mem_St {cm : GlobalTheory.ChainOnto.Com D} {st : StAt (c.V 0)} {b : GA D (c.V 0)} {G : cm.Pg → GLoc v}
    (hB : GlobalTheory.LevZero.Bot cm st b G) (g : GA D (c.V 0)) (hg : g ∈ levS (c.V 0) st.β st.L) :
    finE (c.V 0) g ∈ St st.β := by
  obtain ⟨hr', ξ, hL⟩ := hB.mem.lev
  replace hL : st.L = _ := hL
  have h1 : g ∈ GfC _ ∧ finE (c.V 0) g ∈ Formalism.L2.DIV.lev D.sp.cm (c.V 0).gram st.β st.L := hg
  rw [hL, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h1
  exact h1.2.1.2.1

theorem red_of_congr (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x x' : G.S.P.J) (g : GL (Fin D.R.r) (kP PP))
    (h : GlobalTheory.LevZero.Red G PP x' g)
    (hc : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) :
    GlobalTheory.LevZero.Red G PP x g := by
  intro a b a' b' ha hb z hz
  have h1 := h a b a' b' ha hb z hz
  have hI : GlobalTheory.StepData.IntM (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val :=
    GlobalTheory.StepData.intM_of_mem_KO (G.S.P.le_KO x'.2)
  have hM := hI.mul_maxM (GlobalTheory.StepData.mem_KOne.1 hc)
  have e : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val *
      (((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - 1) =
      (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val := by
    rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [e] at hM
  have h2 := hM a b
  rw [Matrix.sub_apply] at h2
  have e2 : (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) =
      ((x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b) +
      ((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) := by ring
  rw [e2]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h2 h1)

end Helpers

end GlobalTheory.LevZeroPlace


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LevZeroPlace.one_place : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → ∀ (PP : cm.Pg) (x : (G PP).S.P.J), ∃ m ∈ levS (c.V 0) st.β st.L, Q m ∧ (∀ hr : D.R.r ≤ (c.V 0).rank, GlobalTheory.LevZero.Red (G PP) PP.1 x (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) m)))) ∧ ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) m) = 1 := by
  intro D c v cm st b G h0 hB Q hmul hN hU PP x
  have hst : ∀ w ∈ levS (c.V 0) st.β st.L, finE (c.V 0) w ∈ St st.β := GlobalTheory.LevZeroPlace.finE_mem_St hB
  have hbes := (G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)
  have hρ : (G PP).S.ρ = D.R.rS := by have := hbes.1; have := (G PP).S.odd; omega
  have hLev := GlobalTheory.LevZeroPlace.lev_back hB PP ((G PP).s + 1) (Nat.zero_add _)
  have hv : ∀ P : cm.Pg, (G P).q.v = IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers D.host.F) P.1 :=
    fun P => (hB.loc P).under
  have horth : ∀ P P' : cm.Pg, P ≠ P' →
      ((G P).q.e + cA D (G P).q.e) * ((G P').q.e + cA D (G P').q.e) = 0 := by
    intro P P' hne
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    obtain ⟨ε', hε', hsum'⟩ := (G P').q.above
    have hvv : (G P).q.v ≠ (G P').q.v := by
      rw [hv P, hv P']
      intro h
      exact hne (Subtype.ext (GlobalTheory.LevelPlaces.injOn_under D cm hB.com P.2 P'.2 h))
    rw [hsum, hsum', ← map_mul, GlobalTheory.SingleDatum.BasePair.placeIdem_mul_eq_zero hε' hε hvv, map_zero]
  have hoff : ∀ g : GA D (c.V 0), Formalism.L2.Theta.SuppAt (G PP).q.e (c.V 0) g → b⁻¹ * g * b ∈ levS (c.V 0) st.β st.L →
      ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) (b⁻¹ * g * b)) = 1 :=
    fun g hg hl PP' hPP' hne => _root_.GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt D (G ⟨PP', hPP'⟩).k (G ⟨PP', hPP'⟩).q PP' (hB.loc ⟨PP', hPP'⟩).idem (G PP).q.e
      (horth PP ⟨PP', hPP'⟩ fun h => hne (congrArg Subtype.val h).symm) _ _ _
      (GlobalTheory.PlaceMatch.suppAt_conj' hg _) (hst _ hl)
  obtain ⟨n, γ, hnN, hnJ, hγJ, hc⟩ := _root_.GlobalTheory.SymChain.SymData.exists_N_embX_inv_mul_mem_KOne (G PP).k (G PP).s D.R.k (G PP).S x.1 x.2
  obtain ⟨hup1, hup2⟩ := _root_.GlobalTheory.LevZeroUp.upZero_N_embX (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t)
  obtain ⟨hupN, -⟩ := hup1 ⟨n, hnJ⟩ hnN
  rw [hρ] at hupN
  obtain ⟨ν, hν⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q)
    ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) (GlobalTheory.LevZeroGen.upZero (G PP).S (Fin D.R.t) n)
  obtain ⟨η, hη⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q) ((G PP).FX 0 (Nat.zero_le _))
    (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin D.R.k) (Fin D.R.t)) γ)
  have hη' := _root_.GlobalTheory.LocGrp.isLoc_embA D (G PP).k _ _ _ _ _ _ _ _ hbes η _ hη
  rw [← hup2] at hη'
  have hνl := hLev ν _ hν ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hnJ)
  have hηl := hLev _ _ hη' ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hγJ)
  have hQν := hN PP ν _ (GlobalTheory.LocFlag.mem_flagN D _ _ _ _ _ _ _ _ _ hbes ν _ hupN hν) hupN hν hνl
  have hQη := hU η (GlobalTheory.PlaceMatch.mem_GfC_of_suppAt' (G PP).q.split hη.1) hηl
  have hprod := GlobalTheory.LocGrp.isLoc_mul _ hν hη'
  rw [← map_mul] at hprod
  have e : b⁻¹ * ν * b * (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η * b) =
      b⁻¹ * (ν * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η) * b := by group
  have hl : b⁻¹ * (ν * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o η) * b ∈ levS (c.V 0) st.β st.L :=
    hLev _ _ hprod ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 (mul_mem hnJ hγJ))
  refine ⟨_, hl, e ▸ hmul _ hνl _ hηl hQν hQη, fun hr => ?_, hoff _ hprod.1 hl⟩
  exact GlobalTheory.LevZeroPlace.red_of_congr (G PP) PP.1 x ⟨_, mul_mem hnJ hγJ⟩ _
    (_root_.GlobalTheory.LevZeroFamRead.red_of_isLoc (G PP) PP.1 b st.β (hB.loc PP) hB.fin hr _ ⟨_, mul_mem hnJ hγJ⟩ hprod (hst _ hl)) hc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumFrame
section
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.CoreIdele

variable {D : D7}

theorem card_eq_of_inv {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (b : Matrix m n k) (b' : Matrix n m k) (h : b * b' = 1) (h' : b' * b = 1) : Fintype.card n = Fintype.card m := by
  have h1 : Fintype.card m ≤ Fintype.card n := by
    have := Matrix.rank_mul_le_left b b'
    rw [h, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b)
  have h2 : Fintype.card n ≤ Fintype.card m := by
    have := Matrix.rank_mul_le_left b' b
    rw [h', Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b')
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_sumFrame' (p : SplitPt D k) {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p A n) :
    ∃ β₀ : Frame p S (n ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hr : r ⬝ᵥ ζ = 1 := by
    simp only [r]
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let bE : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (o.iB *ᵥ ζ))
  let bE' : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (r ᵥ* o.qB))
  have h1 : bE' * bE = 1 := by
    simp only [bE, bE']
    rw [fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
    congr 1
    · exact o.qA_iA
    · rw [← replicateCol_mulVec, Matrix.mulVec_mulVec, o.qA_iB, Matrix.zero_mulVec]; rfl
    · rw [← replicateRow_vecMul, Matrix.vecMul_vecMul, show o.qB * o.iA = 0 from o.symm.qA_iB, Matrix.vecMul_zero]; rfl
    · ext i j
      rw [replicateRow_mul_replicateCol_apply, dotProduct_mulVec, Matrix.vecMul_vecMul,
        show o.qB * o.iB = 1 from o.symm.qA_iA, Matrix.vecMul_one, hr, Subsingleton.elim i j, Matrix.one_apply_eq]
  have hn : Fintype.card n = A.rank := by simpa using card_eq_of_inv β.b β.b' β.bb' β.b'b
  let X : Matrix (Fin A.rank ⊕ Fin 1) (n ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (n ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have hX : X' * X = 1 := by
    simp only [X, X', fromBlocks_multiply, β.b'b]; simp
  have g1 : (X' * bE'.map f) * (bE.map f * X) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bE'.map f), ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, hX]
  have hc : Fintype.card (Fin S.rank) = Fintype.card (n ⊕ Fin 1) := by
    have := o.rank_add; have := hζ.1
    simp only [Fintype.card_fin, Fintype.card_sum, hn]; omega
  have g2 : (bE.map f * X) * (X' * bE'.map f) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).2 g1
  obtain ⟨β₀, h₀⟩ := ((_root_.GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p).1 S (n ⊕ Fin 1) _ _ g2 g1
  refine ⟨β₀, ?_⟩
  rw [IsSumFrame, h₀]
  simp only [bE, X, fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  ext i (j | j) <;> rfl

theorem line_of_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (v : Pl D) (ho : OrthAt o M LA LL v) (a : AE D) :
    a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a • ratV ζ ∈ latV L LL (· = v) := by
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.FinPl.CoreIdele

theorem GlobalTheory.FinPl.CoreIdele.lineLat_idele : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ m : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a ∈ intAt D (· = x)) → ∃ LL : Lat L, IsSelfDualC L LL ∧ ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP L ζ hζ m hm
  set h := star ζ ⬝ᵥ L.gram *ᵥ ζ with hhdef
  have hh : star h = h := by
    have hG : ∀ i j, star (L.gram i j) = L.gram j i := fun i j => by
      have := congrFun (congrFun (gram_conjTranspose L) j) i
      simpa [Matrix.conjTranspose_apply] using this
    have e : star (star ζ ⬝ᵥ L.gram *ᵥ ζ) = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
      simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, hG]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    exact e
  obtain ⟨m', hoff, hon⟩ := _root_.GlobalTheory.FinPl.exists_idele_change_split D k ι p I P hP h hζ.2 hh m
  obtain ⟨𝔞, h𝔞⟩ := _root_.GlobalTheory.SeeSaw.exists_idealOfIdele D m'
  have key : ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by
    intro x hx a ha
    have h1 : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
    have h2 := (hoff x hx _ h1).1
    rw [← mul_assoc (m : AE D), Units.mul_inv, one_mul] at h2
    calc ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m'⁻¹ : (AE D)ˣ) : AE D) * ((m' : AE D) * (((m⁻¹ : (AE D)ˣ) : AE D) * a)) := by
          rw [h2]
      _ = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hloc : ∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔
      (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
    intro x a ha
    by_cases hx : P x
    · exact hon x hx a ha
    · have h1 : incA D h * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
      have h2 : cA D (m : AE D) * (incA D h * a) ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ h1
      have e : (m' : AE D) * cA D (m' : AE D) * incA D h * a = (m : AE D) * cA D (m : AE D) * incA D h * a := by
        rw [mul_assoc, mul_assoc, (hoff x hx _ h1).2, (hoff x hx _ h2).1, ← mul_assoc, ← mul_assoc]
      rw [e]
      exact hm x hx a ha
  have hsd := _root_.GlobalTheory.FinPl.SelfDualIdeal.selfDual_of_local D h 𝔞 m' h𝔞 hloc
  have hζ0 : ζ ≠ 0 := fun e => hζ.2 (by rw [e]; simp)
  refine ⟨GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 𝔞, GlobalTheory.SeeSaw.LiftModel.isSelfDualC_lineLat D L ζ hζ 𝔞 hsd, fun x hx a ha => ?_⟩
  rw [GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ0 𝔞 x a ha, h𝔞 x a ha, key x hx a ha]


open GlobalTheory.FinPl.CoreIdele GlobalTheory.SeeSaw.CoreGlue in
theorem GlobalTheory.FinPl.CoreIdele.exists_core : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (β : ∀ i, Frame (p i) B.A n) (Q : ι → Pair k n) (LA : Lat B.A), IsSelfDualC B.A LA → (∀ i, (β i).IsLat LA (Q i).lat) → (∀ i, valuation k ((p i).pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)) → ∀ m : (AE D)ˣ, (∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * a ∈ intAt D (· = x)) → (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a ∈ intAt D (· = x)) → ∃ (M : Lat B.V₀) (β₀ : ∀ i, Frame (p i) B.V₀ (n ⊕ Fin 1)), IsSelfDualC B.V₀ M ∧ (∀ i, GluedCore B M q (β i) (β₀ i) (Q i)) ∧ (∀ x, ¬ P x → ∃ LL : Lat B.L, IsSelfDualC B.L LL ∧ OrthAt B.o M LA LL x ∧ ∀ a ∈ idAt D (· = x), a • ratV B.ζ ∈ latV B.L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ x, ∀ a ∈ idAt D (· = x), a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP q n _ _ ρ B β Q LA hLA _ hnorm m hmP hmoff
  obtain ⟨LL, hLL, hline⟩ := lineLat_idele D k ι p I P hP B.L B.ζ B.line m hmoff
  obtain ⟨M₁, hM₁, horth⟩ := exists_orthSum B.o hLA hLL
  have frames : ∀ i, ∃ β₀ : Frame (p i) B.V₀ (n ⊕ Fin 1), IsSumFrame B.o B.ζ (β i) β₀ :=
    fun i => exists_sumFrame' (p i) B.o B.line (β i)
  choose β₀ hβ₀ using frames
  obtain ⟨M, hM, hlat, hoff⟩ := exists_modify hP.inj β₀ (fun i => gluedS q 1 (Q i).ker (Q i).vec)
    (fun i => by haveI := (Q i).ker_isLat; infer_instance) hM₁ I
  have glued : ∀ i, GluedCore B M q (β i) (β₀ i) (Q i) := fun i =>
    ⟨hP.unit i, hβ₀ i, hnorm i, hlat i (hP.all i)⟩
  have offP : ∀ x, ¬ P x → ∀ i, x ≠ (p i).v := fun x hx i e => hx ((hP.mem x).2 ⟨i, e⟩)
  have horthM : ∀ x, ¬ P x → OrthAt B.o M LA LL x := fun x hx y => by
    rw [hoff x (offP x hx)]
    exact horth x y
  refine ⟨M, β₀, hM, glued, fun x hx => ⟨LL, hLL, horthM x hx, hline x hx⟩, fun x a ha => ?_⟩
  by_cases hx : P x
  · obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    rw [line_of_glued hM (glued i) ha]
    have hma : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_left _ _ ha
    have := hmP _ hx _ hma
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm
  · rw [line_of_orth B.o B.ζ M LA LL x (horthM x hx) a]
    exact hline x hx a ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), IsStdChar D ψ (-1) → UnrAt s₁ p.v → UnrAt s₂ p.v → ∀ (M₀ : Lat B.V₀) (M₁ : Lat J.W₀) (M : Lat B'.V₀) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)) (P : Pair k n') (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k], IsSelfDualC B.V₀ M₀ → IsSelfDualC J.W₀ M₁ → IsSelfDualC B'.V₀ M → GluedCore B M₀ q α α₀ P → β.IsLat M₁ Q.lat → IsSumFrame B'.o B'.ζ γ γ₀ → (γ₀.IsLat M (lastKer Λ) ∨ γ₀.IsLat M (lastPair q Λ).lat) → ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ (· = p.v) Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M (· = p.v) Ξ₂ → ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0 := by
  intro D k _ _ _ _ p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL hψ hs₁ hs₂ M₀ M₁ M α α₀ β γ γ₀ P Q Λ _ hM₀ hM₁ hM hG hβ hγ hγ₀ Ξ₁ Ξ₂ hΞ₁ hΞ₂ φ hφ
  obtain ⟨χ, hχ, -, -, hcond⟩ := (_root_.GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p |>.2 ψ hψ
  have hc := hcond hG.unit
  have hVex := GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place D k p q ψ χ hc hχ
  have hV := (Classical.choose_spec hVex).2
  have hO := _root_.GlobalTheory.FinPl.overBasic D
  have h₁ := (hO k p n (n' ⊕ Fin 1) ψ hψ B.V₀ J.W₀ α₀ β M₀ M₁ hM₀ hM₁ Ξ₁ hΞ₁).2.2 hG.unit _ _ hG.lat hβ
  have hO₂ := hO k p (n'' ⊕ Fin 1) n ψ hψ J.W₀ B'.V₀ β γ₀ M₁ M hM₁ hM Ξ₂ hΞ₂
  refine (hV n n' n'' σ B J B' s₁ s₂ l vL hs₁ hs₂ α α₀ β γ γ₀ hG.sum hγ P P Q).2 Λ M₀ M₁ M₁ M Ξ₁ Ξ₁ Ξ₂ Ξ₂ h₁ ?_ φ hφ
  exact hγ₀.elim (fun h => Or.inl (hO₂.2.2 hG.unit _ _ hβ h))
    (fun h => Or.inr (hO₂.2.2 hG.unit _ _ hβ h))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrimeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime : GlobalTheory.AdForm.TwVec' := by
  first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)
end

