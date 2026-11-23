module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjVecLow

open Formalism.L2.SG.InstExistsPf

theorem lowKSub_le_sm_of_unique {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp) (τ : D.what₂.Tau)
    (hone : ∀ S S' : Submodule ℂ (M.H τ),
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S →
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S' → S = S') :
    Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V Sp M τ
  exact le_trans (sSup_le fun S' hS' => (hone S' S hS' hS).le) hSle

theorem gap_rows {D : D7} (hG : GapHyp D) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (fun i : Fin n => Formalism.MainNotions.S.epsS D.R (Fin.cast hn i))
      (fun i : Fin n => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast hn i)) (16 * (D.R.r : ℝ) ^ 19) := by
  subst hn
  have h := Formalism.L2.SG.Pf.BunD.gap_lamS D.R (D.hc τ) (h := 16 * (D.R.r : ℚ) ^ 19) (by positivity)
    (fun j hj => hG.2 τ j hj)
  intro a b hab
  have := h a b (by simpa using hab)
  push_cast at this
  simpa using this

theorem npq_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) :
    (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1 < 16 * (n : ℝ) ^ 19 := by
  have hp : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hq : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp' : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h3 : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hp' (by positivity)) hq' (by positivity) (by positivity)
    nlinarith
  have h19 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 19 := pow_le_pow_right₀ hn' (by norm_num)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 19 := one_le_pow₀ hn'
  linarith

theorem exists_conj_intertwiner_of_gap (hUq : GlobalTheory.Published.DiscreteSeriesUpqUnique) {D : D7} (hG : GapHyp D)
    (I : Formalism.MainNotions.S.AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = Formalism.MainNotions.S.lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, Formalism.MainNotions.S.IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, Formalism.MainNotions.S.IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 hUq
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (GlobalTheory.SeeInt.frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) :=
          funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => GlobalTheory.SeeInt.fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * ((GlobalTheory.SeeInt.frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.SeeInt.frP_unit D τ)]
  · intro τ
    have hone : ∀ S S' : Submodule ℂ (M0.H τ),
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S →
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S' → S = S' := by
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      haveI : CompleteSpace (M0.H τ) := (M0.ds τ).1
      have hgap : Formalism.QuantumDeterminants.GapAtLeast (M0.ε τ) (M0.lam τ) (16 * (D.R.r : ℝ) ^ 19) := by
        have e1 : M0.ε τ = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq (pl.symm τ) i
        have e2 : M0.lam τ = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by
            show lam (pl.symm τ) i = _
            exact (lam_eq (pl.symm τ) i).trans (by rw [Equiv.apply_symm_apply])
        rw [e1, e2]
        exact gap_rows hG n_eq τ
      have hr : (D.sp.Y 0).rank = D.R.r := n_eq
      have hbig : ((D.sp.Y 0).rank : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (M0.ε τ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf (M0.ε τ) : ℝ) + 1 <
          16 * (D.R.r : ℝ) ^ 19 := by
        have h1 : 1 ≤ (D.sp.Y 0).rank := by have := hG.1; omega
        exact (npq_lt (M0.ε τ) h1).trans_eq (by rw [hr])
      exact (ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap _ _ _ hHC _ hgap hbig _ _ (M0.ds τ)).2.1
    have hw : w (pl.symm τ) ∈ M0.sm τ := lowKSub_le_sm_of_unique M0 τ hone (low _).2
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

theorem conjModel_of_gap : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro _ _ hUq _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hG _ hinf _ _
  have key : (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y :=
    GlobalTheory.IotaReal.iota_real_finite_of_eq R.θ hinf X.B.I h X.ιE X.pl X.φ_eq hιE
  obtain ⟨-, hreal, -⟩ := key
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner_of_gap hUq hG X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.ConjVecLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.InertSatake

def transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) : SmIrr H where
  V := σ.V
  ρ := σ.ρ.comp P.symm.toMulEquiv.toMonoidHom
  smooth v := (σ.smooth v).preimage P.symm.continuous
  irred := by
    obtain ⟨h0, h⟩ := (CuspRep.isIrreducible_iff _).1 σ.irred
    refine (CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have := hW (P g) v hv
    change σ.ρ (P.symm (P g)) v ∈ W at this
    rwa [P.symm_apply_apply] at this

theorem transport_apply {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) (g : G) (v : σ.V) : (transport P σ).ρ (P g) v = σ.ρ g v := by
  change σ.ρ (P.symm (P g)) v = _
  rw [P.symm_apply_apply]

theorem isAdmissible_transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (P : G ≃ₜ* H) (σ : SmIrr G) (h : IsAdmissible σ.ρ) : IsAdmissible (transport P σ).ρ := by
  refine ⟨(transport P σ).smooth, fun K ho hc => ?_⟩
  let K' : Subgroup G := K.comap P.toMulEquiv.toMonoidHom
  show FiniteDimensional ℂ (fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K)
  have e : fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K = fixed σ.ρ K' := by
    ext x
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hx k hk
      have := hx (P k) hk
      change σ.ρ (P.symm (P k)) x = x at this
      rwa [P.symm_apply_apply] at this
    · intro hx k hk
      exact hx (P.symm k) (by change P (P.symm k) ∈ K; rwa [P.apply_symm_apply])
  rw [e]
  refine h.2 K' (ho.preimage P.continuous) ?_
  have : (K' : Set G) = P.toHomeomorph ⁻¹' (K : Set H) := rfl
  rw [this]
  exact P.toHomeomorph.isCompact_preimage.2 hc

variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ}

def conjEquiv (s : L →+* L) (b : GL (Fin n) L) (hb : cT s b.1 * 1 * b.1 = antiJ L n) :
    UJ s (1 : Matrix (Fin n) (Fin n) L) ≃ₜ* GU s n where
  toFun g := ⟨b⁻¹ * g * b, GlobalTheory.InertDoubleCoset.conj_mem_UJ s hb g.2⟩
  invFun h := ⟨b * h * b⁻¹, by simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ s (GlobalTheory.InertDoubleCoset.inv_frame s hb) h.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.InertSatake


open GlobalTheory.InertSatake in
theorem GlobalTheory.InertSatake.sph_iff_isSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  intro E _ _ _ n π w hun hns
  obtain ⟨π, rfl⟩ := AU.mk_surjective π
  show IsUnramU π.V w ↔ ∃ α, π.IsSat w α
  constructor
  · rintro ⟨φ, hφ, h0, hfix⟩
    obtain ⟨s, ϖ, q, hs, hU⟩ := _root_.GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w hun hns
    obtain ⟨e, he⟩ := _root_.GlobalTheory.DefU.Inert.locU_equiv E n w s hs hU.2.1
    obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (one_mem (GlobalTheory.LFun.KGL w (n := n)))
      (by rw [Units.val_one, cT_one])
    let P : locU n w ≃ₜ* GU s n := e.trans (conjEquiv s b hb)
    have hP : ∀ x : locU n w, ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) = b⁻¹ * cLoc w x.1 * b := fun x => by
      change b⁻¹ * (e x : GL (Fin n) _) * b = _
      rw [he]
    obtain ⟨σ0, hadm, hcomp⟩ := _root_.GlobalTheory.DefU.LocAdm.exists_admissible_comp E n π w
    obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
    obtain ⟨-, f, hf0, hfm, hf⟩ := hcomp
    let F : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
      have := congrArg Subtype.val (DFunLike.congr_fun h v)
      exact this)
    have htop := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π.V σ0.V σ0.V π.rep (locU n w).subtype σ0.ρ σ0.ρ
      π.isIrreducible_rep σ0.irred σ0.irred (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ0.ρ σ0.irred
      (fun i : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => i.toLinearMap)
      (fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u) {x | cLoc w x.1 ∈ GlobalTheory.LFun.KGL w (n := n)} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hfix k.1 k.2 hk))
      (htop ▸ Submodule.mem_top)
    let σ1 := transport P σ0
    have hsph : GlobalTheory.LGrp.IsSpherical σ1.ρ (KU s n) := by
      refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hv0⟩
      obtain ⟨x, rfl⟩ := P.surjective k
      rw [transport_apply]
      refine hv x ?_
      have h1 : ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL (w.adicCompletion E)) :=
        (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) (P x)).1 hk
      have h2 : cLoc w x.1 = b * (P x : GL (Fin n) (w.adicCompletion E)) * b⁻¹ := by rw [hP]; group
      show cLoc w x.1 ∈ GlobalTheory.LFun.KGL w (n := n)
      rw [h2]
      exact mul_mem (mul_mem hbK h1) (inv_mem hbK)
    obtain ⟨α, hα⟩ := _root_.GlobalTheory.LFun.ExSatU.exists_hasSatU E w ϖ s q n hU σ1.V σ1.ρ σ1.irred (isAdmissible_transport P σ0 hadm) hsph
    refine ⟨α, s, ϖ, q, hs, hU, b, hbK, by have h := hb; rw [Units.val_one, Matrix.mul_one] at h; exact h, P.toMulEquiv.toMonoidHom, hP, σ1,
      ⟨σ1.irred, f, hf0, hfm, fun x u => ?_⟩, hα⟩
    change f (σ0.ρ (P.symm (P x)) u) = _
    rw [P.symm_apply_apply]
    exact hf x u
  · rintro ⟨α, s, ϖ, q, hs, hU, b, hbK, hb, p, hp, σ, ⟨-, f, hf0, hfm, hf⟩, hsat⟩
    obtain ⟨e, he⟩ := _root_.GlobalTheory.DefU.Inert.locU_equiv E n w s hs hU.2.1
    have hb1 : cT s b.1 * 1 * b.1 = antiJ _ n := by rwa [Matrix.mul_one]
    have hsurj : Function.Surjective p := fun g => by
      let P := e.trans (conjEquiv s b hb1)
      have hP : ((P (P.symm g) : GU s n) : GL (Fin n) (w.adicCompletion E)) =
          b⁻¹ * cLoc w (P.symm g).1 * b := by
        change b⁻¹ * (e _ : GL (Fin n) _) * b = _
        rw [he]
      refine ⟨P.symm g, Subtype.ext ?_⟩
      rw [hp, ← hP, P.apply_symm_apply]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have hfv : f v ≠ 0 := by
      intro h
      have hker := ((CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) fun g u hu => by
        obtain ⟨x, rfl⟩ := hsurj g
        rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hu, map_zero]
      rcases hker with h1 | h1
      · have m : v ∈ LinearMap.ker f := LinearMap.mem_ker.2 h
        rw [h1] at m
        exact hv0 ((Submodule.mem_bot ℂ).1 m)
      · exact hf0 (LinearMap.ker_eq_top.1 h1)
    refine ⟨f v, hfm v, hfv, fun x hx hk => ?_⟩
    have hpk : p ⟨x, hx⟩ ∈ KU s n := by
      refine (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) _).2 ?_
      show ((p ⟨x, hx⟩ : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL _)
      rw [hp]
      exact mul_mem (mul_mem (inv_mem hbK) hk) hbK
    refine (hf ⟨x, hx⟩ v).symm.trans ?_
    rw [GlobalTheory.LGrp.mem_fixed.1 hv _ hpk]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigensystemCarriedByFiniteTypeOfMeetsLevelRows
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCarry

theorem inner_eq_zero_of_normal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H →ₗ[ℂ] H) (hT : Commute T (LinearMap.adjoint T)) {a b : ℂ} (hab : a ≠ b) {x y : H}
    (hx : T x = a • x) (hy : T y = b • y) : ⟪x, y⟫_ℂ = 0 := by
  set S : H →ₗ[ℂ] H := T - b • LinearMap.id with hS
  have hSy : S y = 0 := by simp [hS, hy]
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ b) • LinearMap.id := by
    rw [hS, map_sub, LinearEquiv.map_smulₛₗ, LinearMap.adjoint_id]
  have hSc : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    have h1 : Commute T (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) := (Commute.one_right T).smul_right _
    have h2 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (LinearMap.adjoint T) := (Commute.one_left _).smul_left _
    have h3 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) :=
      ((Commute.one_left _).smul_left _).smul_right _
    exact (hT.sub_right h1).sub_left (h2.sub_right h3)
  have hSa : LinearMap.adjoint S y = 0 := by
    have h0 : ⟪LinearMap.adjoint S y, LinearMap.adjoint S y⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      have : S (LinearMap.adjoint S y) = LinearMap.adjoint S (S y) := by
        have := congrArg (fun f : H →ₗ[ℂ] H => f y) hSc.eq
        simpa [Module.End.mul_apply] using this
      rw [this, hSy, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 h0
  have hTa : LinearMap.adjoint T y = (starRingEnd ℂ b) • y := by
    have := hSa
    rw [hSadj, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have key : ⟪T x, y⟫_ℂ = ⟪x, LinearMap.adjoint T y⟫_ℂ := (LinearMap.adjoint_inner_right T x y).symm
  rw [hx, hTa, inner_smul_left, inner_smul_right] at key
  have hne : starRingEnd ℂ a ≠ starRingEnd ℂ b := fun h => hab ((starRingEnd ℂ).injective h)
  have : (starRingEnd ℂ a - starRingEnd ℂ b) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

theorem twSub_iSup {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (V : I → Submodule ℂ E) :
    Tw.sub s (⨆ p, V p) = ⨆ p, Tw.sub s (V p) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun p x hx => Submodule.mem_iSup_of_mem (p := V) p hx)
  exact Submodule.iSup_induction V (motive := fun y => Tw.mk s y ∈ ⨆ p, Tw.sub s (V p)) hx
    (fun p y hy => Submodule.mem_iSup_of_mem p hy) (zero_mem _) fun y z hy hz => add_mem hy hz

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem carries_of_eq (R : RealDat3 D A3 Ks) (p : A3.fam3.base3.Ix) {c c' : Pl D.host.E → List ℤ → ℂ}
    (heq : R.EEc c' = R.EEc c) (h : R.Carries p c') : R.Carries p c := by
  have key : ∀ V W : Submodule ℂ R.HE.H, V = W →
      (V ≠ ⊥ ∧ V.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) →
      (W ≠ ⊥ ∧ W.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) := by
    rintro V W rfl hV; exact hV
  exact key _ _ heq h

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry


set_option maxHeartbeats 1000000 in
theorem carried : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost c b x hx0 hxc hxb
  by_contra hno
  push_neg at hno
  obtain ⟨hcore, hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hP.char
  obtain ⟨h, -, hN, -, hev, hchar⟩ := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 (hcore hHo.aux.ex)
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCu R.toRealDat) R.SF hSF

  have heig : ∀ c' (y : R.HE.H), y ∈ R.EEc c' → ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P →
      GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) y = c' P (dualLab d) • y := by
    intro c' y hy P d hG hL
    rw [hEEc c'] at hy
    rw [hev c' P hG (Finsupp.single d 1) y hy]
    congr 1
    simp [GlobalTheory.Hk3.evC, Finsupp.sum_single_index, hL]

  have horth : ∀ c', R.EEc c' ≠ R.EEc c → R.EEc c' ≤ (ℂ ∙ x)ᗮ := by
    intro c' hne y hy
    have hex : ∃ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ GlobalTheory.Hk3.IsLab (Yc D 0) P d ∧
        c' P (dualLab d) ≠ c P (dualLab d) := by
      by_contra hall
      push_neg at hall
      apply hne
      ext z
      constructor
      · intro hz
        rw [hEEc c]
        exact hchar c z fun P d hG hL => by rw [heig c' z hz P d hG hL, hall P d hG hL]
      · intro hz
        rw [hEEc c']
        exact hchar c' z fun P d hG hL => by rw [heig c z hz P d hG hL, hall P d hG hL]
    obtain ⟨P, d, hG, hL, hcc⟩ := hex
    have hT : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) := by
      rw [hN.2 P hG]
      exact hN.1 P P hG hG _ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := inner_eq_zero_of_normal _ hT hcc (heig c' y hy P d hG hL) (heig c x hxc P d hG hL)
    rw [← inner_conj_symm, this, map_zero]

  have hpart : ∀ p, R.EEp3 p ≤ (ℂ ∙ x)ᗮ := by
    intro p
    unfold RealDat3.EEp3
    refine iSup₂_le fun c' hc' => horth c' fun heq => hno p ?_
    exact carries_of_eq R p heq hc'

  have hxT : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈ (R.toCx3 F).EEl b := hxb
  rw [← (hHo.prim.sumE b).2] at hxT
  have hxS : x ∈ ⨆ p, R.EEp3 p := by
    have h1 : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
      rw [twSub_iSup]
      have hle : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤
          ⨆ p, Tw.sub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 p) := iSup_mono fun p => inf_le_left
      exact hle hxT
    exact h1
  have hself : x ∈ (ℂ ∙ x)ᗮ := (iSup_le hpart) hxS
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hself
  exact hx0 (inner_self_eq_zero.1 hself)

end GlobalTheory.Mem.R3.LabCarry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeGStatement
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram : ∀ (m r : ℕ) (x : Fin m → Fin r → ℂ), (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef →
    IsNegSq (curv (domGram m r) x) r := by
  first | exact @GlobalTheory.PointFormSign.curv_domGram_isNegSq | exact GlobalTheory.PointFormSign.curv_domGram_isNegSq | (intros; apply GlobalTheory.PointFormSign.curv_domGram_isNegSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  first | exact @GlobalTheory.Mem.LiftFin.lift_zfin | exact GlobalTheory.Mem.LiftFin.lift_zfin | (intros; apply GlobalTheory.Mem.LiftFin.lift_zfin <;> assumption)
end

