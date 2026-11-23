module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfJacFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfSplitW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentKeepsLevelFunctional
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.AdaptSplit

open GlobalTheory.FinPl (latV MonoAt PrimAt ColsAt idAt intAt colMul Lat SplitPt)
open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem monoAt_of_besFrame (hU : q.UnitAA) {σ : ℕ} (B : BesLev D σ) {n : Type} [Fintype n] [DecidableEq n] {s : k}
    (hs : valuation k s = 1) (hz : valuation k ((ofSplit q).hz B) = 1) {FA : Frame k B.A.rank n}
    {F : Frame k B.V.rank (n ⊕ Fin (2 * σ + 1))} {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} (hF : (ofSplit q).IsBesFrame B s FA F)
    (hcore : (ofSplit q).IsCoreFrame B s FA F₀) {L : Lat B.V} {L₀ : Lat B.V₀} (hL : IsSelfDualC B.V L)
    (hL₀ : IsSelfDualC B.V₀ L₀) (h : IntIn q B.V F L) (h₀ : IntIn q B.V₀ F₀ L₀) : MonoAt B.d L L₀ q.v := by
  obtain ⟨-, b1, b2, b3, b4⟩ := hF
  have hxi : valuation k (ofSplit q).xi = 1 := GlobalTheory.MonoSplit.xi_unit q hU
  refine GlobalTheory.MonoSplit.monoAt_of_splitW q B.d hL hL₀
    (GlobalTheory.MonoSplit.splitW_of_frame q B.d F F₀ _ _ (fun i => ?_) (fun i => ?_)
      (fun r a => ?_) (fun l hl r => ?_) b2 b4 h h₀)
  · rw [map_mul, map_pow, hs, hxi, one_pow, mul_one]
  · rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, Valuation.map_neg, hs, hz, hxi, map_one]
    simp
  · refine (b1 r a).trans ?_
    change ((_ * _ : Matrix _ _ _).map (GlobalTheory.MonoSplit.prE q) * _ : Matrix _ _ _) r a = _
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun t _ => congrArg _ (hcore.1 t a).symm
  · refine (b3 l hl r).trans ?_
    change _ * GlobalTheory.MonoSplit.prE q _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, mul_left_comm]
    exact congrArg _ (hcore.2 t).symm

theorem line_jac (hU : q.UnitAA) {ρ : ℕ} (J : JacLev D ρ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {s hh : k}
    (hs : valuation k s = 1) (hz : valuation k hh = 1) {F₀ : Frame k J.W₀.rank n} {F : Frame k J.W.rank (n ⊕ Fin c)}
    (hF : (ofSplit q).IsJacFrame J s hh F₀ F) {L : Lat J.W} (hL : IsSelfDualC J.W L) (h : IntIn q J.W F L) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = q.v)) : colMul J.d.jX i a ∈ latV J.W L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  obtain ⟨b, m, hb, hA, hB, hC⟩ := GlobalTheory.JacFramePair.isJacFrame_pairing D k (ofSplit q) ρ J s hh n c F₀ F hF hs hz
    (GlobalTheory.MonoSplit.xi_unit q hU) i
  exact GlobalTheory.SplitLine.line_mem_latV_iff D k q J.W L _ F _ b m hL h hb hA hB hC a ha

theorem line_bes (hU : q.UnitAA) {σ : ℕ} (B : BesLev D σ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {s : k}
    (hs : valuation k s = 1) (hz : valuation k ((ofSplit q).hz B) = 1) {FA : Frame k B.A.rank n}
    {F : Frame k B.V.rank (n ⊕ Fin c)} (hF : (ofSplit q).IsBesFrame B s FA F) {L : Lat B.V} (hL : IsSelfDualC B.V L)
    (h : IntIn q B.V F L) (i : Fin (σ + 1)) (a : AE D) (ha : a ∈ idAt D (· = q.v)) :
    colMul (xLast B.d (vecB B.o B.ζ)) i a ∈ latV B.V L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · obtain ⟨m, hA, hB, hC⟩ := GlobalTheory.BesPair.besz_pairings D k (ofSplit q) σ B s n c FA F hF hs hz
    have e := GlobalTheory.SplitLine.line_mem_latV_iff D k q B.V L _ F _ s m hL h hs hA hB hC a ha
    convert e using 2
    funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.FinPl.colMul, xLast, HypDec.j0, rat, ratV, Matrix.mulVec, dotProduct, map_sum]
  · obtain ⟨b, m, hb, hA, hB, hC⟩ := GlobalTheory.BesPair.bes_cols D k (ofSplit q) σ B s n c FA F hF hs hz
      (GlobalTheory.MonoSplit.xi_unit q hU) i'
    have e := GlobalTheory.SplitLine.line_mem_latV_iff D k q B.V L _ F _ b m hL h hb hA hB hC a ha
    convert e using 2
    funext r
    simp [GlobalTheory.FinPl.colMul, xLast, HypDec.jX, rat]

theorem psiE_triv_iff (hU : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {s : AE D}
    (hs : s ∈ idAt D (· = q.v)) : (∀ o ∈ intAt D (· = q.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = q.v) := by
  obtain ⟨ψk, hk, hc⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  have hxi : valuation k (ofSplit q).xi = 1 := GlobalTheory.MonoSplit.xi_unit q hU
  have hc' : ∀ x : k, (∀ y : k, valuation k y ≤ valuation k x → ψk y = 1) ↔ x ∈ 𝒪[k] := fun x => by
    rw [hc x, Units.val_one, map_one, Valuation.mem_integer_iff]
  have half : ∀ t : AE D, (∀ o ∈ intAt D (· = q.v), psiE ψ (t * o) = 1) → q.pr t ∈ 𝒪[k] := by
    intro t ht
    by_cases h0 : q.pr t = 0
    · rw [h0]; exact zero_mem _
    refine (hc' _).1 fun y hy => ?_
    have hr : y / q.pr t ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have h1 := ht _ (hU.1 _ (sec_mem_intAt q _ hr)).1
    rw [mul_left_comm, mul_comm t, sec_mul_right, div_mul_cancel₀ _ h0] at h1
    exact Circle.ext ((hk y).trans h1)
  constructor
  · intro h
    refine (GlobalTheory.SplitLine.mem_intAt_iff_pr q hs).2 ⟨half s h, half _ fun o ho => ?_⟩
    rw [← GlobalTheory.LocBesChar.psiE_cA, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    exact h _ (GlobalTheory.JacMono.conj_intAt q ho)
  · intro h o ho
    have hb := GlobalTheory.IwaDecomp.intAt_mul' h ho
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitLine.mem_intAt_iff_pr q hb.1).1 hb
    rw [GlobalTheory.LocBesChar.psiE_supp (ofSplit q) hk ((idem_iff q _).1 hb.1), (hc' 1).2 (one_mem _) _ ?_]
    · rfl
    · rw [map_div₀, hxi, div_one, map_one]
      exact (Valuation.mem_integer_iff _ _).1 (add_mem h1 h2)

theorem primAt_of_lines (hU : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (L : Lat S)
    (h : ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = q.v), colMul d.jX i a ∈ latV S L (· = q.v) ↔ a ∈ intAt D (· = q.v)) :
    PrimAt ψ d L q.v := by
  intro i j _ s hs
  rw [psiE_triv_iff q hU hψ hs]
  constructor
  · intro H
    have hε : q.e + cA D q.e ∈ intAt D (· = q.v) :=
      ⟨sum_mem_idAt q, by
        rw [RingHom.map_add (f := _)]
        exact add_mem (e_mem_intAt q).2 (GlobalTheory.JacMono.conj_intAt q (e_mem_intAt q)).2⟩
    have h1 := (h i _ (Ideal.mul_mem_right _ _ hs)).1 (H _ ((h j _ hε.1).2 hε))
    rwa [mul_comm, (idem_iff q s).1 hs] at h1
  · intro H a ha
    have h1 : a ∈ idAt D (· = q.v) := by
      have h2 := GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX (latV_supp ha) j
      rwa [GlobalTheory.JacMono.mulVec_colMul, d.pX_jX, GlobalTheory.FinPl.colMul, Matrix.one_apply_eq, mul_one] at h2
    exact (h i _ (Ideal.mul_mem_right _ _ hs)).2 (GlobalTheory.IwaDecomp.intAt_mul' H ((h j a h1).1 ha))

end GlobalTheory.Fam.AdaptSplit


open GlobalTheory.Fam.AdaptSplit in
theorem GlobalTheory.Fam.adaptFB_of_normalFrames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (pk W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hT0 hτ hNT hζ hsd hgP htP hdis hPre hOrth hbas FY sc hFr N₁ M₁ hsdN hIntN hsdM hIntM PP hP j σ h
  obtain ⟨hsc, -, hhz, hbes, hjac, -⟩ := hFr PP hP
  have hs := (l PP hP).hs
  have hU := (l PP hP).unit
  rw [← (l PP hP).under]
  have hj1 : j + 1 + (2 * (σ + 1)) = (l PP hP).s + 1 := by omega
  have hj2 : j + 1 + 1 + (2 * σ + 1) = (l PP hP).s + 1 := by omega
  have hJ := hjac j (σ + 1) h (2 * (σ + 1)) hj1
  have hB := hbes (j + 1 + 1) σ (idx_step h) (2 * σ + 1) hj2
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes _ _ _ _ _ hB
  have hM := hIntM PP hP (j + 1 + 1) σ (idx_step h) (by omega) F₀ hF₀
  have hV := hsdN (j + 1) (by omega)
  have hV₀ := (hIs.x (j + 1) (by omega)).sd
  have hW' := hsdN (j + 1 + 1) (by omega)
  have hLJ := line_jac (l PP hP).q hU _ (hsc _) (hhz _ _ _) hJ hV (hIntN PP hP (j + 1) _ hj1)
  have hLB := line_bes (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hW' (hIntN PP hP (j + 1 + 1) _ hj2)
  refine ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hV, hV₀, hW', hsdM _ _ _, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.JacMono.monoAt_of_jacFrame (l PP hP).q hU _ hV hV₀ (hsc _) (hhz _ _ _) hJ (hIntN PP hP (j + 1) _ hj1)
      ((l PP hP).latX (j + 1) (by omega))
  · exact monoAt_of_besFrame (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hF₀ hW' (hsdM _ _ _) (hIntN PP hP (j + 1 + 1) _ hj2) hM
  · exact primAt_of_lines (l PP hP).q hU hIs.std _ _ hLJ
  · intro i b hb
    rw [hU.2, hLJ i b hb]
    exact (hLB i b hb).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfRhoLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevZeroUniq
open GlobalTheory.SplitWeil GlobalTheory.StepData

variable {D : D7} {c : Comm D} {v : VCom c} {PP : Formalism.L2.DIV.Pl D.host.E}

def rho (G : GLoc v) : 𝓞 D.host.E →+* G.k := (G.q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem rho_apply (G : GLoc v) (z : 𝓞 D.host.E) : rho G z = (ofSplit G.q).pr (z : D.host.E) := rfl

theorem rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E} (hz : z ∈ PP.asIdeal) :
    valuation G.k (rho G z) < 1 := by
  by_cases h0 : z = 0
  · subst h0; simp
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have h1 := (hid.2 z h0).1 hz
  rw [← G.q.sec_pr, ← G.q.int_iff] at h1
  change (G.q.pr.comp (incA D)) _ ∉ _ at h1
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le] at h1
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).1 h1

theorem mem_of_rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E}
    (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact zero_mem _
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (hid.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

def out (y : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E := Function.surjInv (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem mk_out (y : Formalism.L2.DIV.kP PP) : Ideal.Quotient.mk PP.asIdeal (out y) = y :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem rho_sub_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {y : Formalism.L2.DIV.kP PP} {z : 𝓞 D.host.E}
    (hz : Ideal.Quotient.mk PP.asIdeal z = y) : valuation G.k (rho G (out y) - rho G z) < 1 := by
  rw [← map_sub]
  refine rho_lt G hid (Ideal.Quotient.eq.1 ?_)
  rw [mk_out, hz]

def pos (G : GLoc v) : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r :=
  finSumFinEquiv.trans (finCongr (by have := G.hs; unfold Ranks.r; omega))

theorem pos_val (G : GLoc v) (a : Fin D.R.k ⊕ Fin (G.s + 1)) : (pos G a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
  rcases a with a | a <;> rfl

def lift (G : GLoc v) (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) G.k :=
  fun a b => rho G (out (g (pos G a) (pos G b)))

theorem lift_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) :
    MaxM (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) := by
  intro a b
  have e : (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) a b =
      rho G (out ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) (pos G a) (pos G b))) -
      rho G (if a = b then 1 else 0) := by
    simp only [Matrix.sub_apply, lift, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  refine rho_sub_lt G hid ?_
  simp only [Matrix.one_apply, (pos G).injective.eq_iff]
  split_ifs <;> simp

theorem red_iff (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    GlobalTheory.LevZero.Red G PP x g ↔ MaxM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by
  constructor
  · intro h a b
    have := h a b (pos G a) (pos G b) (pos_val G a) (pos_val G b) _ (mk_out _)
    simpa only [Matrix.sub_apply, lift, rho_apply] using this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = pos G a := Fin.ext (ha.trans (pos_val G a).symm)
    obtain rfl : b' = pos G b := Fin.ext (hb.trans (pos_val G b).symm)
    have e : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E) =
        ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) a b + (rho G (out (g.val (pos G a) (pos G b))) - rho G z) := by
      simp only [Matrix.sub_apply, lift, rho_apply]; ring
    rw [e]
    exact Valuation.map_add_lt _ (h a b) (rho_sub_lt G hid hz)

theorem intM_J (G : GLoc v) (x : G.S.P.J) : IntM (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val ∧
    IntM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹).val :=
  mem_KO.1 (G.S.P.le_KO x.2)

theorem red_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) : GlobalTheory.LevZero.Red G PP 1 1 := by
  rw [red_iff G hid]
  have := (lift_one G hid).neg
  simpa using this

theorem red_uniq (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {x x' : G.S.P.J} {g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)}
    (hx : GlobalTheory.LevZero.Red G PP x g) (hx' : GlobalTheory.LevZero.Red G PP x' g')
    (hk : x.1⁻¹ * x'.1 ∈ KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) : g = g' := by
  rw [red_iff G hid] at hx hx'
  set X := (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX
  set X' := (x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX'
  have h1 : MaxM ((X⁻¹ * X').val - 1) := mem_KOne.1 hk
  have h2 : MaxM (lift G g'.val - lift G g.val) := by
    have e : lift G g'.val - lift G g.val =
        (X.val - lift G g.val) + -(X'.val - lift G g'.val) + X.val * ((X⁻¹ * X').val - 1) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
      abel
    rw [e]
    exact (hx.add hx'.neg).add ((intM_J G x).1.mul_maxM h1)
  refine Units.ext (Matrix.ext fun a' b' => ?_)
  obtain ⟨a, rfl⟩ := (pos G).surjective a'
  obtain ⟨b, rfl⟩ := (pos G).surjective b'
  have h3 : valuation G.k (rho G (out (g'.val (pos G a) (pos G b)) - out (g.val (pos G a) (pos G b)))) < 1 := by
    rw [map_sub]; simpa only [Matrix.sub_apply, lift] using h2 a b
  have h4 := Ideal.Quotient.eq.2 (mem_of_rho_lt G hid h3)
  rw [mk_out, mk_out] at h4
  exact h4.symm

end GlobalTheory.LevZeroUniq

theorem GlobalTheory.LevZeroUniq.main : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → GlobalTheory.LevZero.Red G PP 1 1 ∧ ∀ (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → GlobalTheory.LevZero.Red G PP x' g' → x.1⁻¹ * x'.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1)) → g = g' := by
  intro D c v G PP hid
  exact ⟨GlobalTheory.LevZeroUniq.red_one G hid, fun x x' g g' hx hx' hk => GlobalTheory.LevZeroUniq.red_uniq G hid hx hx' hk⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LevGlue

theorem mem_levS_datY_single : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  intro D V β r t j hr Pg Q P χ ξ PP hPQ hPg hQ κ hκ hoff
  have hPgoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP => hoff PP' (hPg PP' hP) hSt
  have hQoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Q, PP' ≠ PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP hne => hoff PP' (fun e => hne (hQ PP' hP e)) hSt
  have hrt : Lev.finE V κ ∈ Formalism.L2.DIV.St β →
      Formalism.L2.DIV.rTup β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) (Lev.finE V κ) = 1 := by
    intro hSt
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP'.1 _) = 1
    rw [hPgoff hSt _ PP'.2]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨fun h => ?_, fun ⟨hSt, hP⟩ => ?_⟩, fun hSt => ?_⟩
  · have h' : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) := h
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h'
    obtain ⟨_, ⟨_, hSt, _, hq⟩, _⟩ := h'
    exact ⟨hSt, hq PP hPQ⟩
  · show κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B)
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    refine ⟨hκ, ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPgoff hSt PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · rw [e]
        exact hP
      · rw [hQoff hSt PP' hP' e]
        exact one_mem _
    · rw [hrt hSt]
      exact one_mem _
  · simp only [Lev.levChi]
    congr 1
    simp only [Formalism.L2.DIV.levFn]
    rw [hrt hSt, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul]
    rw [Finset.prod_eq_one (fun PP' hP' => Finset.prod_eq_one fun c _ => by
      rw [hPgoff hSt PP' hP', Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]), one_mul]
    rw [Finset.prod_eq_single_of_mem (s := (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B).Q) PP hPQ fun PP' hP hne => by
      rw [hQoff hSt PP' hP hne, Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]]
    simp [Lev.datY]

end GlobalTheory.LevGlue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedLatticeIndexZeroNormalFrameComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero


set_option maxHeartbeats 1000000 in
theorem latV_normalFrame_zero_loc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → ∀ (a : ℕ) (ha : 0 + a = G.s + 1) (Λ L : GlobalTheory.FinPl.Lat (c.V 0)), Formalism.L2.DIV.IsFrame β Λ → GlobalTheory.FinPl.Moves (c.V 0) b Λ L (· = G.q.v) → ∀ y : XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin a → G.k, (fun r => G.q.sec (((G.FY 0 a ha).β *ᵥ y) r)) ∈ GlobalTheory.FinPl.latV (c.V 0) L (· = G.q.v) ↔ (∀ z, y (Sum.inl z) ∈ 𝒪[G.k]) ∧ ∀ i : Fin a, ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k] := by
  intro D c v G PP b β hloc n hn Λ L hβ hmv y
  obtain rfl : n = G.s + 1 := by omega
  obtain ⟨e, -, hM⟩ := hloc.frame (G.s + 1) hn
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame G.q hloc.idem (c.V 0) Λ β hβ
  have hb := GlobalTheory.LocMod.liftM_map β.val
  have h1 := hM _ hb
  have h2 := hB1 _ hb
  rw [GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul] at h2
  rw [Matrix.map_mul, h2] at h1
  let ε := e.symm.trans (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hn)
  let X := (G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val
  let P := (mt (c.V 0) b).map G.q.pr
  let Pi := (mt (c.V 0) b⁻¹).map G.q.pr
  have h1' : P * B.val = X.submatrix id ε := h1
  have hPPi : P * Pi = 1 := by
    change (mt (c.V 0) b).map G.q.pr * (mt (c.V 0) b⁻¹).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, mul_inv_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hPiP : Pi * P = 1 := by
    change (mt (c.V 0) b⁻¹).map G.q.pr * (mt (c.V 0) b).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, inv_mul_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (P * B.val).submatrix id ε.symm := by
    rw [h1', submatrix_submatrix, Function.comp_id, Equiv.self_comp_symm, submatrix_id_id]
  let z := (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y
  have hw : (G.FY 0 (G.s + 1) hn).β *ᵥ y = (P * B.val) *ᵥ (z ∘ ε) := by
    have e1 : (G.FY 0 (G.s + 1) hn).β *ᵥ y = X *ᵥ z := by
      change _ = ((G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val) *ᵥ
        ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y)
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [e1, hX, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id]
  have key : (fun r => G.q.sec (((G.FY 0 (G.s + 1) hn).β *ᵥ y) r)) =
      mt (c.V 0) b *ᵥ (fun r => G.q.sec ((Pi *ᵥ ((G.FY 0 (G.s + 1) hn).β *ᵥ y)) r)) := by
    rw [GlobalTheory.Core.Mi.LatMatch.mulVec_sec_split]
    change _ = fun r => G.q.sec ((P *ᵥ (Pi *ᵥ _)) r)
    rw [mulVec_mulVec, hPPi, one_mulVec]
  rw [key, ← hmv _ (fun i => GlobalTheory.FrameGlob.sec_mem_idAt G.q _), hB2, hw, mulVec_mulVec, mulVec_mulVec]
  have hB : (B⁻¹).val * Pi * (P * B.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPiP, Matrix.one_mul, Units.inv_mul]
  rw [hB, one_mulVec]
  have hz : ∀ w, z w = (GlobalTheory.LevZeroUp.scal (Fin D.R.t) G.S.ϖ w)⁻¹ * y w := by
    intro w
    change ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val *ᵥ y) w = _
    rw [GlobalTheory.LevZeroUp.bas_inv_val, mulVec_diagonal]
  have hall : (∀ i, (z ∘ ε) i ∈ 𝒪[G.k]) ↔ ∀ w, z w ∈ 𝒪[G.k] :=
    ⟨fun h w => by simpa using h (ε.symm w), fun h i => h _⟩
  rw [hall, Sum.forall]
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun i => ?_)
  · rw [hz]
    simp [GlobalTheory.LevZeroUp.scal]
  · rw [hz]
    rfl

end GlobalTheory.LevZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentKeepsLevelFunctionalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_component_keeps_level_functional : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) b i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i →
    ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
    x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal,
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ Formalism.UG.levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v (A.K j hj b).lev.Lb →
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ (A.K j hj b).lev.Uloc (p i).v := by
  first | exact @GlobalTheory.StabFnLev.comp_mem_Uloc | exact GlobalTheory.StabFnLev.comp_mem_Uloc | (intros; apply GlobalTheory.StabFnLev.comp_mem_Uloc <;> assumption)
end

