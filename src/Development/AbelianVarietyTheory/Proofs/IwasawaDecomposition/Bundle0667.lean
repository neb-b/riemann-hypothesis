module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0666

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupFiniteIndexAtFurtherPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLocalGroup_finiteIndex_at_furtherPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  first | exact @GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex | exact GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex | (intros; apply GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagRTup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FlagOnto

theorem exists_flag_rTup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (t : TupU I U) (y : G0 L.Pg X.toD7.R.r), ∃ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
      rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) = y := by
  intro X px I hX U L hI hV hL t y
  obtain ⟨c, hc⟩ := hL.is.βX
  have hsep := GlobalTheory.ChainEquiv.places_sep L (mu0F (tuOf I U)) hL.is t
  obtain ⟨κ, -, hκP, hκr⟩ := GlobalTheory.ParahoricLift.liftsExist X.toD7.sp.X' L.βX (L.datXt t) L.ΛX _ hc hsep.1 hsep.2 y
  exact ⟨⟨(finHom X.toD7.sp.X').rangeRestrict κ, hκP, Subgroup.mem_top _⟩, hκr⟩

end GlobalTheory.Mem.R3.FlagOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHodgeMetricPeriodChartAtBoundaryPoint
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart

theorem gram_entry {m m' g : ℕ} (R : Matrix (Fin m) (Fin g) ℂ) (R' : Matrix (Fin m') (Fin g) ℂ)
    (M : Matrix (Fin g) (Fin g) ℂ) (s t : ℂ) (b : Fin m) (b' : Fin m') :
    ((s • R) * M * (t • R')ᴴ) b b' = s * star t * hermForm M (R b) (R' b') := by
  simp only [hermForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mem_openPart_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) (z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ Inner (cxOf e σ hj z) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj z
  rw [mem_ptsIn]
  exact Iff.rfl


open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in
theorem periodChart_rescale : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → 0 < r → r ≤ 1 → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (r • u) + ∑ i, (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ u : Fin n → ℂ, (∀ i : Fin a, u (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (r • u) + ∑ i, (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B u = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (r • u) := by
  intro n a ha g rk τ₀ B r hP hr hr1
  set cst : ℂ := (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log r / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hP.psd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, r • z ∈ polydisc n 1 := fun z hz k => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hr.le]
    calc r * ‖z k‖ ≤ 1 * ‖z k‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hz k
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => r • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (r : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hP.rk_le, fun j k => ?_, fun z hz => ?_, hP.psd, hP.supp, hP.toric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hP.holo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hP.symm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := hP.abelian _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hP.supp _ j k (Or.inl hj)]
  · ext j k
    have hu' : ∀ i : Fin a, tlog ((r • u) (Fin.castLE ha i)) = -Real.log r / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg hr.le,
        Real.log_mul hr.ne' (norm_ne_zero_iff.2 (hu i))]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    ring

theorem exists_hodge_period_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), y ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∃ (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)) (a : ℕ) (ha : a ≤ X.dim) (g rk : ℕ) (τ₀ : (Fin X.dim → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ (∀ z ∈ ch.source, z ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ∃ i : Fin a, ch z (Fin.castLE ha i) = 0) ∧ ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ, (∀ τ i k, DifferentiableOn ℂ (fun w => Q τ w i k) (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1)) ∧ Fintype.card (Σ τ, Fin (Dw.mult τ)) = g ∧ LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q p.1 0 p.2) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ, lieGram e U hj f₀ A₀ A z τ = Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ (ch z).ofLp)ᴴ) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ τ', τ ≠ τ' → Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ' (ch z).ofLp)ᴴ = 0) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, κ, hP, hE, hx₀, h0, hcard, hκ, hInner, hHodge⟩ :=
    _root_.GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge E H Dw l Xo c O β Y T σ U hσ hU (cxOf e σ hj y)
  obtain ⟨A, hA, r, hr, W, hWd, hWli, hWfr⟩ :=
    _root_.GlobalTheory.LieBase.exists_chart_dirs E H Dw l Xo c O β Y T F e σ C X j f f₀ Eb A₀ hj hL y n g ch₀ ex hE hx₀ h0
  obtain ⟨hn, r', ch, hr', hr'r, hr'1, hHolo, hy', hch0, hpoly, hrel⟩ :=
    _root_.GlobalTheory.LieBase.exists_holoChart_of_expChart E H Dw l Xo c O β Y T F e σ X j hj hL.1 y n g ch₀ ex hE hx₀ h0 r hr
  subst hn
  have hrel' : ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = r' • (ch z).ofLp := by
    intro z hz
    refine ⟨(hrel z hz).1, ?_⟩
    rw [(hrel z hz).2]
    try (funext k; simp [Complex.real_smul])
  obtain ⟨hP1, hY⟩ := periodChart_rescale X.dim a ha g rk τ₀ B r' hP hr' hr'1.le
  have hr'0 : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'.ne'
  have hball : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1, r' • u ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr'.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc r' * ‖u‖ ≤ r' * 1 := by gcongr
      _ < r := by linarith
  have hnz : ∀ z ∈ ch.source, Inner (cxOf e σ hj z) → ∀ i : Fin a, (ch z).ofLp (Fin.castLE ha i) ≠ 0 := by
    intro z hz hI i h
    have := ((hInner _ (hrel' z hz).1).1 hI) i
    rw [(hrel' z hz).2, Pi.smul_apply, h, smul_zero] at this
    exact this rfl
  let Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u =>
    ((Real.sqrt (κ τ) : ℝ) : ℂ) • Matrix.of fun b k => W (r' • u) ⟨τ, b⟩ k
  refine ⟨ch, a, ha, g, rk, _, B, hP1, hHolo, hy', hch0, hpoly, ?_, A, hA, Q, ?_, hcard, ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z, hInner _ (hrel' z hz).1, (hrel' z hz).2]
    simp only [Pi.smul_apply, ne_eq, not_forall, not_not]
    refine exists_congr fun i => ?_
    rw [smul_eq_zero, or_iff_right hr'.ne']
    try rfl
  · intro τ i k
    have hd := (hWd ⟨τ, i⟩ k).comp (f := fun u : Fin X.dim → ℂ => r' • u)
      ((differentiable_id.const_smul (r' : ℂ)).differentiableOn.congr fun u _ => by
        simp [Complex.real_smul, Pi.smul_def]) (fun u hu => hball u hu)
    exact (hd.const_mul ((Real.sqrt (κ τ) : ℝ) : ℂ)).congr fun u _ => by simp [Q]
  · have hW0 : (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => Q p.1 0 p.2) =
        (fun p => Units.mk0 (((Real.sqrt (κ p.1) : ℝ) : ℂ))
          (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hκ p.1)).ne') • W 0 p) := by
      funext p k
      simp [Q]
    rw [hW0]
    exact hWli.units_smul _
  · intro z hz hzO τ
    have hI : Inner (cxOf e σ hj z) := (mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z).1 hzO
    have hb : ch₀ (cxOf e σ hj z) ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
      rw [(hrel' z hz).2]; exact hball _ (hpoly z hz)
    obtain ⟨hex, hDirs⟩ := hWfr z (hrel' z hz).1 hb
    unfold lieGram
    rw [dite_eq_left hex]
    obtain ⟨hgram, -⟩ := hHodge _ (hrel' z hz).1 hI hex.choose _ (hDirs _ hex.choose_spec)
    rw [hgram τ, hY _ (hnz z hz hI), ← (hrel' z hz).2]
    ext b b'
    rw [gram_entry]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Q]
    rw [← (hrel' z hz).2]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hκ τ).le]
    rfl
  · intro z hz hzO τ τ' hττ
    have hI : Inner (cxOf e σ hj z) := (mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z).1 hzO
    have hb : ch₀ (cxOf e σ hj z) ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
      rw [(hrel' z hz).2]; exact hball _ (hpoly z hz)
    obtain ⟨hex, hDirs⟩ := hWfr z (hrel' z hz).1 hb
    obtain ⟨-, horth⟩ := hHodge _ (hrel' z hz).1 hI hex.choose _ (hDirs _ hex.choose_spec)
    rw [hY _ (hnz z hz hI), ← (hrel' z hz).2]
    ext b b'
    rw [gram_entry]
    have h1 := horth ⟨τ, b⟩ ⟨τ', b'⟩ hττ
    simp only [Matrix.zero_apply]
    rw [← (hrel' z hz).2]
    exact mul_eq_zero_of_right _ h1

end GlobalTheory.LieBase.HodgeChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicity
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Main

variable {O : Type} [CommRing O] {bar : O → O}

theorem maxMult_lt_of_among_zero {q M : ℕ} {φ : InvFun O} (hM : 1 ≤ M) (h : maxMult bar q φ ≤ M)
    (h0 : MultCellsAmong bar q φ M 0) : maxMult bar q φ < M := by
  obtain ⟨R, hR⟩ := h0
  have key : maxMult bar q φ ≤ ((M - 1 : ℕ) : ℕ∞) := by
    unfold maxMult
    refine iSup_le fun X => iSup_le fun i1 => iSup_le fun i2 => iSup_le fun i3 => iSup_le fun i4 => iSup_le fun hX =>
      iSup_le fun m => iSup_le fun δ => iSup_le fun hc => iSup_le fun hli => iSup_le fun hp => ?_
    have hle : ((cellMult bar fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) : ℕ∞) ≤ M := by
      refine le_trans ?_ h
      unfold maxMult
      exact le_iSup_of_le X <| le_iSup_of_le i1 <| le_iSup_of_le i2 <| le_iSup_of_le i3 <| le_iSup_of_le i4 <|
        le_iSup_of_le hX <| le_iSup_of_le m <| le_iSup_of_le δ <| le_iSup_of_le hc <| le_iSup_of_le hli <|
        le_iSup_of_le hp le_rfl
    have hne : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≠ M := fun he =>
      (hR X hX m δ ⟨hc, hli, hp, he⟩).elim fun k _ => k.elim0
    have hle' : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M := by exact_mod_cast hle
    exact_mod_cast (show cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M - 1 by omega)
  exact key.trans_lt (by exact_mod_cast (show M - 1 < M by omega))

end Main

theorem exists_round_lt_maxMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → maxMult H.bar q φ < ⊤ →
    2 ≤ maxMult H.bar q φ → ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧
      SimpLab H.bar q φ' lab' ∧ Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < maxMult H.bar q φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult H.bar q φ).toNat with hMdef
  have hMe : maxMult H.bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan E H q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun (𝓞 E)), IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab →
      SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M n →
      ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
        Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ := _root_.GlobalTheory.PolFan.exists_star_drop_multCells E H q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KeepLevel

open GlobalTheory.Mem GlobalTheory.Mem.Th GlobalTheory.ChainEquiv

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank}

theorem levChi_withP (P : LevelP L.Pg L.r ℂ) (p : P.H) {κ : GA D V} (hκ : IsLevelLift V β L p κ) :
    levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]

theorem eigen_of_hasType {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ} (hf : HasType V β (withP L P) f) (p : P.H) {κ : GA D V}
    (hκ : IsLevelLift V β L p κ) (h : GA D V) : ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ) := by
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2.symm ▸ p.2
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [hf κ ⟨hκ.1, hκ.2.1, hp⟩ h, levChi_withP P p hκ]
  field_simp

theorem hasType_of_eigen {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ}
    (hf : ∀ (p : P.H) κ, IsLevelLift V β L p κ → ∀ h, ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ)) :
    HasType V β (withP L P) f := by
  intro κ hκ h
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2
  have hl : IsLevelLift V β L (⟨_, hp⟩ : P.H) κ := ⟨hκ.1, hκ.2.1, rfl⟩
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [levChi_withP P _ hl, mul_right_comm, hf _ κ hl h]
  field_simp

theorem mem_mult_of_level {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {X : MMap M} (hX : X ∈ Mult θ M J χ)
    (h : ∀ v, ∀ k ∈ J', ∀ g, X v (g * k) = χ' k * X v g) : X ∈ Mult θ M J' χ' :=
  have a := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ X).1 hX
  Submodule.subset_span ⟨a.aut, a.cusp, h, a.equiv, a.cont⟩

theorem hasType_of_comm (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {f : GA D V → ℂ}
    (h1 : HasType V β (flag1L L) f) (h2 : HasType V β (flag1L L) (e f)) (hf : HasType V β (withP L P) f)
    (hc : ∀ g, e (actL V β L g f) = actL V β L g (e f)) : HasType V β (withP L P) (e f) := by
  refine IsPLevel.hasType ⟨h2, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p
  have a : actL V β L p f = ((P.chi p : ℂˣ) : ℂ) • f := funext fun h =>
    (level_action_spec h1 ⟨κ, hκ⟩ κ hκ h).trans (eigen_of_hasType hf p hκ h).symm
  exact (hc p).symm.trans ((congrArg e a).trans (e.map_smul _ f))

end General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem mem_lvlPart_iff (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) (U : R.CC t j) :
    U ∈ lvlPart R P t j ↔ ∀ p : P.H, Rel R t p j U (((P.chi p : ℂˣ) : ℂ) • U) := by
  constructor
  · intro hU p κ hκ v h
    have a : (U : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ∈ MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P))
      (levChi _ (R.βY j) (R.datYt t j P)) := (mem_multT R.θ (R.MY j) _ _ _).2 hU
    exact eigen_of_hasType (L := R.datYt t j R.triv) (P := P) (multT_value _ _ _ _ _ a v).2 p hκ h
  · intro hU
    refine mem_mult_of_level ((mem_multT R.θ (R.MY j) _ _ _).1 U.2) fun v => ?_
    exact hasType_of_eigen (L := R.datYt t j R.triv) (P := P) fun p κ hκ h => hU p κ hκ (PiTensorProduct.tprod ℂ v) h

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hr : R.grp_record) (P : LevelP R.Pg D.R.r ℂ) (t : T)
    {X : MMap (R.MY 0)} (hX : X ∈ multAt R P t 0) : postOn (R.MY 0) R.e0 X ∈ R.EEat P := by
  have h0 := multAt_le R P t 0 hX
  rw [multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 X ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (GlobalTheory.ProjectedLift.eC_conv R hr) h0
  refine ⟨mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (X v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 h0).lev v
  refine hasType_of_comm (L := R.dat0 R.triv) (P := P) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 hX).lev v) fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact (GlobalTheory.ProjComm.proj_comm R hl hr).1 g _ a0

end GlobalTheory.KeepLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridFieldHasLattices
section
open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

section Transfer

variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem fieldHas_of_same {G G₀ : GridData Lc sc} {K : Type} [Field K] {e : K →+* ℂ} (hv : G.pl.v0 = G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) (h : FieldHas G₀ e) : FieldHas G e := by
  have hS : G.pl.S0 = G₀.pl.S0 := by
    delta Places.S0
    rw [hv]
  have hd : ∀ v, G.pl.depth sc v = G₀.pl.depth sc v := fun v => by
    delta Places.depth
    rw [hv]
  refine ⟨fun i h1 h2 => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    have := hch ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact h.values _ h1 h2
  · rw [hd]
    exact h.roots v (hS ▸ hv')

theorem lamOf_of_same {G G₀ : GridData Lc sc} (hw : G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) : lamOf G = lamOf G₀ := by
  delta lamOf
  rw [hw]
  congr 1
  funext a
  exact hch a

end Transfer

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridFit_of_parts {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hp : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (h1 : Formalism.L2.Host.ValLL0 D p.R.C) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D))
    (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G :=
  ⟨h1, h2, hs, hc, hp, h3, h4⟩

end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberFormsLayer_midStep_charts_conditions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid | exact GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.stepTiesD_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerTopStepChartConditionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberFormsLayer_topStep_chart_conditions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  first | exact @GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top | exact GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top | (intros; apply GlobalTheory.Mem.Top.KerOne.CertEq.TopStep.stepTies_top <;> assumption)
end

