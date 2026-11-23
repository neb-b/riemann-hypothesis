module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionRemovesMaxMultiplicityCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_star_drop_multCells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
      Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' ≤ M ∧ MultCellsAmong H.bar q φ' M n := by
  intro E _ _ _ H q φ lab hDom hφ hφtw hlabtw hsl M n hM hmax hcells
  obtain ⟨R, hR⟩ := hcells
  obtain ⟨w, hwtw, hwc, hcov, hdrop⟩ := _root_.GlobalTheory.PolFan.OrbMark.centres_exists E H q φ lab hDom hφ hφtw hlabtw hsl M hM hmax (R 0)
  obtain ⟨ψ', hψ', hψ'tw, hsub, hstar⟩ := _root_.GlobalTheory.PolFan.exists_starSubdivision E H q φ w hDom hφ hφtw hwtw hwc
  obtain ⟨lab', hlab'tw, hsl'⟩ := _root_.GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star E H q φ lab w ψ' hDom hφ hlabtw hsl hwtw hwc hψ' hsub hstar
  obtain ⟨hmax', hc'⟩ := _root_.GlobalTheory.PolFan.starMult E H q φ lab w ψ' hDom hφ hsl hwc hdrop hψ' hsub hstar M hmax
  refine ⟨ψ', lab', hψ', hψ'tw, hlab'tw, hsl', hsub, hmax', fun k => R k.succ, ?_⟩
  intro X _ _ _ _ hX m δ hδ
  obtain ⟨hδφ, hnoc⟩ := hc' X hX m δ hδ
  obtain ⟨k, hk⟩ := hR X hX m δ hδφ
  induction k using Fin.cases with
  | zero =>
    obtain ⟨β, hβ, hp, hw1, hin⟩ := hcov X hX m δ hδφ hk
    exact absurd hw1 (hnoc β hβ hp hin)
  | succ k => exact ⟨k, hk⟩

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaIsHeckeElementLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_isHecke : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  intro X px I hX U Xg tr L hI hV hL cV i t A k hF x hx1 hx2 v Pb hPb hv Ut g hg
  show x.2 ≤ (Vc X.toD7 i).rank → ∃ α, IsHeckeAt (Vc X.toD7 i) (x.1.1.1 : Pl X.toD7.host.E) x.2 α ∧ (g : GL _ _) = finHom (Vc X.toD7 i) α⁻¹
  intro _
  obtain ⟨α₀, hα₀, hfin⟩ := GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne (Vc X.toD7 i) g
  obtain ⟨e, he⟩ := _root_.GlobalTheory.SplitEtaIdem.exists_isIdemAt_conjP Pb Ut
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Mem.UnifConj.conj_unif_isUnif Pb Ut
  have hβ := hL.is.βV i
  rw [hL.beta.1 i] at hβ
  have hdict := _root_.GlobalTheory.Mem.SDFrameStd.lamHat_iff_int (Vc X.toD7 i) (L.ΛV i) hβ
  have heps := _root_.GlobalTheory.IdemSupp.idem_mul_eq_zero v Pb e hv he
  have hC : A * k ∈ Formalism.L2.DIV.St 1 := mul_mem hF.2.1 hF.2.2.2.2.1
  have hg' : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (finHom (Vc X.toD7 i) α₀)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
    rw [hfin]; exact hg
  have hs := _root_.GlobalTheory.Mem.R3.LiftBrg.eta_suppAt (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ hv he hα₀ hg'
  have hl := _root_.GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ he heps hdict hC hα₀ hg'
  have hd := _root_.GlobalTheory.Mem.R3.LiftBrg.EtaDet.det_clause (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ (by rw [rkEq X i]; exact hx2) he heps hα₀ hg'
  rw [← hPb]
  refine ⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO X.toD7.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩
  rw [inv_inv, hfin]

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder ContDiff

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ}

theorem eventually_regAt_under {y : CxPts X.str σ} {g : X.Fn} (hg : RegAt (under y) g) :
    ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt_under (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt_under (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem CInfAt.contDiffAt_holoChart {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hy : y ∈ e.source) :
    ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  obtain ⟨W, κ, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have ho := isOpen_over e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hl := e.left_inv hy
  have hg : ContDiffAt ℝ ∞ (fun w a => ev X.str σ W (g a) (e.symm w)) (e y) :=
    contDiffAt_pi.2 fun a => (contDiffOn_real ho (he W (g a))).contDiffAt (ho.mem_nhds (mem_over e hy h₁))
  have h₆ : ContDiffAt ℝ ∞ G (fun a => ev X.str σ W (g a) (e.symm (e y))) := by
    rw [hl]; exact h₄.contDiffAt (h₂.mem_nhds h₃)
  refine (h₆.comp (e y) hg).congr_of_eventuallyEq ?_
  have := e.continuousAt_symm (e.map_source hy)
  rw [ContinuousAt, hl] at this
  exact this.eventually h₅

theorem IsMetricOn.mContDiffAt_two {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0} {O : X.X.Opens}
    {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ} (hH : IsMetricOn E O H) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) (τ : ι) :
    MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := fun i j => by
  obtain ⟨hre, him⟩ := hH.smooth y hy A hA τ i j
  have h1 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).re) (e y) :=
    (CInfAt.contDiffAt_holoChart hre he hye).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).im) (e y) :=
    (CInfAt.contDiffAt_holoChart him he hye).of_le (by norm_cast)
  have h3 : ContDiffAt ℝ 2 (fun v => ((H A (e.symm v) τ i j).re : ℂ) + ((H A (e.symm v) τ i j).im : ℂ) * Complex.I) (e y) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp _ h1).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ h2).mul contDiffAt_const)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  exact (Complex.re_add_im _).symm

theorem curvPoly_polyRep {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {E : Fr (ratOf X) m 0}
    {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    {H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ} (hH : IsMetricOn E O H)
    (hρ : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y))
    {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) :
    curvPoly (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) (e y) =
      ρ.lie (fun τ => curvPoly (fun v => H A (e.symm v) τ) (e y)) := by
  have hG2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := hH.mContDiffAt_two hy hA he hye
  have hdet : ∀ τ, (H A (e.symm (e y)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hye]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y hy A hA τ).isUnit).ne_zero
  obtain ⟨-, hc⟩ := _root_.GlobalTheory.GoodMetric.conn_curvPoly_ev ι m ρ X.dim (fun v => H A (e.symm v)) (e y) hG2 hdet
  rw [← hc]
  have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hye)
    rwa [ContinuousAt, e.left_inv hye] at this
  have heq : (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => ρ.ev (H A (e.symm v)) := by
    filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hy), ht.eventually (eventually_mem_frames hA)] with v h1 h2
    exact hρ _ h1 A h2
  simp only [curvPoly, curv_congr heq]

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.Bridge

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.GoodMetric.isGood_polyRep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (ρ : PolyRep m) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0) (O : X.X.Opens)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ),
    (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) → IsMetricOn E O H →
      (∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y)) →
        IsGood E O H → IsGood E' O H' := by
  intro F _ σ X ι _ m ρ E E' O H H' hS hH hρ hG y hy
  obtain ⟨e, S, he, hye, hS0, hSO, A, hA, c, N, hev⟩ := hG y hy
  obtain ⟨c', N', hgood⟩ := _root_.GlobalTheory.RepBound.goodBound_ev ι m ρ c N
  refine ⟨e, S, he, hye, hS0, hSO, fun _ => ρ.ev A, hS _ A hA, c', N', ?_⟩
  obtain ⟨a₀, ha₀S, ha₀⟩ := (hSO y hye).1 hy
  have hcont : ContinuousAt (fun z => e z a₀) y :=
    (EuclideanSpace.proj (𝕜 := ℂ) a₀).continuous.continuousAt.comp (e.continuousAt hye)
  have hsmall : ∀ᶠ z in 𝓝 y, ‖e z a₀‖ < Real.exp (-1) := by
    have h0 : Tendsto (fun z => e z a₀) (𝓝 y) (𝓝 0) := by
      have := hcont.tendsto
      rwa [ha₀] at this
    exact h0.norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))
  filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds (e.open_source.mem_nhds hye),
    nhdsWithin_le_nhds (eventually_mem_frames hA), nhdsWithin_le_nhds hsmall] with z hz hzO hzs hzA hzsm
  rintro ⟨⟩
  have hz2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e z) := hH.mContDiffAt_two hzO hzA he hzs
  have hdet : ∀ τ, (H A (e.symm (e z)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hzs]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef z hzO A hzA τ).isUnit).ne_zero
  have hne : e z a₀ ≠ 0 := fun h0 => ((hSO z hzs).2 ⟨a₀, ha₀S, h0⟩) hzO
  have hpos : 0 < ‖e z a₀‖ := norm_pos_iff.2 hne
  have hlt : Real.log ‖e z a₀‖ < -1 := by rw [Real.log_lt_iff_lt_exp hpos]; exact hzsm
  have h1 : 1 ≤ |Real.log ‖e z a₀‖| := by rw [abs_of_neg (by linarith)]; linarith
  have hlog : 1 ≤ ∑ a ∈ S, |Real.log ‖e z a‖| :=
    h1.trans (Finset.single_le_sum (f := fun a => |Real.log ‖e z a‖|) (fun a _ => abs_nonneg _) ha₀S)
  have hb := hgood X.dim S (fun v => H A (e.symm v)) (e z) hz2 hdet hlog hz
  refine goodBound_congr_nhds X.dim (Fin ρ.M) S c' N' _ _ (e z) ?_ hb
  have ht : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    have := e.continuousAt_symm (e.map_source hzs)
    rwa [ContinuousAt, e.left_inv hzs] at this
  filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hzO), ht.eventually (eventually_mem_frames hzA)]
    with v h1 h2
  exact (hρ _ h1 A h2).symm

theorem _root_.GlobalTheory.GoodMetric.goodChernWeil_of_goodTopChernForm :
    GlobalTheory.Published.GoodTopChernForm → GlobalTheory.Published.ChernWeilNumbers → GlobalTheory.Published.FlagPushForward → GlobalTheory.Published.GoodChernWeil := by
  intro hT hCW hP
  refine ⟨?_, hP⟩
  intro F _ σ X Y ι _ m E E' φ f gr hRef hGr O H hH hG R
  obtain ⟨J, _, ρ, a, hAlg⟩ := _root_.GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep ι m X.dim R
  obtain ⟨H₀, hH₀⟩ := _root_.GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top F σ X ι m E
  choose Eb hEbS hEbH using fun j => _root_.GlobalTheory.GoodMetric.RepBundle.exists_repBundle F X ι m (ρ j) E
  choose H' hH' hH'eq using fun j => hEbH j σ O H hH
  choose H₀' hH₀' hH₀'eq using fun j => hEbH j σ ⊤ H₀ hH₀
  choose t ht using fun j => _root_.GlobalTheory.GoodMetric.hasChernIntegral_top_of_chernWeil hCW F σ X Unit (fun _ => (ρ j).M) (Eb j) (H₀' j) (hH₀' j)
    (MvPolynomial.X ((), X.dim))
  have htO : ∀ j, HasChernIntegral (Eb j) O (H' j) (MvPolynomial.X ((), X.dim)) (t j) := fun j =>
    hT F σ X (ρ j).M (Eb j) O (H' j) (H₀' j) (hH' j)
      (isGood_polyRep F σ X ι m (ρ j) E (Eb j) O H (H' j) (hEbS j) hH (hH'eq j) hG) (hH₀' j) (t j) (ht j)

  have hdens : ∀ (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
      (H' : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => (ρ j).M) ℂ),
      IsMetricOn E O H →
      (∀ j, ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' j (fun _ => (ρ j).ev A) y () = (ρ j).ev (H A y)) →
      ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y),
        ∃ B : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn, (∀ j, B j ∈ (Eb j).S (under y)) ∧
          chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
            ∑ j, a j * chernTop (MvPolynomial.X ((), X.dim)) (fun v => H' j (B j) (c.e.symm v)) (c.e y) := by
    intro O H H' hH hH'eq y hy c hc
    obtain ⟨A, hA⟩ := E.nonempty (under y)
    refine ⟨A, hA, fun j _ => (ρ j).ev A, fun j => hEbS j _ A hA, ?_⟩
    have hcurv : ∀ j, curvPoly (fun v => H' j (fun _ => (ρ j).ev A) (c.e.symm v) ()) (c.e y) =
        (ρ j).lie (fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) := fun j =>
      curvPoly_polyRep (ρ j) hH (hH'eq j) hy hA c.holo hc
    have hhom : ∀ τ i j, ((fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) τ i j).IsHomogeneous 1 :=
      fun τ i j => by
        simp only [curvPoly, Matrix.of_apply]
        exact IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_C_mul_X _ _
    have key := hAlg _ hhom
    simp only [chernTop, chernPoly, aeval_X]
    rw [key]
    simp only [hcurv, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlinO := _root_.GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum F σ X ι m E O H R J (fun j => (ρ j).M) Eb H' (MvPolynomial.X ((), X.dim)) a t hH hH'
    (hdens O H H' hH hH'eq) htO
  have hlinT := _root_.GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum F σ X ι m E ⊤ H₀ R J (fun j => (ρ j).M) Eb H₀' (MvPolynomial.X ((), X.dim)) a t hH₀ hH₀'
    (hdens ⊤ H₀ H₀' hH₀ hH₀'eq) ht
  have hs := hCW F σ X Y ι m E E' φ f gr hRef hGr H₀ hH₀ R
  rw [hs.2.symm.trans hlinT.2]
  exact hlinO

end GlobalTheory.GoodMetric.Bridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberFormsLayerMidStepChartsConditions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.L2.Forms Formalism.L2.G Formalism.UG Matrix
open scoped TensorProduct

section Hyp

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}


set_option maxHeartbeats 2000000 in
theorem stab_iff_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hdual : SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β))
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β)
      (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Hyp

section Main


set_option maxHeartbeats 8000000 in
theorem stepTiesD_mid : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ u v hg i hi hi2
  have h1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
  let F := t.C.forms u
  let dt : GlobalTheory.Port.MemDt F :=
    ⟨fun j hj _ => GlobalTheory.Port.detTieOf t.full.1.base _, fun j _ _ β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hB : GlobalTheory.Port.BaseEx t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) := by
    obtain ⟨Cm, hC1, hC2, -⟩ := F.deC (i + 1) h1 hi2
    exact GlobalTheory.Port.baseEx_of t.g.herm u v hg _ Cm hC1 hC2 (GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dt i hi v hg)
  have hrat : ∀ β, Formalism.L2.G.Cmp.ChiRatAll ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev (w.D Z).what₂.embLL := by
    rw [GlobalTheory.Port.formsInMem_mid F dt i hi hi2]
    intro β
    obtain ⟨k, hR⟩ := (t.std u).mid (i + 1) h1 hi2
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i + 1) (le_of_succ_m hi2) _ _ _ rfl
      (F.ch (i + 1) h1 hi2) k hR
      (fun β => GlobalTheory.Port.chi_fin_of_glevH (F.glevC (i + 1) h1 hi2 β) fun a => ((w.D Z).host.g_prime a).ne_zero) β
  have hψ : GlobalTheory.Port.PsiEx (GlobalTheory.Port.formsInMem F dt i hi) (t.cmp.embW u v hg) :=
    GlobalTheory.Port.psiEx_of _ (t.cmp.embW u v hg) (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O hrat
      (GlobalTheory.Port.finMem_of F dt i hi)
  haveI : ∀ j, Finite (t.C.herm.base.Ch u j) := fun j => t.C.herm.base.ChFin u j
  let S : StepD t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) :=
    ⟨hB.choose, hB.choose_spec.2, fun β => (hψ β).choose, fun β => GlobalTheory.Port.fin_of _ β _⟩
  refine ⟨GlobalTheory.Port.formsInMem F dt i hi, GlobalTheory.Port.formsInMem_fin F dt i hi, S, ?_⟩
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ (GlobalTheory.Port.formsInMem F dt i hi).T := by
    rw [GlobalTheory.Port.memberChainForms_levelPrime_eq_member]; exact hg.2.2.2.2.2
  have hbad : ∀ w' ∈ (GlobalTheory.Port.formsInMem F dt i hi).bad,
      (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
    rw [GlobalTheory.Port.formsInMem_bad]; exact Formalism.L2.G.bad_notOver u v hg
  have hre := fun β w' => GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram
    (gramN (w.D Z) (i + 1) hi) (gramN_apply (w.D Z) (i + 1) hi) ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev w'
  refine ⟨fun β w' h x hx ha hb => ?_, fun β w' h x hx => ?_, hbad, hB.choose_spec.1, fun β => (hψ β).choose_spec,
    GlobalTheory.Port.chRat_mem (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 F dt i hi,
    GlobalTheory.Port.formsInMem_ok F dt i hi v, hT⟩
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    exact (hre β w').2.2 (fun hb' => hbad w' hb' h) hTw
      ((stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hx).2 ⟨ha, hb⟩)
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    have hl := (hre β w').1 hx
    exact (stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hl.1).1 hl

end Main

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointwiseHodge
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.PointHodge

theorem chernTop_add {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (P Q : MvPolynomial (ι × ℕ) ℝ) : chernTop (P + Q) G v = chernTop P G v + chernTop Q G v := by
  simp only [chernTop, map_add (f := _), topCoeff, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem chernTop_smul {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (r : ℝ) (P : MvPolynomial (ι × ℕ) ℝ) : chernTop (r • P) G v = r * chernTop P G v := by
  have h : ∀ Q : MvPolynomial (Fin n × Fin n) ℂ, topCoeff (r • Q) = (r : ℂ) * topCoeff Q := fun Q => by
    simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  simp only [chernTop, map_smul, h, Complex.re_ofReal_mul]
  ring

noncomputable def chernLin {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : MvPolynomial (ι × ℕ) ℝ →ₗ[ℝ] ℝ where
  toFun P := chernTop P G v
  map_add' P Q := chernTop_add G v P Q
  map_smul' r P := chernTop_smul G v r P

theorem pointwise_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), chernTop R (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL la R hR y hy c' hyc A hA
  have hD : (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
    rw [Φ.dim_eq k, _root_.GlobalTheory.CMTypeCard.card_psi_eq_half E H]
  exact _root_.GlobalTheory.GrassTop.grass_top E H Dw la R X.dim (Φ.C k).Y.dim (chernLin (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y)) hD hR
    (fun Q d hQ hd => GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim _ _ _ _ _ Q d hQ hd) (fun τ Q => (_root_.GlobalTheory.GoodMetric.chernTop_unit _ _ _ _ _ τ Q).1) (fun τ k Q hk => (_root_.GlobalTheory.GoodMetric.chernTop_unit _ _ _ _ _ τ Q).2 k hk)
    (fun τ k' Q hk => _root_.GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk)

end GlobalTheory.PointHodge
end

