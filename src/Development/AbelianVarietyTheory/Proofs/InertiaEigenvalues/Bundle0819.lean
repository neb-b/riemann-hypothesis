module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCard
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.VacTransOrth

theorem vacuumTranslates_conjHalf_sq_norm_eq_card_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y hY hYd μ 𝓕 hμ
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hψ, hf⟩ := hP
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hSV hSW
  have hc0 : infPart D (cA D eT) = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hT
  have hfin : ∀ y ∈ Y, y.map (infPart D) = 0 := fun y hy => by
    ext i j
    show infPart D (y i j) = 0
    rw [← hY y hy i j, RingHom.map_mul, hc0, zero_mul]
  have h := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ V W hψ.1 μ 𝓕 hμ f₀ hf.theta (hf.norm.2 (μ, 𝓕) hμ) (WO V W) Y id
    (fun _ => 1) (fun _ _ => norm_one) ?_
  · simpa only [one_smul, id] using h
  intro y hy y' hy' hne
  have hnot : y - y' ∉ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) :=
    fun hm => hne (hYd y hy y' hy' hm)
  have hm0 : (y - y').map (infPart D) = 0 := by
    ext i j
    have h1 : infPart D (y i j) = 0 := congrFun (congrFun (hfin y hy) i) j
    have h2 : infPart D (y' i j) = 0 := congrFun (congrFun (hfin y' hy') i) j
    show infPart D (y i j - y' i j) = 0
    rw [RingHom.map_sub, h1, h2, sub_zero]
  rw [hd _ hm0] at hnot
  push_neg at hnot
  obtain ⟨l, hl, hne'⟩ := hnot
  obtain ⟨ε, hε, hεf⟩ := hsign f₀ hf.lat l hl
  exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f₀ hf.lat, hne'⟩

end GlobalTheory.VacTransOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.GoodModUnr

open GlobalTheory.IdemSupport

variable {D : D7}

theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} {χ : (AE D)ˣ →* Circle} (h : GlobalTheory.Hk3.UnrPl w χ) :
    GlobalTheory.LFun.UnrAt χ w := by
  intro u hu
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  have hd := (of_isPrimeIdem hΦ hp).1
  have hee : e * e = e := delta_idem hΦ hd
  have hfe : f * e = e := by
    rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
    · have ho : e * cA D e = 0 := hi.1.2.1
      linear_combination hee + ho
    · exact hee
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w u).1 hu
  have hg : e * ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) + (1 - e) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) :=
    GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd (GlobalTheory.LFun.EulerTie.finComp_locIdele_self w u)
  have hx : f * (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1 := by
    linear_combination (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) * hfe + (1 - f) * hg
  have i1 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u).2 h1
  have i2 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u⁻¹).2 h2
  rw [map_inv] at i2
  have := h e f hp _ hx i1 i2
  exact (congrArg Circle.toUnits this).trans (map_one _)

theorem good_of_ne {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) (hv : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.Hk3.Good R t w := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  intro PP hPP
  have key : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro hu
    obtain ⟨e, f', hp⟩ := exists_isPrimeIdem hΦ PP
    obtain ⟨-, ε, hε, hf'⟩ := of_isPrimeIdem hΦ hp
    obtain ⟨ε', hε', rfl⟩ := hf
    rw [hu] at hε
    exact hv PP hPP e f' hp (by rw [hf', placeIdem_unique hε hε'])
  refine ⟨fun h => key (h ▸ hw), fun h => key ?_⟩
  rw [← hw, (isConjPl_iff PP w).1 h, under_cP]

theorem chrTh_unrAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hv w hw
  obtain ⟨he, hm⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hL.lev t w (good_of_ne R t hf hv hw)
  have a := unrAt_of_unrPl (hm ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega))
  have b := unrAt_of_unrPl he
  exact ⟨a, a.mul b.inv⟩

end GlobalTheory.GoodModUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorInvCentralFlipInvariantFormEq
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.FlipScalStep

def flipInv {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * incA D ((m : D.host.E)⁻¹) + cA D e * (m : AE D) + (1 - e - cA D e)

theorem flipElt_mul_flipInv {D : D7} {e : AE D} (he : IsSplitIdem D e) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * flipInv e m = 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hmE, map_one]
  unfold flipElt flipInv
  linear_combination (e + cA D e) * hinc
    + ((m : AE D) * incA D ((m : D.host.E)⁻¹) - m - incA D ((m : D.host.E)⁻¹) + 1) * (hee + hcc)
    + ((m : AE D) ^ 2 - 2 * m + incA D ((m : D.host.E)⁻¹) ^ 2 - 2 * incA D ((m : D.host.E)⁻¹) + 2) * hec

theorem mt_inv_eq {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.mt V g⁻¹ = flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hmul : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hfb : (flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) *
      (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, flipElt_mul_flipInv he hm, one_smul]
  calc Formalism.L2.Theta.mt V g⁻¹ = Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g *
        (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))) := by rw [hg, hfb, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hmul, Matrix.one_mul]

theorem mul_flipInv_sub {D : D7} {e : AE D} (he : IsSplitIdem D e) (m : ℕ) :
    (e + cA D e) * (flipInv e m - 1) = flipInv e m - 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  unfold flipInv
  linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hcc
    + ((m : AE D) + incA D ((m : D.host.E)⁻¹) - 2) * hec

theorem idem_mul_flipInv_pow {D : D7} {e : AE D} (he : IsSplitIdem D e) (m n : ℕ) :
    e * flipInv e m ^ n = e * incA D ((m : D.host.E)⁻¹) ^ n := by
  obtain ⟨hee, hec, -⟩ := he
  have heb : e * flipInv e m = e * incA D ((m : D.host.E)⁻¹) := by
    unfold flipInv
    linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hec
  induction n with
  | zero => rfl
  | succ n ih =>
    linear_combination flipInv e m * ih + incA D ((m : D.host.E)⁻¹) ^ n * heb

theorem suppAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.SuppAt e V g⁻¹ := by
  intro i j
  rw [mt_inv_eq V g e he hm hg, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc (e + cA D e) * (flipInv e m * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j -
        (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      = ((e + cA D e) * (flipInv e m - 1)) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by ring
    _ = _ := by rw [mul_flipInv_sub he m]; ring

theorem isDetAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    {x : (AE D)ˣ} (hx : IsFlipDet V e m x) : Formalism.L2.Theta.IsDetAt e V g⁻¹ x := by
  unfold Formalism.L2.Theta.IsDetAt
  rw [mt_inv_eq V g e he hm hg, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    idem_mul_flipInv_pow he m]
  unfold IsFlipDet at hx
  have hee := he.1
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ hmE, map_one]
  have hpow : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
    rw [← mul_pow, hinc, one_pow]
  have hy : (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1 := by
    linear_combination (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hee + e ^ 2 * hpow
  linear_combination (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * hx - (x : AE D) * hy

theorem om_inv_flip_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW P e m g x ℓ hP hm hg hx hℓ
  have he : IsSplitIdem D e := hP.1
  have hm1 : Formalism.L2.Theta.mt W (1 : GA D W) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : Formalism.L2.Theta.SuppAt e W 1 := fun i j => by rw [hm1, sub_self, Matrix.zero_apply, mul_zero]
  have h1' : Formalism.L2.Theta.IsDetAt e W 1 1 := by
    unfold Formalism.L2.Theta.IsDetAt
    rw [hm1, Matrix.det_one, mul_one, add_sub_cancel, Units.val_one]
  obtain ⟨r, hr, H⟩ := hW.om_split e he g⁻¹ 1 (suppAt_inv V g e he hm hg) h1 x 1 (isDetAt_inv V g e he hm hg hx) h1'
  refine ⟨r, hr, fun f hf => ?_⟩
  rw [H ℓ (fun u hu f hf => hℓ u hu f hf) f hf, splitFacO, map_one, mul_one, Circle.coe_inv]

end GlobalTheory.LevelSeries.FlipScalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationPreservesNorm
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.WeilUnitNorm

open MeasureTheory

theorem weil_norm_one_of_unit_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : MeasureTheory.Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (p : GA D S × GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → nrm2 μ 𝓕 f = 1 → nrm2 μ 𝓕 (om p f) = 1 := by
  intro D ψ S T χS χT om hW μ 𝓕 hC p f hf h1
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have key := hW.om_unit μ 𝓕 hC.1 hC.2.1 p f hf
  have hf' := hW.om_pres p f hf
  have m1 : AEStronglyMeasurable (fun w => ‖om p f w‖ ^ 2) (μ.restrict 𝓕) :=
    (hf'.cont.norm.pow 2).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun w => ‖f w‖ ^ 2) (μ.restrict 𝓕) :=
    (hf.cont.norm.pow 2).aestronglyMeasurable
  have e : nrm2 μ 𝓕 (om p f) = nrm2 μ 𝓕 f := by
    unfold nrm2
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) m1,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) m2]
    congr 1
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    exact key
  rw [e, h1]

end GlobalTheory.WeilUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Growth (F : GA E a → ℂ) : Prop :=
  ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

def Good (F : GA E a → ℂ) : Prop :=
  ∃ h : F ∈ Sm E a, ∀ l : List (Lie E a),
    GlobalTheory.ShortVecDecay.Decays (GlobalTheory.GLFin.word l ⟨F, h⟩).1 ∧ Growth (GlobalTheory.GLFin.word l ⟨F, h⟩).1


theorem Growth.zero : Growth (0 : GA E a → ℂ) := fun _ => ⟨0, 0, fun _ => by simp⟩

theorem Growth.add {F G : GA E a → ℂ} (hF : Growth F) (hG : Growth G) : Growth (F + G) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  obtain ⟨C', N', h'⟩ := hG g
  refine ⟨|C| + |C'|, max N N', fun y => ?_⟩
  have h1 := one_le_height y
  have p1 : height y ^ N ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_left _ _)
  have p2 : height y ^ N' ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_right _ _)
  have q : 0 ≤ height y ^ N := by positivity
  have q' : 0 ≤ height y ^ N' := by positivity
  calc ‖(F + G) (g * infGL E a y)‖ ≤ ‖F (g * infGL E a y)‖ + ‖G (g * infGL E a y)‖ := norm_add_le _ _
    _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h y) (h' y)
    _ ≤ |C| * height y ^ max N N' + |C'| * height y ^ max N N' := by
        exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C) q).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))) ((mul_le_mul_of_nonneg_right (le_abs_self C') q').trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C')))
    _ = (|C| + |C'|) * height y ^ max N N' := by ring

theorem Growth.smul {F : GA E a → ℂ} (hF : Growth F) (z : ℂ) : Growth (z • F) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  refine ⟨‖z‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem Good.mem_Sm {F : GA E a → ℂ} (h : Good F) : F ∈ Sm E a := h.1

theorem Good.decays {F : GA E a → ℂ} (h : Good F) : GlobalTheory.ShortVecDecay.Decays F := (h.2 []).1

theorem Good.growth {F : GA E a → ℂ} (h : Good F) : Growth F := (h.2 []).2

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by
  simp [GlobalTheory.GLFin.word, Module.End.mul_apply]

theorem word_append_single (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.prod_append, Module.End.mul_apply]

theorem Good.derivative {F : GA E a → ℂ} (h : Good F) (X : Lie E a) : Good (lieD X F) := by
  obtain ⟨hF, hl⟩ := h
  refine ⟨lieD_mem_Sm X hF, fun l => ?_⟩
  have e : (⟨lieD X F, lieD_mem_Sm X hF⟩ : Sm E a) = lie E a X ⟨F, hF⟩ := rfl
  rw [e, ← word_append_single]
  exact hl _

theorem good_zero : Good (0 : GA E a → ℂ) := by
  refine ⟨zero_mem _, fun l => ?_⟩
  have e : (⟨0, zero_mem _⟩ : Sm E a) = 0 := rfl
  rw [e, map_zero]
  exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩

theorem Good.add {F G : GA E a → ℂ} (hF : Good F) (hG : Good G) : Good (F + G) := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  refine ⟨add_mem hF1 hG1, fun l => ?_⟩
  have e : (⟨F + G, add_mem hF1 hG1⟩ : Sm E a) = ⟨F, hF1⟩ + ⟨G, hG1⟩ := rfl
  rw [e, map_add (f := _), Submodule.coe_add]
  exact ⟨(hF2 l).1.add (hG2 l).1, (hF2 l).2.add (hG2 l).2⟩

theorem Good.smul {F : GA E a → ℂ} (hF : Good F) (z : ℂ) : Good (z • F) := by
  obtain ⟨hF1, hF2⟩ := hF
  refine ⟨Submodule.smul_mem _ z hF1, fun l => ?_⟩
  have e : (⟨z • F, Submodule.smul_mem _ z hF1⟩ : Sm E a) = z • ⟨F, hF1⟩ := rfl
  rw [e, map_smul, Submodule.coe_smul]
  exact ⟨(hF2 l).1.smul z, (hF2 l).2.smul z⟩

theorem good_of_mem {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) : Good φ.1 :=
  ⟨φ.2, fun l => ⟨GlobalTheory.ShortVecDecay.decays_of_mem hπ (GlobalTheory.ShortVecDecay.word_mem l hφ),
    (π.cusp _ (GlobalTheory.ShortVecDecay.word_mem l hφ)).1.growth⟩⟩

end GlobalTheory.MSpanDecay
end
end

