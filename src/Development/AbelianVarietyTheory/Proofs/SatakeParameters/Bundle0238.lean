module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimes
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.TopXiInvQ

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc GlobalTheory.GO

theorem phiTopG_add {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (sharp : Bool) (i : ℕ) (hc : cOf R i = 0) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P (x + z) = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  unfold PhiTopG
  split_ifs
  · exact GlobalTheory.TopInv.PhiGS_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiG_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiQ_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ hc x z hz

theorem xiTop_invQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 _hX hPr _hsel _hg _hT hL u p Y p' x z hY hz
  have hc := hL.cst_ok
  have hm := hL.hm
  have hc0 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  obtain ⟨h1, h2⟩ := loc_of_mem_mulLat (cst := cst) hPr p p' x hz
  rw [XiTop_eq, XiTop_eq, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq0 := GlobalTheory.TopInv.qOf_ne P.1
  rw [GlobalTheory.TopInv.inFr_add]
  have hZ := h2 P
  generalize inFr (frsF sel mu p P) (frsF sel mu p' P) z = Z at hZ ⊢
  unfold topDat
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (phiTopG_add Ch mu _ (m2 + 1) hc0 P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P (hL.depthQ P) _ _ _ (fun s => ?_) fun l => ?_)
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.TopStep.castAdd_single, ← pow_one (qOf P.1 : X.E)]
    refine GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos ?_
    rw [div_eq_inv_mul]
    exact hZ s _
  · refine GlobalTheory.TopInv.atNL_int _ _ _ fun l => ?_
    rw [div_eq_inv_mul]
    exact hZ s l
  · have h3 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
    rw [← (frsF sel mu p P).apply_symm_apply (_ • _)] at h3
    replace h3 := (GlobalTheory.TopStep.frsF_mem p P _).1 h3
    rw [map_smul] at h3
    exact (mem_localization_standardLattice _ _).1 h3 l

end GlobalTheory.TopXiInvQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KFiDat

theorem termLaw_of_xi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  intro D L hT Gi Gl K Y cX ex t hX hsel hgS hTS h2S hqS hTied u μ i hi c c' γ k hγ hΞ hXi
  obtain ⟨eta, hTied⟩ := hTied
  have hok := t.seam_ok
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  set z : t.X.E := ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) with hz
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hSD' : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N (i + 1) c')) :=
    t.O_lat u μ (i + 1) c' ▸ ((t.O u μ).lat (i + 1) c').2
  obtain ⟨hzs, hzi, hprod1⟩ := _root_.GlobalTheory.DetFields.det_of_stab D t.X t.seam t.χ hok t.χ_ok _ _ hSD' γ hγ
  let eZ : Fin D.R.m → t.X.Tau → ℤ := fun j τ => (D.chTw u μ).sDiv j (t.seam.iT τ) + ((D.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (D.hc (t.seam.iT τ)).e j := by
    intro j τ
    have h1 := (D.chTw u μ).sDiv_eq j j.2 (t.seam.iT τ)
    rw [D.hcW_e] at h1
    obtain ⟨m, hm⟩ := rank_even D.R j
    have h2 : ((D.R.N j / 2 : ℕ) : ℚ) = (D.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    ring
  have hTied' : t.Ch.Tied t.glob.σ₀ (fun j τ => ((eZ j τ : ℤ) : ℚ)) t.glob.mu0 eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (D.hc (t.seam.iT τ)).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact hTied
  have hP := GlobalTheory.NormOneUnit.prod_muAt t.Ch t.sel (t.tup μ) (t.cst μ) t.glob.σ₀ eZ t.glob.mu0 eta hX t.pr_ok hsel hgS
    (_root_.GlobalTheory.ColumnField.ramificationIdxIn_eq_one D t.X t.seam hX hok) hTied' ⟨i, hi⟩ z hzs hzi
  rw [t.glob_σ] at hP
  set M := t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P z) with hMdef
  have hw0 : ∀ τ, t.X.embC t.seam.σ₀ τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have hP' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(eZ ⟨i, hi⟩ τ)) := hP
  have hM0 : M ≠ 0 := by
    rw [hP']
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hw0 τ)
  have hk : ∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) = (t.seam.σ₀ k / M) * (t.rd u μ).Xi i c c' x := by
    intro x
    have := hXi x
    field_simp
    linear_combination this
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨rank_even _ _, rank_even _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  have hSSc : ∀ P ∈ (t.rd u μ).SS, conjPrime₂ P ∉ (t.rd u μ).SS := by
    rw [hSS]
    exact _root_.GlobalTheory.BadNoConj.sall_noConj_ok t.sel (t.tup μ) hX t.pr_ok hsel (t.word u) (hTS _) hgS
  have h2q : ∀ P ∈ (t.rd u μ).SS, ((D.host.QS : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
    intro P hP
    rw [hSS] at hP
    obtain ⟨p, hp, hpP, hk⟩ := sall_nat t.sel (t.tup μ) t.pr_ok hsel (t.word u) hP
    have hp2 : p ∉ D.host.small ∧ p ≠ D.host.q := by
      rcases hk with e | ⟨j, e⟩ | hn
      · rw [e, t.T_rec]; exact ⟨UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u), D.T_ne_q u⟩
      · rw [e, t.g_rec]; exact ⟨UpperTheory.Ram.g_notMem_small D j, GlobalTheory.ShortOwnCompare.level_ne_q D j⟩
      · exact ⟨fun e => hn (h2S _ e), fun e => hn (e ▸ hqS)⟩
    have key : ∀ l : ℕ, l.Prime → l ≠ p → ((l : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
      intro l hl hlp hlP
      have hc : IsCoprime ((p : ℕ) : 𝓞 t.X.E) ((l : ℕ) : 𝓞 t.X.E) := by
        have h1 := (Nat.coprime_primes hp hl).2 (Ne.symm hlp)
        have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 t.X.E))
        simpa using h2
      obtain ⟨a, b, hab⟩ := hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (P.asIdeal.mul_mem_left a hpP) (P.asIdeal.mul_mem_left b hlP)))
    exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS D.host hp hp2.1)).symm, key _ D.host.hyp.1 hp2.2.symm⟩
  have hlev0 : 0 < (t.rd u μ).lev := by
    rw [hlev]
    exact modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos
  have key := GlobalTheory.KerLaw.thC_left_stab D t.X t.seam t.cc t.δ t.B t.χ t.cD hok t.cc_ok t.δ_ok t.χ_ok _ _ _ _ hA
    (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c') hlev0 hSSc h2q hΞ γ hγ _ hk
  have hdet : (matE t.seam γ.1).det = t.seam.iE z := by
    rw [matE]
    change ((t.seam.iE : t.X.E →+* D.host.E).mapMatrix (LinearMap.toMatrix' γ.1.toLinearMap)).det = _
    rw [← RingHom.map_det, LinearMap.det_toMatrix', hz, LinearEquiv.coe_det]
    rfl
  refine ⟨by rw [hdet]; exact (map_ne_zero _).2 hz0, t.seam.σ₀ k / M, fun w => ?_, ?_⟩
  · rw [t.O_Th]
    unfold KerRead.Th Seam.push
    refine (congrArg _ ?_).trans (key (fun τ => w (t.seam.iT τ)))
    funext τ
    refine congrArg (· * Matrix.of (w (t.seam.iT τ))) ?_
    ext a b
    simp only [matE, Matrix.map_apply]
    exact (hok.1 τ _).symm
  · show t.seam.σ₀ k = t.seam.σ₀ k / M * ∏ τ, TaylorLogMetric.embT D τ (matE t.seam γ.1).det ^ (-(D.chTw u μ).sDiv i τ)
    rw [hdet]
    have hw : ∀ τ, t.X.embC t.seam.σ₀ τ z = TaylorLogMetric.embT D (t.seam.iT τ) (t.seam.iE z) := fun τ => hok.1 τ z
    have hR : ∏ τ, TaylorLogMetric.embT D τ (t.seam.iE z) ^ (-(D.chTw u μ).sDiv i τ) =
        ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) :=
      (Fintype.prod_equiv t.seam.iT _ _ fun τ => by rw [hw]).symm
    have h1 : ∏ τ, t.X.embC t.seam.σ₀ τ z = 1 := by
      rw [← hprod1]
      exact Fintype.prod_equiv t.seam.iT _ _ fun τ => hw τ
    have hM' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) := by
      rw [hP']
      simp only [eZ]
      have e1 : ∀ τ, t.X.embC t.seam.σ₀ τ z ^ (-((D.chTw u μ).sDiv i (t.seam.iT τ) + ((D.R.N i / 2 : ℕ) : ℤ))) =
          t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) * t.X.embC t.seam.σ₀ τ z ^ (-((D.R.N i / 2 : ℕ) : ℤ)) :=
        fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
      rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]
    rw [hR, ← hM']
    field_simp

end GlobalTheory.KFiDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveLRes

theorem restricts_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) {K L Ω : Type} [Field Ω] [Field K]
    [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
    [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {O O' : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw)
    (hj' : GlobalTheory.Pst.Induces Bw') (hjj : Bw'.j = Bw.j) (hle : Bw.Kw.1 ≤ Bw'.Kw.1) {LL : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) :
    Restricts (wdPst P ι Bw h hj ρ) (wdPst P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle)) := by
  have hV' := (GlobalTheory.PstLaws.isPst_resTo_iff P ρ hle).2 hV
  haveI := hV.finite
  haveI := hV'.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV']
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv l P ι K L Ω A v v' h h' O O' Bw Bw' hj hj' hle
    (fun σ σ' hσ => weilToGK_eq Bw Bw' hjj hle h h' σ σ' hσ) LL V ρ hV
  exact _root_.GlobalTheory.AboveL.restricts_of_isFrobSS K L Ω A v v' h h' _ _ _ _ _ _ _ _ (isSmooth_wdRho P ι Bw h hj ρ)
    (isSmooth_wdRho P ι Bw' h' hj' _) (BridgeParam.isFrobSS_wdRep P ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep P ι Bw' h' hj' _) e he1 he2

theorem wdAt_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : GlobalTheory.Pst.Induces Bw), IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) → ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj' : GlobalTheory.Pst.Induces Bw'), IsPstAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) ∧ Restricts (wdAt P ι Bw h hj (r.comp (Dec (F := K) A).subtype)) (wdAt P ι Bw' h' hj' ((resTo L r).comp (Dec (F := L) A).subtype)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι P AI _ a r O _ _ _ Bw hj hr
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨S, Bw', hjj, hS, hle⟩ := exists_bridge (L := L) Bw hj L₁
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [hjj]; exact hj x
  have key : ∀ (T : FinExt l) (hT : L₁.1 ≤ T.1), mapRep (algebraMap ↥T.1 (Om l))
      ((mapRep (IntermediateField.inclusion hT).toRingHom r₁).comp (decRes A)) =
      (GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype := by
    intro T hT
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₁.2
  have hpS : IsPst P (Bw'.repE Bw'.LL ((mapRep (IntermediateField.inclusion hS).toRingHom r₁).comp (decRes A))) := by
    rw [repE_decRes Bw Bw' hjj hle]
    exact (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).2 (GlobalTheory.PstExt.isPst_enlarge P Bw hS r₁ hV₁)
  have hrL : IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) :=
    ⟨Bw'.LL, _, ⟨le_rfl, key Bw'.LL hS⟩, hpS⟩
  refine ⟨_, _, _, _, Bw', hj', hrL, ?_⟩
  obtain ⟨L₃, r₃, hm₃, hV₃, e₃⟩ := wdAt_of_isPstAt ι Bw' h' hj' hrL
  have h13 : L₁.1 ≤ (supExt L₁ L₃).1 := le_sup_left
  have h33 : L₃.1 ≤ (supExt L₁ L₃).1 := le_sup_right
  have hm₃' : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) (supExt L₁ L₃)
      (mapRep (IntermediateField.inclusion h33).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h33, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw' _ hm₃' ⟨hm₃.1.trans h33, key _ h13⟩
  rw [e₁, e₃, BridgeParam.wdPst_enlarge P ι Bw h hj h13 r₁ hV₁, BridgeParam.wdPst_enlarge P ι Bw' h' hj' h33 r₃ hV₃,
    heq, repE_decRes Bw Bw' hjj hle]
  exact restricts_wdPst P ι h h' Bw Bw' hj hj' hjj hle _ (GlobalTheory.PstExt.isPst_enlarge P Bw h13 r₁ hV₁)

end GlobalTheory.AboveLRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.SatBC

theorem normV_under_pow (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq, norm_eq]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  haveI := v.isMaximal
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨by rw [← Set.mem_singleton_iff.1 hw, HeightOneSpectrum.under_asIdeal]⟩⟩

theorem isPlaceOver_under {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 M)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K M Ω]
  exact h (algebraMap (𝓞 K) (𝓞 M) x)

end GlobalTheory.AboveL.SatBC
end

