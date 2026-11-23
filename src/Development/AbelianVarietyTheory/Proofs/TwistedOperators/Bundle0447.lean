module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdResidueFunctionsHalfSumIdempotents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.StepVec

theorem frMapO_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (c : AE D) (t : WO S T) :
    frMapO S T βS βT (c • t) = toEAf D c • frMapO S T βS βT t := by
  have hm : ((c • t : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) =
      toEAf D c • (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) := by
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  simp only [frMapO]
  rw [hm, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_locFn_half : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (s : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D),
    (∀ PP ∈ s, Formalism.L2.NTheta.IsIdemAt (es PP) PP) →
    ∀ (ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) (t : WO S T),
      IsHalf (∑ PP ∈ s, es PP) t →
      (open Classical in (if IsIntM (frMapO S T βS βT t) then ∏ PP ∈ s, ω PP (redM PP (frMapO S T βS βT t)) else 0)) =
        ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t) := by
  intro D S T βS βT s es hid ω t hhalf
  classical
  have hint : ∀ PP ∈ s, ∃ h : toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP), h⟩ = 1 :=
    fun PP hPP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hid PP hPP)
  have hhalfPP : ∀ PP ∈ s, IsHalf (es PP) (es PP • t) := by
    intro PP hPP i j
    have he : es PP * es PP = es PP := (hid PP hPP).1.1
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
  simp only [locFn]
  split_ifs with hN
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    obtain ⟨hi, h1⟩ := hint PP hPP
    have hN' : IsIntM (frMapO S T βS βT (es PP • t)) := by
      intro i j
      rw [frMapO_smul, Matrix.smul_apply, smul_eq_mul]
      exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem hi (hN i j)
    rw [if_pos ⟨hhalfPP PP hPP, hN'⟩]
    congr 1
    funext i j
    have hmem : (frMapO S T βS βT (es PP • t)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := hN' i j
    simp only [redM, dif_pos (hN i j), dif_pos hmem]
    have heq : (⟨(frMapO S T βS βT (es PP • t)) i j, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        ⟨toEAf D (es PP), hi⟩ * ⟨(frMapO S T βS βT t) i j, hN i j⟩ := by
      apply Subtype.ext
      simp only [Subring.coe_mul, frMapO_smul, Matrix.smul_apply, smul_eq_mul]
    rw [heq, map_mul, h1, one_mul]
  · have hex : ∃ PP ∈ s, ¬ IsIntM (frMapO S T βS βT (es PP • t)) := by
      by_contra hc
      push_neg at hc
      apply hN
      intro i j
      have ht : t = (∑ PP ∈ s, es PP) • t := by
        ext k l
        exact (hhalf k l).symm
      have hsum : frMapO S T βS βT t i j = ∑ PP ∈ s, frMapO S T βS βT (es PP • t) i j := by
        conv_lhs => rw [ht, frMapO_smul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Matrix.smul_apply, smul_eq_mul, map_sum (toEAf D), Finset.sum_mul]
        refine Finset.sum_congr rfl fun PP _ => ?_
        rw [frMapO_smul, Matrix.smul_apply, smul_eq_mul]
      rw [hsum]
      exact Subring.sum_mem _ fun PP hPP => hc PP hPP i j
    obtain ⟨PP, hPP, hni⟩ := hex
    symm
    exact Finset.prod_eq_zero hPP (if_neg fun h => hni h.2)

end GlobalTheory.StepVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

section Mono

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {S : GridChoice W Set.univ}

theorem charsIn_mono (h : CharsIn G σ) (hσ : Set.range σ ⊆ Set.range σ') : CharsIn G σ' :=
  ⟨fun j w x => hσ (h.mu0 j w x), fun t w x => hσ (h.xi t w x),
    fun i a b w x => hσ (h.chi i a b w x), fun v hv => hσ (h.eta v hv), fun v hv => hσ (h.chiPsi v hv),
    fun v hv => hσ (h.del v hv), fun v hv => hσ (h.del' v hv)⟩

theorem rootCl_mono (h : RootCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : RootCl σ' S :=
  ⟨fun z hz => hσ (h.1 z hz), fun t w hw z hz => hσ (h.2.1 t w hw z hz), fun w hw => hσ (h.2.2 w hw)⟩

theorem phaseCl_mono (h : PhaseCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : PhaseCl σ' S :=
  fun t Φ β hβ w x y e a b => hσ (h t Φ β hβ w x y e a b)

theorem jetCl_mono (h : JetCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : JetCl σ' S :=
  fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hσ ((h t Φ β hβ τ hτ d hd c).1 j a b),
    fun i a b => hσ ((h t Φ β hβ τ hτ d hd c).2 i a b)⟩

theorem lRatios_mono {μ₀ : T} (h : ∀ i j, LRatiosIn G σ μ₀ i j) (hσ : Set.range σ ⊆ Set.range σ') :
    ∀ i j, LRatiosIn G σ' μ₀ i j :=
  fun i j t Λ Λ₀ a b s c d e => hσ (h i j t Λ Λ₀ a b s c d e)

theorem botCl_mono (h : BotCl W σ) (hσ : Set.range σ ⊆ Set.range σ') : BotCl W σ' := by
  intro i j
  obtain ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, H⟩ := h i j
  exact ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, fun t g hg =>
    ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end Mono

theorem range_algebraMap_mono {M M' : IntermediateField ℚ ℂ} (h : M ≤ M') :
    Set.range (algebraMap M ℂ) ⊆ Set.range (algebraMap M' ℂ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, h x.2⟩, rfl⟩

theorem InNF.and {Q Q' : ∀ M : IntermediateField ℚ ℂ, (M →+* ℂ) → Prop}
    (hQ : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q M (algebraMap M ℂ) → Q M' (algebraMap M' ℂ))
    (hQ' : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q' M (algebraMap M ℂ) → Q' M' (algebraMap M' ℂ))
    (h : InNF Q) (h' : InNF Q') : InNF fun M σ => Q M σ ∧ Q' M σ := by
  obtain ⟨M, hM, hq⟩ := h
  obtain ⟨M', hM', hq'⟩ := h'
  exact ⟨M ⊔ M', IntermediateField.finiteDimensional_sup M M', hQ _ _ le_sup_left hq, hQ' _ _ le_sup_right hq'⟩

theorem nfAll_of : NFChars → NFRoot → NFPhase → NFJet → NFRatio → NFBot → NFAll := by
  intro h1 h2 h3 h4 h5 h6
  obtain ⟨CF0, H⟩ := Big.and h1 (Big.and h2 (Big.and h3 (Big.and h4 (Big.and h5 h6))))
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi ha
  have k := InNF.and (fun M M' h q => charsIn_mono q (range_algebraMap_mono h))
    (fun M M' h q => rootCl_mono q (range_algebraMap_mono h)) c1 c2
  have k := InNF.and (fun M M' h q => ⟨charsIn_mono q.1 (range_algebraMap_mono h), rootCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => phaseCl_mono q (range_algebraMap_mono h)) k c3
  have k := InNF.and (fun M M' h q => ⟨⟨charsIn_mono q.1.1 (range_algebraMap_mono h), rootCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      phaseCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => jetCl_mono q (range_algebraMap_mono h)) k c4
  have k := InNF.and (fun M M' h q => ⟨⟨⟨charsIn_mono q.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => lRatios_mono q (range_algebraMap_mono h)) k c5
  have k := InNF.and (fun M M' h q => ⟨⟨⟨⟨charsIn_mono q.1.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.1.2 (range_algebraMap_mono h)⟩, lRatios_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => botCl_mono q (range_algebraMap_mono h)) k c6
  obtain ⟨M, hM, ⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩⟩ := k
  exact ⟨M, hM, ⟨q1, q2, q3, q4, q5, q6⟩⟩

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainSteps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

namespace WeakSepPf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)


variable (G) in
theorem nonempty_coreVol : Nonempty (CoreVol G) := ⟨fun i => (GlobalTheory.Unf.Inhab.nonempty_vol (G.V (.core i))).some⟩

theorem rapidDec_of_rapidRow {M : Vol G} {u : GA D (Yc D 0) → ℂ} (h : RapidRow W M u) : RapidDec (Yc D 0) u :=
  h (fun _ => 0) (fun _ => default) 0 (Nat.zero_le _)

theorem rapidDec_of_reach {v : CoreVol G} {F : Fn G (.core 0)} (h : F ∈ Reach W v) : RapidDec (G.V (.core 0)) F := by
  obtain ⟨Ψ, hΨ, rfl, -⟩ := h
  exact hΨ.1 0 (Nat.zero_le _)

theorem integrableOn_corePeriod_rapidlyDecreasing {M : Vol G} (hM : M.IsRow) {F : Fn G (.core 0)}
    (hF : RapidDec (G.V (.core 0)) F) {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) :
    IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) := by
  obtain ⟨h1, h2⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨C, hC⟩ := hF.2.2 0
  exact RapidDec.integrableOn_mul_of_le (V := Yc D 0) (f := fun h => F (stabilizerEmbedding G.sp.dec0 h)) hu h1 h2
    ((hF.2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding G.sp.dec0)).aestronglyMeasurable) (C := C) (A := 0)
    fun g => by simpa using hC _

theorem exists_reach_of_span {M : Vol G} (hM : M.IsRow) {v : CoreVol G}
    {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) {F : Fn G (.core 0)} (hF : F ∈ Submodule.span ℂ (Reach W v))
    (h0 : per0 G M F u ≠ 0) : ∃ F' ∈ Reach W v, per0 G M F' u ≠ 0 := by
  by_contra hn
  push_neg at hn
  have key : IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) ∧
      per0 G M F u = 0 := by
    clear h0
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨integrableOn_corePeriod_rapidlyDecreasing hM (rapidDec_of_reach W hx) hu, hn x hx⟩
    | zero => exact ⟨by simp only [Pi.zero_apply, zero_mul]; exact integrableOn_zero, by simp [per0]⟩
    | add x y _ _ hx hy =>
      have e : (fun h => (x + y) (stabilizerEmbedding G.sp.dec0 h) * u h) =
          fun h => x (stabilizerEmbedding G.sp.dec0 h) * u h + y (stabilizerEmbedding G.sp.dec0 h) * u h := by
        funext h; simp [add_mul]
      refine ⟨e ▸ hx.1.add hy.1, ?_⟩
      have a := hx.2
      have b := hy.2
      unfold per0 at a b ⊢
      erw [e, integral_add hx.1 hy.1, a, b, add_zero]
    | smul c x _ hx =>
      have e : (fun h => (c • x) (stabilizerEmbedding G.sp.dec0 h) * u h) = fun h => c * (x (stabilizerEmbedding G.sp.dec0 h) * u h) := by
        funext h; simp [mul_assoc]
      refine ⟨e ▸ hx.1.const_mul c, ?_⟩
      have a := hx.2
      unfold per0 at a ⊢
      erw [e, integral_const_mul, a, mul_zero]
  exact h0 key.2

end WeakSepPf

theorem weakSep_of_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  intro hs h1 h2 h3 h4 h5 ε CF hCF
  obtain ⟨x, hx⟩ := h3 ε CF hCF
  obtain ⟨x', hx'⟩ := hs ε
  refine ⟨max x x', fun D large₂ e a b T L μ0 hL G W M hM M₀ hc0 t ht t0 w w0 => ?_⟩
  have q := offQ_of_sizeRows b
  have s := hx' D large₂ e (le_trans (le_max_right _ _) a) b
  obtain ⟨MP, hMP⟩ := h1 D q T L μ0 hL _ G W M hM 0 (Nat.zero_le _)
  obtain ⟨y, hy, v, hv, hp⟩ := hx D large₂ e (le_trans (le_max_left _ _) a) b T L μ0 hL G W M hM M₀ MP t ht t0 w w0
  obtain ⟨vol⟩ := WeakSepPf.nonempty_coreVol G
  have hr := (h2 D q s T L μ0 hL _ rfl G W M hM M₀ hc0 t ht w).1
  obtain ⟨F, ⟨Ψ, hΨ, rfl, c, hcol, ξ, hξ⟩, hF⟩ := WeakSepPf.exists_reach_of_span W hM (WeakSepPf.rapidDec_of_rapidRow W hr)
    (h4 D q s T L μ0 hL _ rfl G W M hM vol MP hMP y hy v hv) hp
  obtain ⟨ρ, Φ, hB⟩ := h5 D q T L μ0 hL _ G W M hM vol Ψ hΨ _ hr hF
  exact ⟨ρ, ξ, c, hcol, Φ, by rw [fPsiPhi, ← hξ]; exact hB⟩

end GlobalTheory.SepRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

def thSub (W : G.Weil) (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ (G.pS p) (G.pT p) f}
  add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg


open Classical in
def toTh (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : thSub W p :=
  if h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f then ⟨f, h⟩ else 0

theorem coe_toTh (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) :
    (toTh W p f : WO (G.pS p) (G.pT p) → ℂ) = f := by
  simp [toTh, h]

def lastIx (D : D7) : Fin D.R.m := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩

theorem lastIx_succ (D : D7) : D.R.m = (lastIx D : ℕ) + 1 := by
  have := D.R.two_le_m
  simp only [lastIx]
  omega

variable {W : G.Weil}

def colMapV (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (fs ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (gs ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

theorem colMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (x : ∀ j, FinPt G (.top j)) :
    S.colMap d x = colMapV S (fun j => S.Z.vec (d.1 j)) x := rfl

theorem rowMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    S.rowMap d y = rowMapV S (fun i => S.Z.vec (d.2 i)) y := rfl

def topLast (g : FinPt G (.top D.R.m)) : FinPt G (.top ((lastIx D : ℕ) + 1)) := lastIx_succ D ▸ g

def gridLast (g : FinPt G (.grid D.R.m D.R.m)) : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m) := lastIx_succ D ▸ g

def colShift (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) :=
  W.om (.top t (lastIx D)) (G.toPair (.top t (lastIx D)) 1
    (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1)

def rowShift (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (lastIx D) D.R.m) (G.toPair (.chi (lastIx D) D.R.m) 1
    (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1)

end GlobalTheory.LastVertexInv

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inRange_top (t : T) (j : Fin D.R.m) : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := by
  have := j.2
  simp [Pair.InRange, Node.InRange]

theorem inRange_chi (i : Fin D.R.m) : (Pair.chi (i : ℕ) D.R.m : Pair T).InRange D.R.m := by
  have := i.2
  simp [Pair.InRange, Node.InRange]

theorem defPair_top (t : T) (j : Fin D.R.m) : DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) := by
  have := j.2
  simp [DefPair]

theorem defPair_chi (i : Fin D.R.m) : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := by
  have := i.2
  simp [DefPair]

theorem vec_theta (S : GridChoice W U) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m)
    (d : FinDatum G t p) (h : S.Z.HasVec d) : IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (S.Z.vac_is p hp).2.theta)

theorem colShift_theta (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    {f : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (colShift S t g f) :=
  (W.om_is _ (inRange_top t (lastIx D))).om_pres _ _ h

theorem rowShift_theta (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    {f : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (rowShift S k f) :=
  (W.om_is _ (inRange_chi (lastIx D))).om_pres _ _ h

end GlobalTheory.LastVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitHalfResidueReductionFunctionEqFrameLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec.HalfCmp

variable {D : D7}

theorem toEAf_surjective : Function.Surjective (toEAf D) := by
  intro y
  have hs : Function.Surjective (finPart D) := by
    have h1 : Function.Surjective (sndA D.host.F) := fun b => ⟨(0, b), rfl⟩
    exact TensorProduct.map_surjective (g := (sndA D.host.F).toLinearMap) h1
      (g' := (AlgHom.id D.host.F D.host.E).toLinearMap) Function.surjective_id
  obtain ⟨z, hz⟩ := hs ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm y)
  refine ⟨z, ?_⟩
  change (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D z) = y
  rw [hz]; exact AlgEquiv.apply_symm_apply _ _

theorem gl_map_val {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin n) R) :
    (Matrix.GeneralLinearGroup.map f g).val = g.val.map f := rfl

end GlobalTheory.StepVec.HalfCmp


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
open GlobalTheory.StepVec.HalfCmp in
theorem GlobalTheory.StepVec.onHalf_viaRed_eq_locFn : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsIdemOf φ e → IsProjAt φ PP → IsRedMap φ PP r →
    ∀ (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ),
      onHalf φ S T (frCo φ βS) (frCo φ βT) e (viaRed r ω) = locFn S T βS βT e PP ω := by
  intro D v φ e PP r he hP hr S T βS βT ω
  obtain ⟨hchart, hcomp, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  funext t
  set N := frMapO S T βS βT t with hNdef
  have h1 : mapCo φ S T (frCo φ βS) (frCo φ βT) t = N.map (rdE φ) := by
    rw [hNdef]
    unfold mapCo frCo frMapO
    rw [Matrix.map_mul, Matrix.map_mul, ← map_inv, gl_map_val, gl_map_val, Matrix.map_map]
    congr 2
    ext i j
    simp [Function.comp, hcomp]
  unfold onHalf locFn
  by_cases hh : IsHalf e t
  swap
  · rw [if_neg hh, if_neg (fun h => hh h.1)]
  rw [if_pos hh, h1]
  have hfix : ∀ i j, toEAf D e * N i j = N i j := by
    intro i j
    have : toEAf D e • N = N := by
      rw [hNdef]; unfold frMapO
      rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      congr 2
      ext k l
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, hh k l]
    exact congrFun (congrFun this i) j
  have hiff : (∀ i j, (N.map (rdE φ)) i j ∈ v.adicCompletionIntegers D.host.F) ↔ IsIntM N := by
    constructor
    · intro h i j
      obtain ⟨a, ha⟩ := toEAf_surjective (N i j)
      have h2 : GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (rdA φ a) := by
        rw [GlobalTheory.SplitHecke.isInt_Ov, ← hcomp, ha]; exact h i j
      have h3 := (hchart.2.2.2 a).2 h2
      have h4 := GlobalTheory.PlaceCoord.toEAf_mem h3
      rwa [map_mul, ha, hfix] at h4
    · intro h i j
      exact (hr.2.2.2 (N i j) (h i j)).1
  unfold viaRed
  by_cases hI : IsIntM N
  · rw [dite_eq_left (hiff.2 hI), if_pos ⟨hh, hI⟩]
    congr 1
    ext i j
    obtain ⟨hm, hm'⟩ := hr.2.2.2 (N i j) (hI i j)
    simp only [Matrix.of_apply, Matrix.map_apply]
    unfold redM
    rw [dite_eq_left (hI i j), ← hm']
  · rw [dite_eq_right (fun h => hI (hiff.1 h)), if_neg (fun h => hI h.2)]
end

