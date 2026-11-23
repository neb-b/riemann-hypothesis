module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeBotOfNotMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LB GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)

namespace GlobalTheory.CompHS

def Cartier.pullOfInt {Y T : Scheme.{0}} [IsIntegral T] {I : Y.IdealSheafData} (Δ : Cartier I) (r : T ⟶ Y) {z₀ : T}
    (hz : r z₀ ∉ I.support) : Cartier (I.comap r) :=
  { Cartier.ofSec (LB.isLB_pull Δ.isLB r) (secPull Δ.t r) (y₀ := z₀)
      (by rw [nonzeroLocus_secPull]; exact (Δ.mem_nonzeroLocus _).2 hz) with
    cut := (GlobalTheory.Vanishing.eq_comap_of_stalk
      (fun z => GlobalTheory.Vanishing.stalkId_cutIdeal_secPull Δ.isLB (fun _ : Unit => Δ.t) z)).trans (by rw [Δ.cut]) }

theorem ne_bot_of_notMem {Y : Scheme.{0}} {I : Y.IdealSheafData} {y : Y} (h : y ∉ I.support) : I ≠ ⊥ := fun e => by
  rw [e, Scheme.IdealSheafData.support_bot] at h
  exact h trivial

theorem nonempty_resol (hPr : GlobalTheory.Published.Principalisation) {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}}
    {p : Y ⟶ Sp F} {D : ℕ} (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p)
    {U : Y.Opens} (hU : (U : Set Y).Nonempty) {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) {a₁ a₂ : Λ}
    {W₁ : Submodule F (H0 p (B a₁) ⊤)} {W₂ : Submodule F (H0 p (B a₂) ⊤)}
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) : Nonempty (Resol C U D W₁ W₂) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres p
  have hY : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral (f := p) (K := F) (𝟙 _) (𝟙 Y) p IsPullback.of_id_fst
  obtain ⟨u, hu⟩ := hU
  obtain ⟨Y₁, s₁, hi₁, hs₁, hp₁, hb₁, -, hc₁, -⟩ :=
    hPr F D Y p hY hs hp (baseIdeal (C.isLB a₁) W₁) (ne_bot_of_notMem (h₁ u hu))
  have iso₁ : IsIso (s₁ ∣_ U) := hb₁.isIso_restrict U h₁
  obtain ⟨z₁, hz₁⟩ : ∃ z : Y₁, z ∈ s₁ ⁻¹ᵁ U :=
    let z := inv (s₁ ∣_ U) ⟨u, hu⟩
    ⟨z.1, z.2⟩
  let M₁ : Modif p U D := ⟨Y₁, s₁, hs₁, hp₁, iso₁, (s₁ ⁻¹ᵁ U).isOpen.dense ⟨z₁, hz₁⟩⟩
  have off₂ : ∀ y ∈ s₁ ⁻¹ᵁ U, y ∉ ((baseIdeal (C.isLB a₂) W₂).comap s₁).support := fun y hy h => by
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h₂ _ hy h
  obtain ⟨Y₂, s₂, hi₂, hs₂, hp₂, hb₂, -, hc₂, -⟩ :=
    hPr F D Y₁ (s₁ ≫ p) hi₁ hs₁ hp₁ _ (ne_bot_of_notMem (off₂ z₁ hz₁))
  have iso₂ : IsIso (s₂ ∣_ (s₁ ⁻¹ᵁ U)) := hb₂.isIso_restrict _ off₂
  obtain ⟨z₂, hz₂⟩ : ∃ z : Y₂, z ∈ s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U) :=
    let z := inv (s₂ ∣_ (s₁ ⁻¹ᵁ U)) ⟨z₁, hz₁⟩
    ⟨z.1, z.2⟩
  let M₂ : Modif M₁.str M₁.opn D := ⟨Y₂, s₂, hs₂, hp₂, iso₂, (s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U)).isOpen.dense ⟨z₂, hz₂⟩⟩
  have Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact (_root_.GlobalTheory.CompHS.nonempty_cartier_of_locally_principal _ _ hc₂).some
  have Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (_root_.GlobalTheory.CompHS.nonempty_cartier_of_locally_principal _ _ hc₁).some.pullOfInt s₂ (z₀ := z₂) (by
      rw [Scheme.IdealSheafData.support_comap]; exact h₁ _ hz₂)
  exact ⟨{ toModif := M₁.trans M₂, Δ₁ := Δ₁, Δ₂ := Δ₂ }⟩

end GlobalTheory.CompHS


open GlobalTheory.CompHS in
theorem GlobalTheory.CompHS.nonempty_choice : GlobalTheory.Published.Principalisation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw), IsVariety₀ TF.X Z → FreeOnOpen TF.X Z U P.u₁ → FreeOnOpen TF.X Z U P.u₂ → Nonempty (Choice TF.X Z U P) := by
  intro hPr E _ _ _ H Dw l Xo c TF Z r U P hv h₁ h₂
  obtain ⟨hs, hp, hc⟩ := hv
  have : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  exact nonempty_resol hPr hs hp hc (dense_U₀ TF.X Z).nonempty (common₀ TF.X Z) h₁ h₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulLeSqrtBergmanMulComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open MeasureTheory

namespace GlobalTheory.HSApp.NormProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)
  {D : D7} (V : TH.HSp D) (dict : Formalism.L2.Theta.GA D V → (k : U.Comp) × FD.Frame (U.X k).Ψ r) (μ : Measure (AutQ V))

theorem ptN_rdU_le {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c} (hf : rdU U f ∈ holSub U.X la)
    (z : (k : U.Comp) × FD.Frame (U.X k).Ψ r) : AllWt.ptN la (rdU U f) z ≤ (supE U.X la (rdU U f)).toReal := by
  by_cases h : z.2 ∈ (U.X z.1).dom
  · have h1 : ENNReal.ofReal (AllWt.ptN la (rdU U f) z) ≤ supE U.X la (rdU U f) :=
      le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2)) ⟨z.1, ⟨z.2, h⟩⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top U.X la hf)).1 h1
  · have h0 : AllWt.ptN la (rdU U f) z = 0 := by
      simp [AllWt.ptN, FD.Data.pnorm, rdU, h]
    rw [h0]; exact ENNReal.toReal_nonneg

theorem petE_rdU_ne_top (hμ : μ Set.univ ≤ 1) {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X la) : AllWt.petE V dict μ la (rdU U f) ≠ ⊤ := by
  have hb : ∀ᵐ q ∂μ, ‖AllWt.ptN la (rdU U f) (dict (Quotient.out q))‖ ≤ (supE U.X la (rdU U f)).toReal :=
    Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _)]; exact ptN_rdU_le U hf _
  have hle : AllWt.petE V dict μ la (rdU U f) ≤
      eLpNorm' (fun _ : AutQ V => (supE U.X la (rdU U f)).toReal) 2 μ := by
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [hb] with q hq
    simpa [Real.norm_of_nonneg ENNReal.toReal_nonneg] using hq
  rw [eLpNorm'_const _ (by norm_num), Real.enorm_eq_ofReal ENNReal.toReal_nonneg] at hle
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ))) hle

theorem eLpNorm_homN_ne_top (hμ : μ Set.univ ≤ 1) {G : WTZ E} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    eLpNorm' (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) 2 μ ≠ ⊤ := by
  have : (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) =
      AllWt.lieFacZ Dw x G • fun q : AutQ V => AllWt.ptN (AllWt.modelWt U G) (rdU U f) (dict (Quotient.out q)) := rfl
  rw [this, eLpNorm'_const_smul _ (by norm_num)]
  exact ENNReal.mul_ne_top enorm_ne_top (petE_rdU_ne_top U V dict μ hμ hf)

theorem homN_le_of_berg (hμ : μ Set.univ ≤ 1) (y : FPt U.X) {B : ℝ} (hB0 : 0 ≤ B) {G : WTZ E}
    (hB : AllWt.bergE V dict μ (AllWt.modelWt U G) y ≤ ENNReal.ofReal B) {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    AllWt.homN U x G f ⟨y.1, y.2.1⟩ ≤ Real.sqrt B * AllWt.petAt U x V dict μ G f := by
  have hfin := petE_rdU_ne_top U V dict μ hμ hf
  have h1 : ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) (rdU U f) ⟨y.1, y.2.1⟩) ^ 2 /
      AllWt.petE V dict μ (AllWt.modelWt U G) (rdU U f) ^ 2 ≤ ENNReal.ofReal B :=
    (le_iSup₂ (f := fun P (_ : P ∈ holSub U.X (AllWt.modelWt U G)) =>
      ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) P ⟨y.1, y.2.1⟩) ^ 2 /
        AllWt.petE V dict μ (AllWt.modelWt U G) P ^ 2) (rdU U f) hf).trans hB
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl (ENNReal.pow_ne_top hfin))] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) h1
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB0, ENNReal.toReal_pow] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (AllWt.lieFacZ Dw x G))
  have h4 : AllWt.homN U x G f ⟨y.1, y.2.1⟩ ^ 2 ≤ B * AllWt.petAt U x V dict μ G f ^ 2 := by
    unfold AllWt.homN AllWt.petAt
    nlinarith [h3]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (AllWt.homN_nonneg _ _ _ _ _), Real.sqrt_mul hB0, Real.sqrt_sq (AllWt.petAt_nonneg _ _ _ _ _ _ _)] at h5

end GlobalTheory.HSApp.NormProd

namespace GlobalTheory.HSApp


open MeasureTheory in
theorem petOn_mul_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  intro D T j Y e o _ _ Z a b w f β hβ hB σ
  set σ' := goodOf Y.d.c₂ σ with hσ'
  have hg : GoodEmb Y.d.c₂ σ' := Formalism.L2.PjFree.goodEmb_goodOf Y.d.c₂ σ
  set μ := AllWt.muOn (Y.U σ') (D.sp.W j) (Y.dict σ') Z with hμdef
  have hμ : μ Set.univ ≤ 1 := AllWt.muPart_univ_le _ _ _
  have hwH := (AllWt.mem_cuspW.1 w.2.1).2 σ' hg
  have hfH := (AllWt.mem_cuspW.1 f.2.1).2 σ' hg
  have hab : AllWt.wtOf (T.Q.Dw j) (a + b) 0 = AllWt.wtOf (T.Q.Dw j) a 0 + AllWt.wtOf (T.Q.Dw j) b 0 :=
    AllWt.wtOf_add a b 0 0
  set Pa := AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) a 0) w.1 with hPa
  have hPa0 : 0 ≤ Pa := AllWt.petAt_nonneg _ _ _ _ _ _ _
  have hpt : ∀ z : (k : (Y.U σ').Comp) × FD.Frame ((Y.U σ').X k).Ψ D.R.r,
      AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z ≤
        (Real.sqrt β * Pa) * AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) b 0) f.1 z := by
    intro z
    by_cases hz : z ∈ AllWt.framesOn (Y.U σ') Z
    · obtain ⟨h, -⟩ := id hz
      rw [hab, AllWt.homN_mul _ _ (AllWt.even_wtOf _ _) (AllWt.even_wtOf _ _) _ _ z h]
      refine mul_le_mul_of_nonneg_right ?_ (AllWt.homN_nonneg _ _ _ _ _)
      have hy := hB σ' hg ⟨z.1, ⟨z.2, h⟩⟩ hz
      exact NormProd.homN_le_of_berg (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ hμ ⟨z.1, ⟨z.2, h⟩⟩ hβ hy hwH
    · have h0 : rdU (Y.U σ') w.1 z.1 z.2 = 0 := AllWt.rdU_eq_zero (Y.U σ') w.2.2 hz
      have h1 : AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z = 0 := by
        simp only [AllWt.homN, AllWt.ptN, FD.Data.pnorm, AllWt.rdU_mul, Pi.mul_apply, h0, zero_mul, norm_zero, mul_zero]
      rw [h1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hPa0) (AllWt.homN_nonneg _ _ _ _ _)
  have key : eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0)
      (w.1 * f.1) (Y.dict σ' (Quotient.out q))) 2 μ ≤
      ENNReal.ofReal (Real.sqrt β * Pa) * eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
        (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) 2 μ := by
    rw [← Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0), ← eLpNorm'_const_smul _ (by norm_num)]
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [] with q
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.norm_of_nonneg (AllWt.homN_nonneg _ _ _ _ _),
      Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hPa0)
        (AllWt.homN_nonneg _ _ _ _ _))]
    exact hpt _
  have hfin : eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
      (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) 2 μ ≠ ⊤ := by
    have heq : (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
        (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) =
        AllWt.lieFacZ (T.Q.Dw j) (xiR D) (AllWt.wtOf (T.Q.Dw j) b 0) •
          fun q : AutQ (D.sp.W j) => AllWt.ptN (AllWt.modelWt (Y.U σ') (AllWt.wtOf (T.Q.Dw j) b 0))
            (rdU (Y.U σ') f.1) (Y.dict σ' (Quotient.out q)) := rfl
    rw [heq, eLpNorm'_const_smul _ (by norm_num)]
    exact ENNReal.mul_ne_top enorm_ne_top (NormProd.petE_rdU_ne_top (Y.U σ') (D.sp.W j) (Y.dict σ') μ hμ hfH)
  have k2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) key
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0)] at k2
  show AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ (w.1 * f.1) ≤
    Real.sqrt β * Pa * AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ f.1
  rw [AllWt.petAt_eq, AllWt.petAt_eq (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) b 0)]
  exact k2

end GlobalTheory.HSApp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixExp

theorem pow_mul_le_of_cls_eq {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)]
    (h : Published.NefProductNonneg) (hp : IsProjOver (strHom k (X := Y))) {e : ℕ}
    (hD : topologicalKrullDim Y = e) {N N' N₀ : LB Y} (hN : IsNef k N) (hN' : IsNef k N')
    (h₀ : N₀.IsLB) (a b : ℕ) (hc : cls N₀ h₀ = a • cls N hN.isLB + b • cls N' hN'.isLB) :
    (a : ℤ) ^ e * interNum k (structureModule Y) (fun _ : Fin e => N) ≤
      interNum k (structureModule Y) (fun _ : Fin e => N₀) := by
  have := isNoetherian_of_isProjOver hp
  have H := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k Y) (structureModule Y) hp
    (d := e) (by rw [suppDim_structureModule, hD])
  have hL : ∀ j, IsNef k ((![N, N'] : Fin 2 → LB Y) j) := fun j => by
    fin_cases j
    exacts [hN, hN']
  have e₁ := H.interNum_of_cls_eq_sum (L := ![N, N']) (fun j => (hL j).isLB)
    (Q := fun _ => N₀) (fun _ => h₀) (fun _ => ![(a : ℤ), (b : ℤ)])
    (fun _ => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natCast_zsmul]
      exact hc)
  have e₂ := Finset.single_le_sum
    (f := fun c : Fin e → Fin 2 =>
      (∏ i, (![(a : ℤ), (b : ℤ)] : Fin 2 → ℤ) (c i)) *
        interNum k (structureModule Y) (![N, N'] ∘ c))
    (fun c _ => mul_nonneg (Finset.prod_nonneg fun i _ => by
        generalize c i = j
        fin_cases j <;> simp)
      (h.interNum_nonneg (N := ![N, N'] ∘ c) hp hD fun i => hL (c i)))
    (Finset.mem_univ fun _ => 0)
  rw [e₁]
  refine le_trans (le_of_eq ?_) e₂
  simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.MixExp


open GlobalTheory.MixExp in
theorem GlobalTheory.mixExp_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  intro h k _ X q hq
  letI := algebraΓOfHom q
  intro N N' N₀ hN hN' h₀ a b Z e hnef hnef' hc hZ
  have hp : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := q) fun _ => rfl]
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  change (a : ℤ) ^ e * interNumOn k (redι Z) (fun _ : Fin e => N) ≤
    interNumOn k (redι Z) (fun _ : Fin e => N₀)
  rw [interNumOn_eq_interNum_pull hi fun _ => hN, interNumOn_eq_interNum_pull hi fun _ => h₀]
  refine pow_mul_le_of_cls_eq h.1 hpZ ((topologicalKrullDim_red Z).trans hZ)
    (hnef.pull_of_isClosedImmersion (redι Z) hi) (hnef'.pull_of_isClosedImmersion (redι Z) hi)
    (LB.isLB_pull h₀ (redι Z)) a b ?_
  rw [cls_pull h₀, cls_pull hN, cls_pull hN', hc, map_add (f := _), map_nsmul, map_nsmul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullTopInjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullBig

open GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 Filter

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (σ : X ⟶ Y)
    (hσ : DenseRange σ) : σ (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image σ.continuous
  rw [Set.image_univ, hσ.closure_range] at h
  exact h.eq (genericPoint_spec Y)

theorem pull_top_injective {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : Y ⟶ Sp k} (σ : X ⟶ Y) (hσ : DenseRange σ) (B : LB Y) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top) := by
  have hη := map_genericPoint σ hσ
  have hF : IsField (Y.presheaf.stalk (σ (genericPoint X))) := by
    rw [hη]; exact Field.toIsField Y.functionField
  refine (injective_iff_map_eq_zero _).2 fun f hf => LB.sec_ext fun i => fun_ext_ger fun y hy => ?_
  have hηi : genericPoint Y ∈ B.U i :=
    ((genericPoint_spec Y).mem_open_set_iff (B.U i).isOpen).2 ⟨y, Set.mem_univ _, hy.2⟩
  have hxi : σ (genericPoint X) ∈ B.U i := hη ▸ hηi
  have h0 : germ (p := p) (O := ⊤) i (σ (genericPoint X)) trivial hxi f = 0 := by
    have e := congrArg (germ (p := σ ≫ p) (B := B.pull σ) (O := ⊤) (fun _ => i) (genericPoint X) trivial (mem_pull.2 hxi)) hf
    have e' := (germ_pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top (fun _ => i) (genericPoint X) trivial
      (mem_pull.2 hxi) f).symm.trans (e.trans (map_zero _))
    by_contra hne
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    have := congrArg (σ.stalkMap (genericPoint X)).hom hb
    rw [map_mul, e', zero_mul, map_one] at this
    exact zero_ne_one this
  have hloc : f.loc i = 0 :=
    germ_injective_of_isIntegral Y (U := ⊤ ⊓ B.U i) (σ (genericPoint X)) ⟨trivial, hxi⟩
      (h0.trans (map_zero _).symm)
  exact congrArg _ hloc

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y), IsProjOver p → IsProjOver (σ ≫ p) →
    topologicalKrullDim X = topologicalKrullDim Y → DenseRange σ → ∀ L : LB Y,
    (letI := algebraΓOfHom p; IsBig k L) → (letI := algebraΓOfHom (σ ≫ p); IsBig k (L.pull σ)) := by
  intro k _ X Y _ _ p σ hp hq hdim hσ L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (σ ≫ p)
  obtain ⟨D, hD, c, hc, hm⟩ := hL.growth
  have hL' := LB.isLB_pull hL.isLB σ
  have key (m : ℕ) : lbH0 k (lbPow L m) ≤ lbH0 k (lbPow (L.pull σ) m) := by
    have hLm := isLB_lbPow hL.isLB m
    have hP := LB.isLB_pull hLm σ
    haveI := finite_top hq hP
    calc lbH0 k (lbPow L m) = Module.finrank k (H0 p (lbPow L m) ⊤) := (H0.finrank_top p _).symm
      _ ≤ Module.finrank k (H0 (σ ≫ p) ((lbPow L m).pull σ) ⊤) :=
        LinearMap.finrank_le_finrank_of_injective (pull_top_injective σ hσ _)
      _ = lbH0 k ((lbPow L m).pull σ) := H0.finrank_top _ _
      _ = lbH0 k (lbPow (L.pull σ) m) := lineBundleGlobalSectionsDim_congr_picardClass hP (isLB_lbPow hL' m) (by
        rw [cls_pull hLm, cls_lbPow hL.isLB, cls_lbPow hL', cls_pull hL.isLB, map_nsmul])
  refine (isBig_iff (fun _ => rfl) hq (hdim.trans hD)).2 ⟨hL', c, hc, hm.mono fun m hm' => ?_⟩
  exact hm'.trans (by exact_mod_cast key m)

end GlobalTheory.PullBig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

def ratField {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (S : Set (H0 p B O))
    (y : Y) (hy : y ∈ O) : Subfield (Y.residueField y) :=
  Subfield.closure {r | ∃ (i : B.ι) (hi : y ∈ B.U i) (s s' : H0 p B O), s ∈ S ∧ s' ∈ S ∧
    r = (Y.residue y).hom (germ i y hy hi s) / (Y.residue y).hom (germ i y hy hi s')}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def RatGen {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) : Prop :=
  ∃ (η : Y₀ X Z) (hη : η ∈ U₀ X Z), IsGenericPoint η Set.univ ∧
    ratField (Set.range (cuspSec X Z U la)) η hη = ⊤

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortFamilyOfSpanning
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

theorem GlobalTheory.HSApp.shortFamily_of_spanning : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, ∀ (Λ : ℝ) (m : ℕ) (v : Fin m → Cusp Z U (P.wt j)), (∀ i, v i ∈ latOn U Z _) → Submodule.span c.F (Set.range v) = ⊤ → (∀ i σ, petOn U x V dict Z (wtOf Dw (P.wt j) 0) σ (v i).1 ≤ Λ) → (h.data f₁ f₂ th k).ShortFamily j Λ := by
  intro E _ _ _ H Dw l Xo c TF Z r U P R ω x D V dict h f₁ f₂ th k j hj Λ m v hv hs hn
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' c.F v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  let b := Module.Basis.mk hli (by rw [hsp, hs])
  have hcard : Fintype.card κ = latRank c.F ((h.data f₁ f₂ th k).M j) := by
    rw [(h.data f₁ f₂ th k).latRank_M j, ← (h.equivV f₁ f₂ th k hj).finrank_eq, Module.finrank_eq_card_basis b]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => h.equivV f₁ f₂ th k hj (v (a (e i))), fun i => ?_, ?_, fun i σ => ?_⟩
  · exact (h.equivV_mem f₁ f₂ th k hj _).2 (hv _)
  · exact ((hli.comp e e.injective).map' _ (h.equivV f₁ f₂ th k hj).ker)
  · rw [h.nrm_equivV f₁ f₂ th k hj]
    exact hn _ σ
end

