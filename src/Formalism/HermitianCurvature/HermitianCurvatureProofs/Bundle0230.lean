module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0226
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0224

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ResidueSquareIntegrablePositiveRank
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section JF

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain in
theorem residue_radial_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (a b : Ix S) :
    ((RRi L st 0 w) a b).1 Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 := by
  have hlc : Φ ∈ lcSub P.k P.r z z' π π' := jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ
  have hRRlc := RRi_lc X μ L st l0 hD 0 w hw.1.2.1
  refine ⟨(hRRlc a b).1 Φ hlc, fun c => ?_⟩
  subst hz hz' hπ hπ'
  obtain ⟨ε, hε, hG⟩ := hF.1.2
  have hN : JC.NiceCoef D ε F :=
    ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hF.1.1 0 m).choose_spec.1), hF.1.1, hG⟩
  let F' : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => if b' = b then F else fun _ => 0
  have hN' : ∀ b', JC.NiceCoef D ε (F' b') := by
    intro b'
    by_cases h : b' = b
    · simp only [F', if_pos h]; exact hN
    · simp only [F', if_neg h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let x : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => B.JF D (F' b')
  let Φv : Ix S → RadSp P.k P.r D.z D.z' D.π D.π' := fun b' => if b' = b then Φ else 0
  have hx : ∀ b', x b' ∈ FFl P.k P.r D.z D.z' D.π D.π' 0 (OmPlus P.k P.r D.z D.z') := fun b' =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq D (F' b') ε hε (hN' b')
  have hΦv : ∀ b', ∀ y ∈ DomR P.k P.r D.z D.z',
      (Φv b' : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (x b') y.1 y.2 := by
    intro b' y hy
    by_cases h : b' = b
    · simp only [Φv, x, F', if_pos h]; exact hΦ y hy
    · simp only [Φv, x, F', if_neg h]
      simp only [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero, smul_zero]
      rfl
  have key := Formalism.FourierDecayAlt.P.JCx2.rma_main D.z_mem D.z'_mem X L st (M.sgn P l0) hD.2.2.1 hD.2.2.2.1 w x Φv hx hΦv
  have hsingle : act (RRi L st 0 w) Φv a = ((RRi L st 0 w) a b).1 Φ := by
    unfold act
    rw [Finset.sum_eq_single b (fun b' _ hb' => by simp only [Φv, if_neg hb', map_zero])
      (fun h => absurd (Finset.mem_univ b) h)]
    simp only [Φv, if_pos rfl]
  have hR := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure Formalism.FourierDecayAlt.P.JCx2.bcGood_closed
    (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0))
    (fun Y p q => Formalism.FourierDecayAlt.P.JCx2.bcGood_tL (Bs := D) (ε := ε) (M.sgn P l0) Y p q) w
  let G : Mx P.k P.r → (Wq →L[ℂ] Wp) :=
    Formalism.FourierDecayAlt.D.actOp (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w) F' a
  have hGN : JC.NiceCoef D ε G := by
    show JC.NiceCoef D ε (∑ b', Formalism.FourierDecayAlt.D.ap (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w a b') (F' b'))
    exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' Finset.univ _ fun b' _ => (hR a b').1 (F' b') (hN' b')
  have hpic : ∀ y ∈ DomR P.k P.r D.z D.z',
      ((((RRi L st 0 w) a b).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
    intro y hy
    rw [← hsingle, key a y hy]
    have hGV : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ JF.Om P.k P.r D.z D.z' :=
      ⟨hGV, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hy.1 hy.2.1 hy.2.2⟩
    simp only [resG]
    congr 1
    exact (Formalism.FourierDecayAlt.P.JCx2.bc_core _ hR F' hN' a hh).symm
  have h := level_zero_form_integrable_compact (S := Empty) D μ hD.2.1 (fun _ => G) (fun _ => G)
    (fun _ => ((RRi L st 0 w) a b).1 Φ) (fun _ => ((RRi L st 0 w) a b).1 Φ)
    (fun _ => hGN.2.1) (fun _ => hGN.2.1) (fun _ => hpic) (fun _ => hpic) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

end JF

section Gd

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]


variable (S : Type) [Fintype S] [DecidableEq S] in
def gd0 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) : Submodule ℂ (RadSp P.k P.r z z' π π') where
  carrier := {v | v ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ ∧ ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
    ∀ a b, ((RRi L st 0 w) a b).1 v ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ}
  zero_mem' := ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).zero_mem, fun w _ a b => by
    rw [map_zero]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).zero_mem⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    exact ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).add_mem hu hv, fun w hw a b => by
      rw [map_add (f := _)]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).add_mem (Iu w hw a b) (Iv w hw a b)⟩
  smul_mem' := by
    rintro c u ⟨hu, Iu⟩
    exact ⟨(squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).smul_mem c hu, fun w hw a b => by
      rw [map_smul]; exact (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ).smul_mem c (Iu w hw a b)⟩

variable {S : Type} [Fintype S] [DecidableEq S]

theorem good_domain_plane_wave (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) (hl : l.castSucc = 0) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (h1 : multiplicationOperator Wv (fun c _ => fsv s (c l))) (h2 : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (v : RadSp P.k P.r z z' π π') (hv : v ∈ gd0 S P z z' π π' μ hD.2.1 L st l0) :
    Wv v ∈ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
  obtain ⟨hvl, hvR⟩ := hv
  refine ⟨unimodular_multiplier_preserves_L2 μ hD.2.1 h1 (fun c _ => norm_fsv _ _) v hvl, fun w hw a b => ?_⟩
  have hC := Formalism.FourierDecayAlt.P5.waveCommQQAll Wp Wq P z z' π π' X μ L st l0 hD l s Wv Wv' h1 h2
  have hWQ := waveQQ_castSucc X L st hD.2.2.1 l s Wv Wv' h1 h2 hC
  rw [hl] at hWQ
  obtain ⟨hWave, -⟩ := Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' h1 h2
  have hrr := rr_io_wave (QQi L st 0) (mkP Wv Wv') (mkP Wv' Wv) s w hWave hWQ hw.1.1
  have he := congrFun (congrFun hrr a) b
  rw [mul_io_apply, io_apply_mul] at he
  have hM : ((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b) ∈
      sendsTo (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1) v := by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨α, hα⟩ := mem_bot_alg (star_entSub (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w) a c)
    obtain ⟨β, hβ⟩ := mem_bot_alg (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w d b)
    rw [hα, hβ]
    exact sendsTo_alg_mul_alg _ v (hvR w hw c d) α β
  have e : ((RRi L st 0 w) a b).1 (Wv v) = Wv ((((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b)).1 v) :=
    congrArg (fun x : Pr (RadSp P.k P.r z z' π π') => x.1 v) he
  rw [e]
  exact unimodular_multiplier_preserves_L2 μ hD.2.1 h1 (fun c _ => norm_fsv _ _) _ hM

theorem compact_kernel_le_good_domain (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (hr : 0 < P.r) :
    herKc S P z z' π π' L st l0 D 0 ≤ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ gd0 S P z z' π π' μ hD.2.1 L st l0 := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ =>
      exact fun _ => ⟨radial_transform_square_integrable P z z' π π' μ hD.2.1 D hD.1 hz hz' hπ hπ' F hF Φ hΦ,
        fun w hw a b => residue_radial_square_integrable P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' F hF Φ hΦ w hw a b⟩
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w' s Wv Wv' a' b' Φ _ h1 h2 _ ih =>
      intro h
      have hv := ih h
      have hVw : Vw (mkP Wv Wv') s w' a' b' = mkP Wv Wv' * UUiw s w' a' b' := by
        unfold Vw; exact io_apply_mul _ _ _ _
      obtain ⟨κ, hκ⟩ := mem_bot_alg (UUiw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w' a' b')
      have e : (Vw (mkP Wv Wv') s w' a' b').1 Φ = κ • Wv Φ := by
        rw [hVw, hκ, pr_fst_mul, pr_fst_algebraMap, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
        rfl
      rw [e]
      exact (gd0 S P z z' π π' μ hD.2.1 L st l0).smul_mem κ
        (good_domain_plane_wave P z z' π π' X μ L st l0 hD l h s Wv Wv' h1 h2 Φ hv)
    | waveZ w s Wv Wv' a b Φ _ _ _ _ _ =>
      intro h
      exfalso
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
  exact key 0 Φ hΦ rfl

def ResidueSquareIntegrablePositiveRank : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D 0) x → ∀ (a : Ix S) (c : Fin P.r → ℂ), c ∈ OmX P.r →
        LevelSquareIntegrable μ 0 (act (RRi L st 0 w) x a) c

theorem rRL2Lev0Pos : ResidueSquareIntegrablePositiveRank := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' hr w hw x hx a c _
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hle := compact_kernel_le_good_domain (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' hr
  have hm : act (RRi L st 0 w) x a ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1 :=
    (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hD.2.1).sum_mem fun b _ => (hle (hx b)).2 w hw a b
  exact hm.2 c

def HermitianLevelZeroPositiveRank : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' → 0 < P.r →
    HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D 0

theorem hermitian_level_zero_positive_rank : HermitianLevelZeroPositiveRank := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  refine ⟨fun u hu => ?_, fun w hw x hx a =>
    rRL2Lev0Pos Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' hr w hw x hx a c hc⟩
  exact (compact_kernel_le_L2 (S := S) P z z' π π' μ hD.2.1 L st l0 D hD.1 hz hz' hπ hπ' hu).2 c

theorem hermitian_all_of_transport (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) : HermitianSquareIntegrableAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
  obtain ⟨Di, Xi, μi, Li, sti, T, hDi, ⟨-, ⟨κ, hκ, hpair⟩, -, hw⟩, hHer⟩ :=
    hT Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i c (fun l _ => hc l)
  have hlow := hermitian_level_zero_positive_rank Wp Wq S (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 Di hDi h1 h2 rfl rfl rfl rfl
    (by show 0 < P.r - (i : ℕ); omega) (fun _ => 1) (fun _ => one_ne_zero)
  refine ⟨fun u hu => ?_, fun w hwo x hx a => ?_⟩
  · exact level_square_integrable_of_transport μ i c μi T κ hκ hpair u _ (hlow.1 (T u) (hHer S u hu))
  · obtain ⟨-, hRR, hWO⟩ := hw S w
    have hA := hRR 0 (by omega)
    have e1 : (⟨0 + i.val, by omega⟩ : Fin (P.r + 1)) = i := Fin.ext (by simp)
    have e0 : (⟨0, by omega⟩ : Fin (P.r - i + 1)) = 0 := rfl
    rw [e1, e0] at hA
    refine level_square_integrable_of_transport μ i c μi T κ hκ hpair _ (fun _ => 1) ?_
    rw [act_tr T hA x a]
    exact hlow.2 w (hWO hwo) _ (fun b => hHer S (x b) (hx b)) a

theorem formIntOuterCpt_of_levT (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) : FormIntOuterCpt :=
  outer_form_compact_of_square (hermitian_all_of_transport hT)

end Gd

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntegralJacobianFactor
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section fubini

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def psiH {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : ℂ := G.psi U.betaU (U.subS (lhOf σ v))

theorem volume_empty_blocks_real (p : ℕ) : (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).real Set.univ = 1 := by
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  rw [volume_pi, volume_pi, Measure.pi_univ, Measure.pi_univ]
  simp [volume_pi, Measure.pi_univ]

def regroup (σ : Equiv.Perm (Fin p)) :
    XL k p ρ σ ≃ᵐ PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ) :=
  MeasurableEquiv.prodAssoc.symm

theorem regroup_apply (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : regroup σ x = ((x.1, x.2.1), x.2.2) := rfl

theorem regroup_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (regroup σ) (muL Bj σ)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  exact (measurePreserving_prodAssoc (Bj.μW.prod Bj.μN) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))).symm

def fH (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ)
    (q : PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)) : Wq →L[ℂ] Wp :=
  psiH σ q.2.2 • PBQ.pbI Bj B0 rfl H (U.mMap k p ρ (lhOf σ q.2.2 * U.hMat σ d) g) q.1

theorem ellL_eq (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) = fH Bj B0 σ d H g (regroup σ x) := by
  have hP : PBQ.GoodP Bj (x.1, x.2.1) := hx
  have hs : sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g =
      D.castM rfl (PBQ.sP Bj (x.1, x.2.1)) * U.mMap k p ρ (lhOf σ x.2.2.2 * U.hMat σ d) g := by
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, sxL, if_pos hx, PBQ.sP, if_pos hP]
    have e := embedding_map_lower_unipotent k p ρ (lhOf σ x.2.2.2) (U.hMat σ d) 1 g (lh_unit σ x.2.2.2)
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.PBM.muP_one, Matrix.mul_one] at e
    rw [e]
    have e2 := embedded_group_measure_preserving k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
      ((lhOf σ x.2.2.2)ᴴ⁻¹)
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← Matrix.mul_assoc (U.muP k p ρ _) (U.embG k p ρ _), ← e2, Matrix.mul_assoc]
  rw [hs, regroup_apply]
  unfold fH ellL PBQ.pbI cL PBQ.cP psiH
  simp only [_root_.smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceInt (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g) := by
  obtain ⟨hint, hJ⟩ := core_lf hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have hsf : SigmaFinite (PBQ.muXP (p := p) Bj) := by unfold PBQ.muXP; infer_instance
  have hae : (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) =ᵐ[muL Bj σ]
      fun x => fH Bj B0 σ d H g (regroup σ x) := by
    filter_upwards [ae_goodL Bj σ] with x hx
    exact ellL_eq Bj B0 σ d H g x hx
  have mp := regroup_mp Bj σ
  have hint2 : Integrable (fH Bj B0 σ d H g)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) :=
    (mp.integrable_comp_emb (regroup σ).measurableEmbedding).1 ((hint.congr hae))
  have hJ2 : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, fH Bj B0 σ d H g q ∂((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) ×
        (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))) := by
    rw [hJ, integral_congr_ae hae, mp.integral_comp' (fH Bj B0 σ d H g)]
  have hin : ∀ c : ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ),
      ∫ xP, fH Bj B0 σ d H g (xP, c) ∂(PBQ.muXP Bj) =
        psiH σ c.2 • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ c.2 * U.hMat σ d) g) := by
    intro c
    unfold fH PBQ.pbF
    exact integral_smul (psiH σ c.2) _
  have hR1 := hint2.integral_prod_right
  simp only [hin] at hR1
  have hR2 := hR1.integral_prod_right
  simp only [integral_const, volume_empty_blocks_real, one_smul] at hR2
  refine ⟨hR2, ?_⟩
  rw [hJ2, integral_prod_symm _ hint2]
  simp only [hin]
  rw [integral_fun_snd (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)),
    volume_empty_blocks_real, one_smul]

end fubini

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem slice_integral_jacobian_factor {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ,
          G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g) :=
  SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothGOfSf
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Ent

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothG_of_sf {a : Mx k ρ → ℂ}
    (h : SmoothFam k ρ (Fin.last ρ) (Set.univ : Set (Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) (fun _ g => a g)) : SmoothG k ρ a := by
  intro y₀ hy₀
  obtain ⟨U, F, hU, hxU, hF, hfF⟩ := h ((0 : Fin ρ → ℂ), Matrix.of y₀) (Set.mem_univ _) hy₀
  have hm : Continuous fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    continuous_const.prodMk continuous_id
  have hmd : ContDiff ℝ ∞ fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) ⁻¹' U,
    fun y => F ((0 : Fin ρ → ℂ), Matrix.of y), hU.preimage hm, hxU, hF.comp hmd.contDiffOn (fun y hy => hy),
    fun y hy hG => hfF _ hy hG⟩

theorem smoothG_yv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => yv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_yv z j)

theorem smoothG_ybv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => ybv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_ybv z j)

theorem parOK_EH (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (EH k ρ (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) :=
  parOK_congr (parOK_add (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).1))
    (parOK_csmul Complex.I
      (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).2)))) (fun f g => rfl)

theorem parOK_Top (u : ℂ) (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (Top (EH k ρ) u (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) := by
  by_cases hab : posL k ρ (Fin.last ρ) a = posL k ρ (Fin.last ρ) b
  · exact parOK_congr (parOK_add (parOK_csmul u parOK_id) (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])
  · exact parOK_congr (parOK_add parOK_zero (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])

theorem parOK_qminor {t : ℕ} (a b : Fin t → Fin (mdim k ρ (Fin.last ρ))) (u : ℂ) :
    ParOK k ρ (E := E) (qminorOp (EH k ρ) (posL k ρ (Fin.last ρ) ∘ a) (posL k ρ (Fin.last ρ) ∘ b) u) := by
  have key : ∀ σ : Equiv.Perm (Fin t), ParOK k ρ (E := E) (fun f g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k ρ) (u - ((j : ℕ) : ℂ)) ((posL k ρ (Fin.last ρ) ∘ a) (σ j))
          ((posL k ρ (Fin.last ρ) ∘ b) j)).foldr (fun T h => T h) f g)) := by
    intro σ
    refine parOK_csmul _ (parOK_foldr _ ?_)
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact parOK_Top _ _ _
  refine parOK_congr (parOK_sum Finset.univ (fun σ _ => key σ)) (fun f g => ?_)
  simp [qminorOp, Finset.sum_apply]

theorem parOK_chatL (u : ℂ) (a β : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) :
    ParOK k ρ (E := E) (chatL (EH k ρ) (posL k ρ (Fin.last ρ)) u a β) := by
  refine parOK_congr (parOK_sum Finset.univ fun i' _ => parOK_sum Finset.univ fun j' _ =>
    parOK_smulG (smoothG_mul (smoothG_mul (smoothG_const _) (hβ i')) (ha j')) (parOK_qminor _ _ _))
    (fun f g => rfl)

theorem parOK_chat2L (u : ℂ) (a a' β β' : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (ha' : ∀ j, SmoothG k ρ (fun g => a' g j))
    (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) (hβ' : ∀ j, SmoothG k ρ (fun g => β' g j)) :
    ParOK k ρ (E := E) (chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) u a a' β β') := by
  refine parOK_congr (parOK_sum Finset.univ fun i₁ _ => parOK_sum Finset.univ fun i₂ _ =>
    parOK_sum Finset.univ fun j₁ _ => parOK_sum Finset.univ fun j₂ _ => ?_) (fun f g => rfl)
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · refine parOK_congr (parOK_smulG (smoothG_mul (smoothG_mul
      (smoothG_const ((-1 : ℂ) ^ ((i₁ : ℕ) + (i₂ : ℕ) + (j₁ : ℕ) + (j₂ : ℕ))))
      (smoothG_sub (smoothG_mul (hβ i₁) (hβ' i₂)) (smoothG_mul (hβ i₂) (hβ' i₁))))
      (smoothG_sub (smoothG_mul (ha j₁) (ha' j₂)) (smoothG_mul (ha j₂) (ha' j₁)))) (parOK_qminor (skip2 i₁ i₂) (skip2 j₁ j₂) u))
      (fun f g => by simp only [if_pos hc])
  · exact parOK_congr parOK_zero (fun f g => by simp only [if_neg hc])

theorem parOK_tL (z z' : Fin (2 * ρ + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    ParOK k ρ (E := E) (tL k ρ z z' (Fin.last ρ) Y p q) := by
  fin_cases p <;> fin_cases q
  · show ParOK k ρ (capL k ρ (Fin.last ρ) (uC k ρ (Fin.last ρ) Y))
    exact parOK_qminor id id _
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_const _) (fun j => smoothG_ybv z j))
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y) (yv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _))
  · show ParOK k ρ (fun f g => -(chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (yv k ρ z (Fin.last ρ)) (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chat2L _ _ _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _)
      (fun j => smoothG_ybv z j) (fun j => smoothG_const _))

end Ent

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

