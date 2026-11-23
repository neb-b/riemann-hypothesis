module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField PI.UnitaryGroupMassFormula.GsFr
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def kcut (t : ℝ) : ℝ := Real.smoothTransition (6 * t - 2)

theorem kcut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kcut :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem kcut_zero {t : ℝ} (ht : t ≤ 1 / 3) : kcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem kcut_one {t : ℝ} (ht : 1 / 2 ≤ t) : kcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def NrmWFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) ∧
    ∀ h ∈ UWset k r z, ∀ a, PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a

theorem nrmW_smul {k r : ℕ} (z a : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PRho.nrmW k r z (c • a) = Complex.normSq c * PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]
  rw [hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]

section lm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def lmul (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

theorem lmul_apply (A : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) : lmul A X = A.comp X := rfl

theorem hsInner_lmul (A : Wp →L[ℂ] Wp) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (lmul A X) Y = B.hsInner X (lmul A Y) := by
  simp only [B.hsInner, B.hsVec, lmul_apply, PiLp.inner_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA]

end lm

theorem typeProj_of (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines) (hDU : SSn.Rep.DatumUnit)
    (hNW : NrmWFacts) : TypeProj := by
  refine ⟨0, le_rfl, ?_⟩
  intro Cc _ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  by_cases hk : 2 ≤ S.G.k
  · obtain ⟨Pr, hs, heqv, hrest⟩ := hPE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
    obtain ⟨hnc, hninv⟩ := hNW S.G.k S.G.r (T v).base.z (T v).base.z_mem (T v).base.T_pos
    refine ⟨fun σ a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a), ?_, ?_, ?_, ?_⟩
    ·
      intro σ
      rw [contDiff_iff_contDiffAt]
      intro a₀
      by_cases h : 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a₀
      · have hO : IsOpen {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          isOpen_lt continuous_const hnc.continuous
        have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun A : Wp (S.pl v) →L[ℂ] Wp (S.pl v) => (lmul A : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] _)) :=
          (ContinuousLinearMap.compL ℂ (Wq (S.pl v)) (Wp (S.pl v)) (Wp (S.pl v))).contDiff.restrict_scalars ℝ
        have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a))
            {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          ((Complex.ofRealCLM.contDiff.comp (kcut_contDiff.comp hnc)).contDiffOn).smul
            (hl.comp_contDiffOn (hs σ))
        exact h1.contDiffAt (hO.mem_nhds h)
      · have hO : IsOpen {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} :=
          isOpen_lt hnc.continuous continuous_const
        have hmem : a₀ ∈ {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} := by
          simp only [Set.mem_setOf_eq]; linarith [not_lt.1 h]
        refine (contDiffAt_const (c := (0 : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))).congr_of_eventuallyEq ?_
        filter_upwards [hO.mem_nhds hmem] with a ha
        simp [kcut_zero (le_of_lt ha)]
    ·
      intro σ a A B'
      dsimp only
      by_cases h : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z a
      · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, kap_hsInner_smul_left,
          kap_hsInner_smul_right, Complex.conj_ofReal, hsInner_lmul _ ((hrest a h).2.1 σ)]
      · have h0 : kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) = 0 := kcut_zero (by linarith [not_lt.1 h])
        simp [h0, B.hsInner, kap_hsVec_zero]
    ·
      intro σ h hh h' hh' a X
      have hinv : h⁻¹ ∈ UWset S.G.k S.G.r (T v).base.z := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      have hh1 : h⁻¹ * h = 1 := by
        first
          | exact Matrix.nonsing_inv_mul _ hu
          | exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
      have key : ∀ y, (T v).base.π h⁻¹ ((T v).base.π h y) = y := by
        intro y
        rw [← ContinuousLinearMap.comp_apply, ← (T v).base.π_rep.2 _ hinv _ hh, hh1, (T v).base.π_rep.1]
        rfl
      dsimp only
      rw [hninv h hh a, heqv h hh σ a]
      ext y
      simp [lmul_apply, key]
    ·
      intro x hx σ ρ
      dsimp only
      obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v x.2 hx.2
      set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2 with hn0
      have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
        unfold PRho.nrmW; rw [hP1, hH1]; simp
      have hph : SSn.phD x.1 ≠ 0 := by
        intro h0
        have := SSn.Geom.phD_norm hx.1
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      have hN : PRho.nrmW S.G.k S.G.r (T v).base.z (SSn.phD x.1 • n0) = 1 := by
        rw [nrmW_smul, hN0, mul_one, Complex.normSq_eq_norm_sq, SSn.Geom.phD_norm hx.1]; norm_num
      have hscale : ∀ τ, Pr τ (SSn.phD x.1 • n0) = Pr τ n0 :=
        fun τ => (hrest n0 (by rw [hN0]; norm_num)).1 τ _ hph
      have hfix : ∀ y, Pr ρ n0 (e ρ x.2 y) = e ρ x.2 y := by
        intro y
        refine ((hrest n0 (by rw [hN0]; norm_num)).2.2.2 ρ (e ρ x.2 y)).2 ?_
        intro Fr hFrm w
        rw [hP1] at hFrm
        exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk x.2 hx.2 ρ Fr hFrm w y
      rw [ContinuousLinearMap.smul_apply, hN, kcut_one (by norm_num), lmul_apply, hscale]
      simp only [Complex.ofReal_one, one_smul]
      by_cases hσ : σ = ρ
      · subst hσ
        rw [if_pos rfl]
        ext y
        exact hfix y
      · rw [if_neg hσ]
        ext y
        have horth := (hrest n0 (by rw [hN0]; norm_num)).2.2.1 σ ρ
        rw [if_neg hσ] at horth
        rw [ContinuousLinearMap.comp_apply, ← hfix y, ← ContinuousLinearMap.comp_apply (Pr σ n0), horth]
        rfl
  ·
    have hk1 : (D.parOf S v).k - 1 = 0 := by
      have : (D.parOf S v).k = S.G.k := rfl
      omega
    have hsub : ∀ σ ρ : M.Ty (D.parOf S v), σ = ρ := by
      intro σ ρ
      funext i
      exact absurd i.2 (by omega)
    refine ⟨fun _ _ => ContinuousLinearMap.id ℂ _, fun σ => contDiff_const, fun σ a A B' => rfl,
      fun σ h _ h' _ a X => rfl, ?_⟩
    intro x _ σ ρ
    rw [if_pos (hsub σ ρ)]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd
section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pair

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂]

theorem ssn_ckOn_subset {m : ℕ∞} {UU UU' : Set (Mat k r)} {f : Mat k r → E₁} (h : CkOn m UU f) (hs : UU' ⊆ UU) :
    CkOn m UU' f := fun g hg => h g (hs hg)

theorem ssn_ckOn_pair {m : ℕ∞} {UU : Set (Mat k r)} {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn m UU f₁) (h₂ : CkOn m UU f₂) : CkOn m UU (fun g => (f₁ g, f₂ g)) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => (f₁' g, f₂' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).prodMk (hc₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show (f₁ g, f₂ g) = (f₁' g, f₂' g)
  rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]

theorem ssn_Dw_pair {U : Set (Mat k r)} (hU : IsOpen U) {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn ⊤ (U ∩ GV k r) f₁) (h₂ : CkOn ⊤ (U ∩ GV k r) f₂) :
    ∀ w : List (Bool × Mat k r), (∀ x ∈ w, inLie k r x.2) → ∀ g ∈ GV k r, g ∈ U →
      Dw w (fun g => (f₁ g, f₂ g)) g = (Dw w f₁ g, Dw w f₂ g) := by
  intro w
  induction w with
  | nil => intro _ g _ _; rfl
  | cons x w ih =>
    intro hw g hg hgU
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    show Dx x (Dw w (fun g => (f₁ g, f₂ g))) g = (Dx x (Dw w f₁) g, Dx x (Dw w f₂) g)
    rw [Dx_congr_loc hx hU (f₂ := fun g => (Dw w f₁ g, Dw w f₂ g)) (fun g hg hgU => ih hw' g hg hgU) g hg hgU]
    have c₁ : CkOn 1 (U ∩ GV k r) (Dw w f₁) := CkOn_Dw hw' (sCkOn_mono le_top h₁)
    have c₂ : CkOn 1 (U ∩ GV k r) (Dw w f₂) := CkOn_Dw hw' (sCkOn_mono le_top h₂)
    have d₁ := CkOn_diff hx c₁ ⟨hgU, hg⟩ hg
    have d₂ := CkOn_diff hx c₂ ⟨hgU, hg⟩ hg
    rw [Dx_eq]
    exact (d₁.prodMk d₂).deriv

end pair

theorem datumBd_of_chain (hCh : SSn.ChainBd) : DatumBd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v Bg a a' ι Ψ hBg hD hΨ
  intro ε hε m
  set U : Set (B.Mat S.G.k S.G.r) := {g | ε / 2 < GfP S T v g} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  set K : Set (B.Mat S.G.k S.G.r) := {g | g ∈ B.GV S.G.k S.G.r ∧ ε ≤ GfP S T v g} with hKdef
  have hUG : U ∩ B.GV S.G.k S.G.r ⊆ B.GPos (T v).base := fun g hg =>
    ⟨hg.2, lt_trans (by linarith) hg.1⟩
  have hKU : K ⊆ U := fun g hg => show ε / 2 < GfP S T v g by linarith [hg.2]
  have hKG : K ⊆ B.GV S.G.k S.G.r := fun g hg => hg.1
  set F : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      B.Mat S.G.k S.G.r := fun g => (a g, (a' g, ι g)) with hFdef
  have cka : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a := ssn_ckOn_subset hD.1 hUG
  have cka' : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a' := ssn_ckOn_subset hD.2.1 hUG
  have ckι : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) ι := ssn_ckOn_subset hD.2.2.1 hUG
  have ckF : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) F := ssn_ckOn_pair cka (ssn_ckOn_pair cka' ckι)
  have hFb : ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r), (∀ X ∈ u, unitLie S.G.k S.G.r X) →
      (∀ X ∈ w, unitLie S.G.k S.G.r X) → u.length + w.length ≤ m → ∀ g ∈ K,
        ‖dLR u w F g‖ ≤ C * gN g ^ (Bg * m) := by
    intro m
    obtain ⟨C₁, h₁⟩ := hD.2.2.2.2.1 ε hε m
    obtain ⟨C₂, h₂⟩ := hD.2.2.2.2.2.1 ε hε m
    obtain ⟨C₃, h₃⟩ := hD.2.2.2.2.2.2.1 ε hε m
    refine ⟨C₁ + C₂ + C₃, fun u w hu hw hl g hg => ?_⟩
    have hlie := lie_LR (unit_lie hu) (unit_lie hw)
    have e1 : dLR u w F g = (dLR u w a g, (dLR u w a' g, dLR u w ι g)) := by
      rw [dLR_eq, dLR_eq, dLR_eq, dLR_eq]
      rw [ssn_Dw_pair hUo cka (ssn_ckOn_pair cka' ckι) _ hlie g hg.1 (hKU hg),
        ssn_Dw_pair hUo cka' ckι _ hlie g hg.1 (hKU hg)]
    rw [e1]
    have b₁ := h₁ u w hu hw hl g hg.1 hg.2
    have b₂ := h₂ u w hu hw hl g hg.1 hg.2
    have b₃ := h₃ u w hu hw hl g hg.1 hg.2
    calc ‖(dLR u w a g, (dLR u w a' g, dLR u w ι g))‖
        ≤ ‖dLR u w a g‖ + (‖dLR u w a' g‖ + ‖dLR u w ι g‖) :=
          (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (by positivity),
            (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (norm_nonneg _),
              le_add_of_nonneg_left (norm_nonneg _)⟩).trans (le_add_of_nonneg_left (norm_nonneg _))⟩)
      _ ≤ C₁ * gN g ^ (Bg * m) + (C₂ * gN g ^ (Bg * m) + C₃ * gN g ^ (Bg * m)) := by
          linarith
      _ = (C₁ + C₂ + C₃) * gN g ^ (Bg * m) := by ring
  obtain ⟨C, hC⟩ := hCh S.G.k S.G.r _ _ (fun x => Ψ x.1 x.2.1 x.2.2) hΨ F U K hUo ckF hKU hKG Bg hBg hFb m
  refine ⟨C, fun u w hu hw hl g hg hεg => ?_⟩
  have hgK : g ∈ K := ⟨hg, hεg⟩
  have hO : IsOpen {g : B.Mat S.G.k S.G.r | 0 < GfP S T v g} :=
    isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  have hlie := lie_LR (unit_lie hu) (unit_lie hw)
  have e : dLR u w (datumCoef S T v Ψ a a' ι) g = dLR u w (fun g => (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r => Ψ x.1 x.2.1 x.2.2) (F g)) g := by
    rw [dLR_eq, dLR_eq]
    refine Dw_congr_loc hlie hO (fun g' hg' hg'O => ?_) g hg (show 0 < GfP S T v g by linarith)
    exact datumCoef_pos S T v a a' ι Ψ ⟨hg', hg'O⟩
  rw [e]
  exact hC u w hu hw hl g hgK

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjIntAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem hasCompactSupport_rho (D : B.RealPlaceData k r Wp Wq) {q : B.SS k r} (hq : D.inSS q)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : HasCompactSupport F) : HasCompactSupport (B.rho D q F) := by
  have ha := Formalism.FourierDecayAlt.P.B5.inSS_left D hq
  have hb := Formalism.FourierDecayAlt.P.B5.inSS_right D hq
  have himg : B.sgs q ⁻¹' tsupport F ⊆ (fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F := by
    intro x hx
    refine ⟨B.sgs q x, hx, ?_⟩
    dsimp only
    rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
    have key : ∀ (a b y : B.Mat k r), a * a⁻¹ = 1 → b * b⁻¹ = 1 → a * (a⁻¹ * y * b) * b⁻¹ = y := by
      intro a b y ha hb
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hb, Matrix.mul_one, ← Matrix.mul_assoc, ha, Matrix.one_mul]
    exact key _ _ x (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv ha).1 (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hb).1
  have hcK : IsCompact ((fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F) :=
    hF.image ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  refine hcK.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => himg (subset_tsupport _ ?_)) hcK.isClosed)
  intro h0
  apply hx
  show B.rho D q F x = 0
  unfold B.rho
  rw [h0]
  simp

variable [FiniteDimensional ℂ Wq]

noncomputable def II (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG

theorem ii_swap (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : II D X Y = conj (II D Y X) := by
  unfold II
  rw [← integral_conj]
  congr 1
  funext x
  unfold B.hsInner
  rw [inner_conj_symm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hermitian_curvature_adjoint_integral : AdjIntAsm := by
  intro hU hF k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp φ hφ hφc hφs
  obtain ⟨p', hp', hUp⟩ := hU k r Wp Wq D p hp
  have hU' : ∀ X Y, II D (B.rho D p X) Y = II D X (B.rho D p' Y) := hUp
  have hF' : ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F →
      B.SuppIn (B.GPos D) F → B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      II D (B.opApply Θ F) F' = II D F (B.opAdj Θ F') := hF k r Wp Wq D Θ hs hc
  have hcomm : II D (B.opApply Θ (B.rho D p' φ)) f = II D (B.rho D p' (B.opApply Θ φ)) f := by
    unfold II
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
    by_cases hxp : Matrix.of x ∈ B.GPos D
    · rw [hc p' hp' φ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hφ) _ hxp]
    · have h0 : f (Matrix.of x) = 0 := by
        by_contra hne
        exact hxp (hfs (subset_closure ⟨hx, hne⟩))
      simp only [h0, Formalism.FourierDecayAlt.P.B5.hs_zero_right]
  show II D (B.opAdj Θ (B.rho D p f)) φ = II D (B.rho D p (B.opAdj Θ f)) φ
  calc II D (B.opAdj Θ (B.rho D p f)) φ = conj (II D φ (B.opAdj Θ (B.rho D p f))) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ φ) (B.rho D p f)) := by
        rw [hF' φ (B.rho D p f) hφ hφc hφs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (hasCompactSupport_rho D hp hfc)
          (suppIn_rho D hp hfs)]
    _ = II D (B.rho D p f) (B.opApply Θ φ) := (ii_swap D _ _).symm
    _ = II D f (B.rho D p' (B.opApply Θ φ)) := hU' _ _
    _ = conj (II D (B.rho D p' (B.opApply Θ φ)) f) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ (B.rho D p' φ)) f) := by rw [hcomm]
    _ = conj (II D (B.rho D p' φ) (B.opAdj Θ f)) := by
        rw [hF' (B.rho D p' φ) f (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp' hφ) (hasCompactSupport_rho D hp' hφc)
          (suppIn_rho D hp' hφs) hf hfc hfs]
    _ = II D (B.opAdj Θ f) (B.rho D p' φ) := (ii_swap D _ _).symm
    _ = II D (B.rho D p (B.opAdj Θ f)) φ := (hU' _ _).symm

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjJComm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gAJComm_of_thetaJ (hT : LT.ThetaJ) : GAJComm := by
  refine ⟨12, 0, by norm_num, le_rfl, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d Bg hd hBg hΘ _hCoef η F _hη hFs hFg _hFsupp
    U J hU hJ hagree x hx hxU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hBg0 : 0 ≤ Bg := le_trans (by simp) hBg

  have hAg := LT.agreement_on_domain_holds S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base J F U hJ
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    (fun g => Gf S.G.k S.G.r (T v).base.z (T v).base.z' g) ⁻¹' U with hVdef
  have hVo : IsOpen V := (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _).inter
    (hU.preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))
  have hJV : ∀ y ∈ V, y ∈ B.GV S.G.k S.G.r → J y = B.JF (T v).base F y := fun y hy hyG =>
    hAg y ⟨hyG, hy.1⟩ hy.2
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base x ∈ V := ⟨hg0.2, hxU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hJ.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base x ∈ UU := ⟨hg0, hg0V⟩

  have hThr : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold S.G.k S.G.r
      (B.AB S.G.k S.G.r + 12 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5) -
        Bg * ((B.opOrder Θ : ℕ) : ℝ)) (B.opOrder Θ) := by
    have hAB : (0 : ℝ) ≤ B.AB S.G.k S.G.r := by unfold B.AB; positivity
    have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have ho : (0 : ℝ) ≤ (B.opOrder Θ : ℝ) := Nat.cast_nonneg _
    apply Formalism.FourierDecayAlt.P.CutMP.jdc_thrW (B.opOrder Θ) _ (B.AB S.G.k S.G.r + 30 * (S.G.r : ℝ) + d +
      Bg * ((B.opOrder Θ : ℝ) + 10)) (by positivity)
    linarith
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU hThr hΘ.1 hΘ.2 hFs
    (hFg (B.opOrder Θ)) hUU hCkF

  have hg0G : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun y => Tm.coefAdj y (J y)) (f' := fun y => Tm.coefAdj y (B.JF (T v).base F y))
      (fun y hy hyG => by simp only [hJV y hy hyG]) _ hg0V hg0G]

theorem gAJComm_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : GAJComm :=
  gAJComm_of_thetaJ (LT.thetaJ_of_adjComm hAC)

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end

