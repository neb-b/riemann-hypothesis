module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0119
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0186
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem hsInner_zero_left' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_right]

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_zero_small (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    {G : B.Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g)
    (q : C.LPt) (hq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q < ε) : D.vecV Bs ν' m₀ G q = 0 := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) G (fun _ => 0) 0 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        have hz : G (B.sgs p h'.choose) = 0 := by
          by_contra hne
          have h1 := hG _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hne
          rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, ← hGq] at h1
          linarith
        simp [D.orbIntegrand, B.rho, hz])
      rw [e, zero_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

theorem rr_top_small {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℂ, Complex.normSq c - P.T * P.T' < δ →
      p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
  classical

  have hθc := fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hθ hF hw
  choose F' hF'c hF'd hF'v using hθc
  obtain ⟨εF, hεF, hGF⟩ := hF.2.2
  choose εe hεe hGe using fun e => (hF'c e).2.2
  let Sε : Finset ℝ := insert εF (Finset.univ.image εe)
  have hne : Sε.Nonempty := ⟨εF, Finset.mem_insert_self _ _⟩
  set ε := Sε.min' hne with hεdef
  have hε : 0 < ε := by
    rw [hεdef, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hεF
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεe a
  have hεF' : ε ≤ εF := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hεe' : ∀ e, ε ≤ εe e := fun e =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ e)))
  set Dh := Complex.normSq (D.ptMatN h P.r).det with hDh
  have hD0 : 0 ≤ Dh := Complex.normSq_nonneg _
  have hD1 : 0 < Dh + 1 := by linarith
  refine ⟨ε / (Dh + 1), div_pos hε hD1, fun c hc => ?_⟩
  have hTT : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' = P.T * P.T' := by
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  have hpt : D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (h ++ [(1, c)]) < ε := by
    rw [hTT, Formalism.FourierDecayAlt.P.PBD.ptG_app _ c h P.r hh.2]
    by_cases hs : Complex.normSq c - P.T * P.T' ≤ 0
    · have : Dh * (Complex.normSq c - P.T * P.T') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD0 hs
      linarith
    · push Not at hs
      have h1 : Dh * (Complex.normSq c - P.T * P.T') ≤ (Dh + 1) * (Complex.normSq c - P.T * P.T') := by nlinarith
      have h2 : (Dh + 1) * (Complex.normSq c - P.T * P.T') < (Dh + 1) * (ε / (Dh + 1)) :=
        mul_lt_mul_of_pos_left hc hD1
      rw [mul_div_cancel₀ _ hD1.ne'] at h2
      linarith
  unfold KB.Pl.RR D.RRplace
  split_ifs with hloc hi hi2 hw0
  · omega
  · have hv : D.vecV p.T.base p.ν' p.m₀ F (h ++ [(1, c)]) = 0 :=
      vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans hεF' (hGF g hg h0)) _ hpt
    rw [hv, hsInner_zero_left']
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    have hv : D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h ++ [(1, c)]) = 0 := by
      have := hF'v e (h ++ [(1, c)])
      unfold KB.Pl.V at this
      rw [this]
      exact vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans (hεe' e) (hGe e g hg h0)) _ hpt
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left', mul_zero]
  · omega
  · rfl

section law

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zetaNorm_map {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ) :
    μ.map (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      (volume : Measure ℂ).withDensity (Formalism.FourierDecayAlt.P.JCx2.rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
  rw [lintegral_map hψ hf, hμ.2 ψ hψ, lintegral_withDensity_eq_lintegral_mul _ (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _) hψ]
  rfl

theorem zetaNorm_integral {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ) :
    ∫ g, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) ∂μ =
      ∫ ζ, (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  rw [← integral_map hf.aemeasurable hψ.aestronglyMeasurable, zetaNorm_map hμ,
    integral_withDensity_eq_integral_toReal_smul (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
      (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

theorem zetaNorm_integrable {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ)
    (hi : Integrable (fun g => ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g))) μ) :
    Integrable (fun ζ => (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  have h1 : Integrable ψ (μ.map fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) :=
    (integrable_map_measure hψ.aestronglyMeasurable hf.aemeasurable).2 hi
  rw [zetaNorm_map hμ, integrable_withDensity_iff_integrable_smul' (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
    (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

end law

section pic

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pic_cpt {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (K0 : Submodule ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π'))
    (hJ : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
        (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
      (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2 := by
  classical
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  set F₂ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => if g ∈ B.GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ B.GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hs₂ : B.CkOn ⊤ (B.GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun g hg hgG => by rw [he g hgG, hfe g hg hgG]⟩
  have hz : ∀ g, g ∉ {g : B.Mat k r | B.gN g ≤ R} → F₂ g = 0 := by
    intro g hg
    by_cases hgG : g ∈ B.GV k r
    · rw [he g hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · simp [hF₂, hgG]
  have hC := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
  obtain ⟨Φ, hΦK, hΦ⟩ := hJ F₂ ε hε
    (fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs₂ hC (fun g _ hgC => hz g hgC) A m)
    (HasCompactSupport.intro hC hz)
    (fun g hg h0 => hG g hg (by rwa [he g hg] at h0))
  refine ⟨Φ, hΦK, fun x hx => ?_⟩
  rw [hΦ x hx]
  have hGV : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hx.1 (by simp)) hx.2.1.1
  simp only [resG]
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (a := 1) (fun g hg => by rw [he g hg, one_smul]) hGV, one_smul]

end pic

def TopContOn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (hh' : D.IsLocPt h' P.r) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F →
    KB.CutWord P p.l0 w →
    ContinuousOn (fun c : ℂ => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]))
      {c : ℂ | P.T * P.T' < Complex.normSq c}

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismCompactSupport
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem vIsoCpt_main : Formalism.FourierDecayAlt.KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'

  obtain ⟨ε, hε, hεall⟩ := Formalism.FourierDecayAlt.P.JCx2.exists_common_eps
    (fun (i : Bool × Wd.Ix (Fin w.length)) ε => JC.NiceCoef (p.T.bs j) ε (if i.1 then x i.2 else x' i.2))
    (fun i ε ε' _ h hF => nice_mono h hF)
    (fun i => by
      rcases i with ⟨b, e⟩
      cases b
      · exact Formalism.FourierDecayAlt.P.TLB.nice_of_cpt (hx' e)
      · exact Formalism.FourierDecayAlt.P.TLB.nice_of_cpt (hx e))
  have hxN : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e) := fun e => by simpa using hεall (true, e)
  have hx'N : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e) := fun e => by simpa using hεall (false, e)
  obtain ⟨R, hR⟩ := common_R (fun i : Bool × Wd.Ix (Fin w.length) => if i.1 then x i.2 else x' i.2)
    (fun i => by
      rcases i with ⟨b, e⟩
      cases b
      · exact (hx' e).2.1
      · exact (hx e).2.1)
  have hxR : ∀ e, ∀ g ∈ B.GV P.k (P.r - j), x e g ≠ 0 → B.gN g ≤ R := fun e => by simpa using hR (true, e)
  have hx'R : ∀ e, ∀ g ∈ B.GV P.k (P.r - j), x' e g ≠ 0 → B.gN g ≤ R := fun e => by simpa using hR (false, e)
  have hwN := waveG_nice (p.T.bs j) ε s w x hxN
  refine ⟨fun e => ⟨(hwN e).1, ⟨R, waveG_bs (p.T.bs j) s w x R hxR e⟩, ε, hε, (hwN e).2.2⟩, ?_⟩
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hJ : ∀ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), JC.NiceCoef (p.T.bs jF) ε F →
      (∃ R : ℝ, ∀ g ∈ B.GV P.k (P.r - j), F g ≠ 0 → B.gN g ≤ R) →
      ∃ Φ ∈ K 0, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Φ : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) F) y.1 y.2 := by
    rintro F hF ⟨R', hR'⟩
    exact Formalism.FourierDecayAlt.P.PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε hF hR'
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  choose Φ hΦK hΦ using fun a => hJ (x a) (hxN a) ⟨R, hxR a⟩
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) (hx'N a) ⟨R, hx'R a⟩
  have hnx := waveG_nice (p.T.bs j) ε s w x hxN
  have hnx' := waveG_nice (p.T.bs j) ε s w x' hx'N
  show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') =
    D.formLev p.T (M.sgn P p.l0) jF w x x'
  have hmem : ∀ (Wv Wv' : Module.End ℂ (RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π')) (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r
      (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'),
      (∀ e, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Ψ' e : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) (KB.waveG (p.T.bs j) s w x' e))
            y.1 y.2) → InK (K 0) Ψ' := by
    intro _ _ Ψ' hΨ' e
    obtain ⟨Ψ0, hΨ0K, hΨ0⟩ := hJ (KB.waveG (p.T.bs j) s w x' e) (hnx' e) ⟨R, waveG_bs (p.T.bs j) s w x' R hx'R e⟩
    have : Ψ' e = Ψ0 := radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)
    rw [this]
    exact hΨ0K
  by_cases hr : 0 < P.r - j
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hxN Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx'N Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hxN hx'N hΦ hΦ']
    congr 1
    have key := rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))
  · have hr0 : P.r - j = 0 := by omega
    obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_top_eq_zeta hr0]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hxN Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx'N Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hxN hx'N hΦ hΦ']
    congr 1
    have key := rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))

end Formalism.FourierDecayAlt.P.PBFV

namespace Formalism.FourierDecayAlt.P

theorem vector_isomorphism_compact_support : Formalism.FourierDecayAlt.KB.VIsoCpt := Formalism.FourierDecayAlt.P.PBFV.vIsoCpt_main

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellAction
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section row

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n r : ℕ}

theorem unit_matrix_zero_mul_apply (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (i : Fin 2) (e : Ix (Fin n)) (m : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      if (0 : Fin 2) = i then N (Fin.cons 0 e) m else 0 := by
  rw [Matrix.mul_apply]
  simp only [insert_unit_matrix_zero_apply, ite_mul, one_mul, zero_mul]
  by_cases hi : (0 : Fin 2) = i
  · subst hi
    simp
  · simp [hi]

theorem row_sum (col : Fin 2 → SlopeTestRemainingChoices (Fin (n + 1)) A) (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (e : Ix (Fin n))
    (m : Ix (Fin (n + 1))) :
    ((∑ i : Fin 2, eU (0 : Fin (n + 1)) i 0 * col i) * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      (col 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m := by
  rw [Finset.sum_mul, Matrix.sum_apply, Fin.sum_univ_two, mul_assoc, mul_assoc, unit_matrix_zero_mul_apply, unit_matrix_zero_mul_apply]
  simp

theorem io_mul_apply {S : Type} [Fintype S] [DecidableEq S] (x : A) (N : SlopeTestRemainingChoices S A) (z m : Ix S) :
    (io x * N : SlopeTestRemainingChoices S A) z m = x * N z m := by
  rw [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem firstRow (hWS : TL.WordStep) (L : LevelData A r) (st : Start A) (hA : TL.AHyp L st) (y : ℂ)
    (u : List (Letter ℂ (Fin n))) (hadm : admitted st (⟨true, 0, y⟩ :: u.map upL)) (e : Ix (Fin n)) :
    ((ofWord L st (⟨true, 0, y⟩ :: u.map upL)).F * TL.bTA L (⟨true, 0, y⟩ :: u.map upL)) (Fin.cons 0 e) e1 =
      TL.aP L y * ((ofWord L st u).F * TL.bTA L u) e e1 := by
  rw [hWS A (Fin (n + 1)) r L st ⟨true, 0, y⟩ (u.map upL) hA hadm (Fin.cons 0 e)]
  rw [(lifted_ofWord L st u).F, bTA_lift, ← liftM_mul]
  dsimp only
  rw [row_sum]
  simp only [TL.letterCol, ↓reduceIte, Matrix.cons_val_zero]
  rw [io_mul_apply, liftM_apply]
  congr 1

end row

section act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_e1Vec (M : SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (x : Ix S) :
    P5.act M (Top.firstStateVector Φ) x = (M x e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (e1 : Ix S)]
  · split_ifs with h
    · rfl
    · exact absurd rfl h
  · intro b _ hb
    have hb' : ¬(b = fun _ => 0) := hb
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

end act

theorem cutWord_tail {P : M.Par} {l0 : ℕ} {l : C.Letter} {w : List C.Letter} (h : KB.CutWord P l0 (l :: w)) :
    KB.CutWord P l0 w := by
  refine ⟨fun a => h.1 a.succ, fun a b hab => h.2 a.succ b.succ fun e => hab (Fin.succ_injective _ e)⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rad_plus (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq) (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter) (y : ℝ)
    (hcut : KB.CutWord P p.l0 ((true, y) :: w)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (e : Ix (Fin w.length)) :
    P5.act ((Fr.ofWord L st (D.positionted ((true, y) :: w))).F * P5.bTall L (D.positionted ((true, y) :: w)))
        (Top.firstStateVector Φ) (Fin.cons 0 e) =
      (TL.aP L (y : ℂ)).1 (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  have hA := (Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st p.l0 hD).1
  have hOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' st p.l0 p.hP.1 p.hl.1
    p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 ((true, y) :: w) hcut.1 hcut.2
  have hadm := hOK.1
  rw [act_e1Vec, act_e1Vec]
  rw [positioned_cons] at hadm ⊢
  exact congrArg (fun x : Q.Pr _ => x.1 Φ) (firstRow hWS L st hA (y : ℂ) (D.positionted w) hadm e)

end main

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

end Formalism.FourierDecayAlt.P
end
end

