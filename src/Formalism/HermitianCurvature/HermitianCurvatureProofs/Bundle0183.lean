module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0178
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHRepLin
section
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem repLin_nice {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp))
    (hG : GoodFam T j G) (t : ℂ) (ht : t ≠ 0) :
    ∃ ε, 0 < ε ∧ JC.NiceCoef (T.bs (j + 1)) ε (G t) := by
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 {t} isCompact_singleton (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact ht)
  have hsupp : ∀ γ, G t γ ≠ 0 → γ ∈ C := fun γ h => (hCε t rfl γ h).1
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t ht γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact ⟨ε, hε, hck, fun A' m' => JFxG.cptInCC_G hck hC (fun γ _ hγC => by
      by_contra h; exact hγC (hsupp γ h)) A' m', fun γ hγ hne => (hCε t rfl γ hne).2 hγ⟩

theorem representation_linear : RepLin := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j _ _ G G' hG hG' t ht a x hx
  obtain ⟨ε, hε, hN⟩ := repLin_nice T j G hG t ht
  obtain ⟨ε', hε', hN'⟩ := repLin_nice T j G' hG' t ht
  have hm : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G t) :=
    ⟨hN.1, hN.2.1, fun g hg hne => (min_le_left _ _).trans (hN.2.2 g hg hne)⟩
  have hm' : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G' t) :=
    ⟨hN'.1, hN'.2.1, fun g hg hne => (min_le_right _ _).trans (hN'.2.2 g hg hne)⟩
  have hom : wCell P.k (P.r - (j + 1)) (Fin.last (P.r - (j + 1))) x.1 * x.2 ∈
      JF.Om P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' :=
    TLB.wCell_om (Pa := JC.parLev P (j + 1)) (T.bs (j + 1)) hx
  have hs : B.JF (T.bs (j + 1)) (fun γ => a • G t γ) = a • B.JF (T.bs (j + 1)) (G t) :=
    funext fun h => JCx2.bc_JF_smul a (G t) h
  refine ⟨?_, ?_⟩
  · simp only [resG]
    rw [JCx2.bc_JF_add hm hm' hom, smul_add]
  · rw [hs, JCx2.rma_resG_smul]

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6.Lev0

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lev0Q {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (0 + ρ) + k + 1) → ℂ) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (ε : ℝ) (hε : 0 < ε)
    (A₀ A : ℝ) (mm : ℕ) (hA : A + 2 * (((0 + ρ : ℕ) : ℝ) + 1) * (mm : ℝ) ≤ A₀) :
    ∃ ε' C : ℝ, 0 < ε' ∧ 0 ≤ C ∧ ∀ (f : B.Mat k (0 + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm f c →
      B.CCle A mm (fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g) (C * c) ∧
      ∀ g ∈ B.GV k (0 + ρ), ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g ≠ 0 → ε' ≤ Gf k (0 + ρ) z z' g := by
  obtain ⟨δ, hδ, hG, hsupp⟩ := isCutG_div hχ hε
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k 0 ρ Wp Wq z z' 0 0 (idOp k (0 + ρ) Wp Wq) bumpOne
    (fun x => χ (x / ε)) (δ * ε) (inDD_idOp k ρ Wp Wq) isCutC_bumpOne hG mm mm A₀ (by simp)
  refine ⟨δ * ε, max C 0, by positivity, le_max_right _ _, fun f c hc => ?_⟩
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hS := hC f c hc
  have hF : B.opApply (idOp k (0 + ρ) Wp Wq) (U.cutDG k 0 ρ z z' bumpOne (fun x => χ (x / ε)) f) =
      fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g := by
    rw [opApply_idOp]
    funext g
    simp [U.cutDG, U.DjU, bumpOne_one]
  rw [hF] at hS
  obtain ⟨hck, -, hbd⟩ := hS
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.compactly_supported_monotone k (0 + ρ) _
      (A₀ - ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) - 2 * (((0 + ρ : ℕ) : ℝ) + 1) * ((mm + 0 : ℕ) : ℝ))
      A (C * c) mm _ ?_ ⟨hck, ?_⟩) (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0), ?_⟩
  · push_cast at hA ⊢; linarith
  · intro u v hu hv hl g hg
    refine hbd u v ?_ ?_ hl g hg
    · intro X hX; exact ⟨⟨(hu X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hu X hX).2⟩
    · intro X hX; exact ⟨⟨(hv X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hv X hX).2⟩
  · intro g hg hne
    have h1 : χ (Gf k (0 + ρ) z z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have h2 := hsupp _ h1
    rw [le_div_iff₀ hε] at h2
    linarith

def xs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) (p : C.LPt) (hc : r - i = r - D.ptSize p) (h : B.Mat k r → (Wq →L[ℂ] Wp))
    (a : Wd.Ix (Fin w.length)) : B.Mat k (r - i) → (Wq →L[ℂ] Wp) :=
  D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h ε) i hi w a) p)

theorem sliceQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (a : Wd.Ix (Fin w.length)),
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      (∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (xs T χ ε i hi w p hc h a) ∧
        B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xs T χ ε i hi w p hc h a) (K * c)) ∧
      ∀ (h₁ h₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV k r) h₁ → B.CkOn ⊤ (B.GV k r) h₂ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₁ c₁ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₂ c₂ →
        ∀ γ ∈ B.GV k (r - i), xs T χ ε i hi w p hc h₁ a γ - xs T χ ε i hi w p hc h₂ a γ =
          xs T χ ε i hi w p hc (fun g => h₁ g - h₂ g) a γ := by
  obtain ⟨Cp, hCp0, hL⟩ := levQ
  refine ⟨max 150 (16 * Cp), by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw p hc hp a
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    obtain rfl : p = [] := by
      cases p with
      | nil => rfl
      | cons b p =>
        exfalso
        have h1 := (hp.1 b (by simp)).1
        have h2 := hp.2
        simp [D.ptSize] at h2
        omega
    have hfun : ∀ h : B.Mat k r → (Wq →L[ℂ] Wp), xs T χ ε 0 hi w [] hc h a =
        (if a = Wd.e1 then D.cutF T.base χ h ε else 0) := by
      intro h
      funext γ
      have hcm : D.castM (k := k) (a := r - 0) (b := r - D.ptSize []) hc γ = γ := by
        ext i j; rfl
      simp only [xs, D.castF]
      rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem, Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
    obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
    have hb := Formalism.FourierDecayAlt.P.JCTx6.Link.budget0 (0 + ρ) k N hk2 A₀ Cc (le_trans (le_max_left _ _) hCc) hA₀
    obtain ⟨ε', C, hε', hC0, hQ⟩ := lev0Q (Wp := Wp) (Wq := Wq) T.base.z T.base.z' χ hχ ε hε A₀ (P5.Auser P0 N + 1) (P5.mmUser P0 N) (by
        simp only [P5.Auser, P5.mmUser, P5.nV, hPk, hPr]
        push_cast
        push_cast at hb
        linarith)
    have hmmM : P5.mmUser P0 N ≤ 3 * (11 * (N * (2 * (0 + ρ) + k + 1) ^ 2 + (2 * (0 + ρ) + k + 1) ^ 3) + 5) := by
      obtain ⟨-, -, b3, -, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs (0 + ρ) k N 0 0 hk2 (Nat.zero_le _) (Nat.zero_le _)
      have : P5.mmUser P0 N = 5 + 3 * ((0 + ρ) + 1) * (N + 2) * (2 * (0 + ρ) + k + 1) + N * (0 + ρ) := by
        simp only [P5.mmUser, P5.nV, hPk, hPr]
      omega
    refine ⟨ε', C, hε', hC0, ?_, ?_⟩
    · intro h c _ hcl
      have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hcl
      rw [hfun h]
      by_cases ha : a = Wd.e1
      · rw [if_pos ha]
        obtain ⟨q1, q2⟩ := hQ h c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmmM hcl)
        exact ⟨⟨q1.1, ⟨_, q1⟩, q2⟩, q1⟩
      · rw [if_neg ha]
        have hz : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (0 : B.Mat k (0 + ρ - 0) → (Wq →L[ℂ] Wp)) (C * c) :=
          Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (mul_nonneg hC0 hc0)
        exact ⟨⟨hz.1, ⟨_, hz⟩, fun g _ hne => (hne rfl).elim⟩, hz⟩
    · intro h₁ h₂ c₁ c₂ _ _ _ _ γ _
      rw [hfun h₁, hfun h₂, hfun (fun g => h₁ g - h₂ g)]
      by_cases ha : a = Wd.e1
      · simp only [if_pos ha, D.cutF, smul_sub]
      · simp only [if_neg ha, Pi.zero_apply, sub_zero]
  · obtain ⟨ε', K, hε', hK, hQ1, hQ2⟩ := hL Cc (le_trans (le_max_right _ _) hCc) k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ
      hA₀ ε hε i hi h1 w hw p hc hp a
    exact ⟨ε', K, hε', hK, hQ1, hQ2⟩

theorem auser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.Auser P0 L ≤ P5.Auser P0 N := by
  unfold P5.Auser
  have : (L : ℝ) ≤ N := by exact_mod_cast h
  gcongr

theorem mmUser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.mmUser P0 L ≤ P5.mmUser P0 N := by
  unfold P5.mmUser
  gcongr

theorem formLev_limit {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
      D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) (fun e => (hdx n e).1) (fun e => (hyn n e).1)).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) (fun e => (hdy n e).1) (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ n, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    intro n
    rw [key n]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx n e).2) (hv _ _ fun e => (hyn n e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy n e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) atTop (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero (fun n => norm_nonneg _) hbd hlim

end Formalism.FourierDecayAlt.P.PBE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSmulL
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section formh

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}

theorem form_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w 0 y = 0 := by
  have h := form_sl p j hj w 0 0 y 1 nv_zero nv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem form_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : NV (p.T.bs j) ε x) :
    p.form j hj w x 0 = 0 := by
  have h := form_sr p j hj w x 0 0 1 hx nv_zero nv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem form_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := form_sl p j hj w 0 x y c nv_zero hx hy
  rw [zero_add, form_zero_l p j hj w y hy, zero_add] at h
  exact h

theorem form_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := form_sr p j hj w x 0 y c hx nv_zero hy
  rw [zero_add, form_zero_r p j hj w x hx, zero_add] at h
  exact h

end formh

section block0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def uB (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  if hh : D.IsLocPt h j then
    (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)
  else 0

theorem dW_split (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) :
    dW S v j w h h' = (√(nnS S h) / bS S h) * (√(nnS S h') / bS S h') * (1 / (ΓS S j * S.sizeAt v w)) := by
  unfold dW; ring

theorem uB_nv {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) :
    ∃ ε', 0 < ε' ∧ NV ((p v).T.bs j) ε' (uB S p F v ε j hj w h) := by
  have hgpos := g_pos_of_built hB
  unfold uB
  split_ifs with hh
  · have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    obtain ⟨ε', hε', hn⟩ := slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH
    exact ⟨ε', hε', nv_smul _ hn⟩
  · exact ⟨1, one_pos, nv_zero⟩

end block0

section block0b

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem nv_pair {k ρ : ℕ} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] {Sx Sy : Type} {Bs : B.RealPlaceData k ρ Wp' Wq'} {x : Wd.Ix Sx → B.Mat k ρ → (Wq' →L[ℂ] Wp')}
    {y : Wd.Ix Sy → B.Mat k ρ → (Wq' →L[ℂ] Wp')}
    (hx : ∃ ε, 0 < ε ∧ NV Bs ε x) (hy : ∃ ε, 0 < ε ∧ NV Bs ε y) : ∃ ε, 0 < ε ∧ NV Bs ε x ∧ NV Bs ε y := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  exact ⟨min a b, lt_min ha hb, nv_mono hxa (min_le_left _ _), nv_mono hyb (min_le_right _ _)⟩

theorem gN_uB (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt) :
    KB.gN (setC S p F) v ε j w h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w (uB S p F v ε j hj w h) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [gN_setC_form hB F v ε j hj w h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dite_eq_left hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dite_eq_left hh']
    rw [e1, e2, form_smul_l (p v) j hj w _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hs hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [gN_setC_zero hB F v ε j w h h' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dite_eq_right (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dite_eq_right hh]
    rcases this with h0 | h0
    · rw [h0, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hx, mul_zero]

theorem hatB_uB (hA : P5.ThmPActual) (hPS : KB.PStd) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w (uB S p F v ε j hj w h)) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 (sW S j l) w _ hx
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [hatB_setC hA hPS hB F hF v ε hε j hj w hw l h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dite_eq_left hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dite_eq_left hh']
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 (sW S j l) w _ hs
    have ew : KB.waveG ((p v).T.bs j) (sW S j l) w ((((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) =
        (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) := by
      have := PBG.waveG_add_smul ((p v).T.bs j) (sW S j l) w 0
        (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) (((√(nnS S h) / bS S h : ℝ) : ℂ))
      rw [zero_add, PBG.waveG_zero, zero_add] at this
      exact this
    rw [e1, e2, ew, form_smul_l (p v) j hj w _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hws hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [hatB_setC_zero hB F v ε j w l h h' hsz hsz' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dite_eq_right (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dite_eq_right hh]
    rcases this with h0 | h0
    · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hwx, mul_zero]

theorem block0 (hA : P5.ThmPActual) (hPS : KB.PStd) (hVI : KB.VIso) (hFP : FormPos)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (Y : Finset C.LPt)
    (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y (KB.gN (setC S p F) v ε j w) (KB.hatB (setC S p F) v ε (j + 1) 1 w l)
      (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  obtain ⟨ε0, hε0, hall⟩ := nv_common Y (uB S p F v ε j hj w) (fun h _ => uB_nv hB F hF v ε hε j hj w h)
  set Dv := NV ((p v).T.bs j) ε0 (S := Fin w.length) with hDv
  refine block_iso Dv ((p v).form j hj w) nv_zero (fun x y hx hy => nv_add hx hy) (fun c x hx => nv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => form_sl (p v) j hj w x₁ x₂ y c h₁ h₂ hy)
    (fun x y₁ y₂ c hx h₁ h₂ => form_sr (p v) j hj w x y₁ y₂ c hx h₁ h₂)
    (fun x hx => hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x ε0 hε0 hx)
    (KB.waveG ((p v).T.bs j) (sW S j l) w) (fun x hx => PBFV.waveG_nice ((p v).T.bs j) ε0 (sW S j l) w x hx)
    (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x y ε0 hε0 hx hy).2)
    Y (fun h => if h ∈ Y then uB S p F v ε j hj w h else 0)
    (fun h => by by_cases hh : h ∈ Y <;> simp only [hh, if_true, if_false] <;> first | exact hall h hh | exact nv_zero)
    (1 / (ΓS S j * S.sizeAt v w)) ?_ _ _ ?_ ?_
  · have : 0 ≤ ΓS S j * S.sizeAt v w := by
      refine mul_nonneg ?_ (sizeAt_nonneg S v w)
      unfold ΓS
      have hgpos := g_pos_of_built hB
      have hrd := PBD.rd_pos' E
      exact (PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _).le
    positivity
  · intro h hh h' hh'
    simp only [hh, hh', if_true]
    exact gN_uB hB F hF v ε hε j hj w h h'
  · intro h hh h' hh'
    simp only [hh, hh', if_true]
    exact hatB_uB hA hPS hB F hF v ε hε j hj w hw l h h' (hY h hh) (hY h' hh')

end block0b

end

end Formalism.FourierDecayAlt.P.PBL
end

