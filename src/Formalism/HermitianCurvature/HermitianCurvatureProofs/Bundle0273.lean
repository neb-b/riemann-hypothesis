module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0271
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0272
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def cutN (k r n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

def apx {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (G : B.Mat k r → (Wq →L[ℂ] Wp)) (n : ℕ) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => cutN k r n g • G g

theorem cptCoef_apx {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) : KB.CptCoef Bs (apx (D.cutF Bs χ F ε) n) := by
  letI : NormedAddCommGroup (B.Mat P.k P.r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat P.k P.r) := Matrix.normedSpace
  obtain ⟨hχs, ⟨δ, hδ, hχ0⟩, -⟩ := hχ
  refine ⟨?_, ⟨2 * ((n : ℝ) + 1), ?_⟩, ⟨δ * ε, mul_pos hδ hε, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', hFe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => cutN P.k P.r n g • (((χ (Gf P.k P.r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F' g),
      hU, hgU, ?_, ?_⟩
    · have hn2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
        have e : (fun z : ℂ => Complex.normSq z) = fun z => z.re * z.re + z.im * z.im := by
          funext z
          exact Complex.normSq_apply z
        rw [e]
        exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
          (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
      have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat P.k P.r => cutN P.k P.r n g) := by
        unfold cutN
        refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
        refine (contDiff_const.sub ?_).div_const _
        refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => hn2.comp ?_
        exact (contDiff_apply_apply ℝ i j).comp (contDiff_id.const_smul (((n : ℝ) + 1)⁻¹))
      exact hc.contDiffOn.smul ((Complex.ofRealCLM.contDiff.comp
        (hχs.comp ((JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))).contDiffOn.smul hF')
    · intro g hg hgv
      simp only [apx, D.cutF]
      rw [hFe g hg hgv]
  · intro g _ hne
    have h1 : cutN P.k P.r n g ≠ 0 := by
      intro h0
      apply hne
      simp only [apx, h0, zero_smul]
    simp only [cutN, ne_eq, Complex.ofReal_eq_zero, Real.smoothTransition.zero_iff_nonpos, not_le] at h1
    have hs : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) < 4 := by
      have := (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).1 h1
      linarith
    have heq : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
        ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hS : ∑ i, ∑ j, Complex.normSq (g i j) ≤ (2 * ((n : ℝ) + 1)) ^ 2 := by
      rw [heq, inv_pow, inv_mul_lt_iff₀ (by positivity)] at hs
      have e2 : (2 * ((n : ℝ) + 1)) ^ 2 = ((n : ℝ) + 1) ^ 2 * 4 := by ring
      rw [e2]
      exact hs.le
    unfold B.gN
    calc Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) :=
          Real.sqrt_le_sqrt hS
      _ = 2 * ((n : ℝ) + 1) := Real.sqrt_sq (by positivity)
  · intro g _ hne
    have h1 : ((χ (Gf P.k P.r Bs.z Bs.z' g / ε) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      apply hne
      simp only [apx, D.cutF, h0, zero_smul, smul_zero]
    have h2 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε := by
      by_contra hlt
      push_neg at hlt
      exact h1 (by rw [hχ0 _ hlt]; simp)
    rwa [le_div_iff₀ hε] at h2

section fpmCk

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_fpm {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A : B.Mat P.k P.r → (Wq →L[ℂ] Wq)} (p₀ : ℕ)
    (hf : B.CkOn ⊤ (B.GV P.k P.r) f) (hA : B.CkOn ⊤ (B.GV P.k P.r) A) :
    B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f A p₀) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := ckOn_comp hf hA g₀ hg₀
  refine ⟨U, fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f' g, hU, hgU, ?_, ?_⟩
  · have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g : B.Mat P.k P.r => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((JCx1.contDiff_Gf p.T.base.z p.T.base.z').pow p₀)
    exact hs.contDiffOn.smul hf'
  · intro g hg hgv
    simp only [TBBx4.fpm]
    congr 1
    exact hfe g hg hgv

end fpmCk

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimTopN (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) →
    Tendsto (fun n : ℕ => TBB.Ew p nn (apx G n) (P.r + 1) [] γ) atTop (𝓝 (TBB.Ew p nn G (P.r + 1) [] γ))

def LimZeroN (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    Tendsto (fun n : ℕ => TBB.Ew p nn (apx G n) 0 w []) atTop (𝓝 (TBB.Ew p nn G 0 w []))

theorem corS_of_apx (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (Λ : ℝ) (K N : ℕ) (C₂ : ℝ) (hC : ∀ n, TBB.CorS p nn (apx G n) Y Λ K N C₂) (hT : LimTopN p nn G)
    (hZ : LimZeroN p nn G Y N) : TBB.CorS p nn G Y Λ K N C₂ := by
  classical
  intro γ hγ
  have h := fun n => hC n γ hγ
  choose w hw hle using h
  set A : Finset C.Letter := Y.image (fun y => ((true, y) : C.Letter)) ∪
    Y.image (fun y => ((false, y + 1) : C.Letter)) with hA
  have hmem : ∀ n, ∀ l ∈ w n, l ∈ A := by
    intro n l hl
    obtain ⟨-, -, L, hL, -, hLl⟩ := hw n
    rw [hL, List.append_nil] at hl
    obtain ⟨y, hy, h | h⟩ := hLl l hl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, hy, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, h.symm⟩)
  have hfin : (Set.range w).Finite := by
    refine ((List.finite_length_le (↥A) N).image (fun l => l.map Subtype.val)).subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨(w n).pmap Subtype.mk (hmem n), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, List.length_pmap]
      exact (hw n).2.1
    · simp [List.map_pmap]
  obtain ⟨w0, hw0⟩ : ∃ w0, ∃ᶠ n in atTop, w n = w0 := by
    by_contra hcon
    push_neg at hcon
    have h2 := (Filter.eventually_all_finite hfin).mpr fun i _ => hcon i
    obtain ⟨n, hn⟩ := h2.exists
    exact hn (w n) ⟨n, rfl⟩ rfl
  have hw0' : TBB.IsExt P p.l0 Y N ((P.r + 1) * K) [] w0 := by
    obtain ⟨n, rfl⟩ := hw0.exists
    exact hw n
  refine ⟨w0, hw0', ?_⟩
  have hadm : TBB.AdmW P p.l0 Y w0 := by
    obtain ⟨hcut, -, L, hL, -, hLl⟩ := hw0'
    refine ⟨hcut, fun l hl => hLl l ?_⟩
    rwa [hL, List.append_nil] at hl
  have hlim := (hZ w0 hadm hw0'.2.1).const_mul ((C₂ * Λ ^ 2) ^ (P.r + 1)) |>.sub (hT γ hγ)
  have hfreq : ∃ᶠ n in atTop, (C₂ * Λ ^ 2) ^ (P.r + 1) * TBB.Ew p nn (apx G n) 0 w0 [] -
      TBB.Ew p nn (apx G n) (P.r + 1) [] γ ∈ Set.Ici (0 : ℝ) :=
    hw0.mono fun n hn => by
      rw [← hn]
      exact sub_nonneg.mpr (hle n)
  exact sub_nonneg.mp (isClosed_Ici.mem_of_frequently_of_tendsto hfreq hlim)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GermContAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) :
    Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, TBB.AdmW P p.l0 Y w →
    w.length + K ≤ N → ContinuousOn (fun z : ℂ => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)])) {0}ᶜ

def GermDataAt (lev : ℕ → Prop) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → lev (b + s - 1) → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N →
    (∀ w', TBB.IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => TBB.Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2

end place

def GermContAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → GermContAt p nn F Y K N

def PropGMean : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (s : ℕ) (β ε' η : ℂ)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS κ₁ κ₂ : ℝ) (E : ℂ → ℝ) (Nk : ℂ → ℂ → ℂ),
    2 ≤ s → 0 ≤ κ₂ → κ₂ ≤ Real.pi * κ₁ → (η = 1 ∨ η = -1) →
    PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS →
    (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) →
    (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
      ‖Nk t t'‖ = κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) →
    (∀ z : ℂ, z ≠ 0 → E z = κ₂ * ‖PBK.bz s bt z‖ ^ 2) →
    Integrable E ∧
      ∀ ω₁ ω₂ : ℂ, (conj ω₁ * ω₂).im ≠ 0 → ∃ A : ℂ → ℂ, PDDual ω₁ ω₂ A ∧
        ∀ σ : ℂ, TBB.InDual ω₁ ω₂ σ →
          (‖(Real.pi⁻¹ : ℂ) * (∫ z : ℂ, P5.fsv σ z * (E z : ℂ)) + A σ‖₊ : ℝ≥0∞) ≤
            limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (𝓝[≠] 0)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem germAtPD_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (K N : ℕ) (hC : GermContAt p nn F Y K N) (hL : GermDataAt (fun i => i ≤ P.r) p nn F Y K N)
    (hT : GermDataAt (fun i => i = P.r + 1) p nn F Y K N) (hM : PropGMean) : GermAtPD p nn F Y K N := by
  intro b s hb hs hbs h hh w hw hN hBdd
  have hcont := hC b s hb hs hbs h hh w hw hN
  have hdata : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2 := by
    rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
    · exact hL b s hb hs hbs (by omega) h hh w hw hN hBdd
    · exact hT b s hb hs hbs (by omega) h hh w hw hN hBdd
  obtain ⟨H, _, _, _, ut, bt, β, ε', η, SS, κ₁, κ₂, hκ₂, hκ, hη, hGD, hpsi, hNk, hE⟩ := hdata
  obtain ⟨hint, hlat⟩ := hM H s β ε' η ut bt SS κ₁ κ₂
    (fun z => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]))
    (fun t t' => TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]))
    hs hκ₂ hκ hη hGD hpsi hNk hE
  exact ⟨hcont, hint, hlat⟩

end place

end

end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConst
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

theorem line_at_most_one_holds : LineAtMost := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ X hX Y hY hX0
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hcap : ∀ Z ∈ Line P Bs Pr π ζ, Gauge.GC.CapEig P Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) π Z := by
    intro Z hZ Yc v
    have hZv : Pr π ν (Z v) = Z v := by
      have := DFunLike.congr_fun hZ.2 v
      simpa only [ContinuousLinearMap.comp_apply] using this
    have hr := ((hPr.2.2 ν hpos).2.2.2 π (Z v)).1 hZv Fr (by rw [hνfix]; exact hFr) (Yc + ((P.k : ℂ) - 2) / 2)
    rw [hpass Z hZ.1, hgl'] at hr
    have e : Yc + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Yc := by ring
    rw [e] at hr
    exact hr
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX.1 (h, h') ⟨hh, hh', he⟩
  have hYF : Y ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hY.1 (h, h') ⟨hh, hh', he⟩
  exact Gauge.GC.lie_weight_at_most_holds Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π X Y hXF hYF
    (hcap X hX) (hcap Y hY) hX0

theorem modConst_of_cut : ModConstOfCut := by
  intro hLN hAM hDT hSR hSN hTF Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  set x0 : ℝ := |P.TT| + 1 with hx0
  have hζ0 : ((x0 : ℝ) : ℂ) ∈ Gauge.GC.Ann P := by
    show P.TT < Complex.normSq ((x0 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  obtain ⟨X0, hX0F, hX0P, hX0ne⟩ := hLN Wp Wq P Bs hpl hk Pr hPr π _ hζ0
  set ζ0 : ℂ := ((x0 : ℝ) : ℂ) with hζ0def
  set T0 := (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)).comp
    (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0) with hT0
  have hB0 : ‖B.hsVec X0‖ ≠ 0 := norm_ne_zero_iff.2 (Gauge.GC.hsVec_ne_zero hX0ne)
  refine ⟨M.Nrm P l π, ‖B.hsVec T0‖ ^ 2 / ‖B.hsVec X0‖ ^ 2, fun ζ hζ Xf hXf hXP => ⟨?_, ?_⟩⟩
  · have hL : Xf ∈ Line P Bs Pr π ζ := ⟨hXf, hXP⟩
    have hR := hSR Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ρ hUp ζ hζ Xf hL
    rw [hR.2]
    exact hSN Wp Wq P Bs hk X d hA l hl S hS Pr hPr π ζ hζ Xf hL
  · have hζT : P.TT < Complex.normSq ζ := hζ
    have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
      rw [hTz, hTz']; exact hζT
    have hζ0T : P.TT < Complex.normSq ζ0 := hζ0
    have hζ0' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ0 := by
      rw [hTz, hTz']; exact hζ0T
    obtain ⟨h, hh, h', hh', hν, hν', hι, hst⟩ :=
      hDT P.k P.r Bs.z Bs.z' Bs.μsec hk hz hz' Bs.T_pos Bs.T'_pos Bs.sec ζ0 ζ hζ0' hζ'
    have hhi := LieBracketMultiplication.uw_inv hh
    have hh'i := LieBracketMultiplication.uw_inv hh'
    have hiso : ∀ Y, ‖B.hsVec ((Bs.π h).comp (Y.comp (Bs.π' h'⁻¹)))‖ = ‖B.hsVec Y‖ :=
      fun Y => CutBP.hsVec_norm_CinL Bs hh hh' Y
    have hinv1 : ∀ w, Bs.π h⁻¹ (Bs.π h w) = w := by
      intro w
      rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hhi _ hh, NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
      rfl

    have hF : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
      refine fun p hp => ?_
      have hp1 : p.1 ∈ UWset P.k P.r Bs.z := hp.1
      have hp2 : p.2 ∈ UWset P.k P.r Bs.z' := hp.2.1
      have hm1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hhi hp1) hh
      have hm2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' := LieBracketMultiplication.uw_mul (LieBracketMultiplication.uw_mul hh'i hp2) hh'
      have key := hX0F _ (hst p hp)
      have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
        rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hm1, ← mul_assoc, ← mul_assoc,
          NFRadRedS.uw_mul_inv hh, one_mul]
      have e2 : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
        rw [← Bs.π'_rep.2 _ hh'i _ hp2, ← Bs.π'_rep.2 _ hm2 _ hh'i, mul_assoc (h'⁻¹ * p.2) h' h'⁻¹,
          NFRadRedS.uw_mul_inv hh', mul_one]
      ext v
      have k1 := DFunLike.congr_fun e1 (X0 (Bs.π' h'⁻¹ (Bs.π' p.2 v)))
      have k2 := DFunLike.congr_fun e2 v
      have k3 := DFunLike.congr_fun key (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 k2 k3 ⊢
      rw [k1, k2, k3]

    have hP : (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹))) =
        (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) := by
      rw [← hν, hPr.2.1 h hh π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0)]
      ext v
      have k1 := DFunLike.congr_fun hX0P (Bs.π' h'⁻¹ v)
      simp only [ContinuousLinearMap.comp_apply] at k1 ⊢
      rw [hinv1, k1]
    have hL0 : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ∈ Line P Bs Pr π ζ := ⟨hF, hP⟩
    have hne : (Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)) ≠ 0 := by
      intro h0
      apply hB0
      have hz0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
        rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), Gauge.GC.hsVec_smul, zero_smul]
      rw [← hiso X0, h0, hz0, norm_zero]
    obtain ⟨c, hc⟩ := hAM Wp Wq P Bs hpl hk Pr hPr π ζ hζ _ hL0 Xf ⟨hXf, hXP⟩ hne

    have hTe := ((hTF Wp Wq P Bs hpl Bw Bw' hBw hBw').2.2.2.1 h hh h' hh'
      (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ0)
      (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0) X0).1
    rw [hν, hν', hι] at hTe
    have hPT : (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
        (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
          ((Bs.π h).comp (X0.comp (Bs.π' h'⁻¹)))) = (Bs.π h).comp (T0.comp (Bs.π' h'⁻¹)) := by
      rw [hTe]
      conv_lhs => rw [← hν]
      rw [hPr.2.1 h hh ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ0), hT0]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hinv1]
    rw [hc, map_smul, ContinuousLinearMap.comp_smul, hPT, Gauge.GC.hsVec_smul, Gauge.GC.hsVec_smul,
      norm_smul, norm_smul, hiso, hiso]
    field_simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

