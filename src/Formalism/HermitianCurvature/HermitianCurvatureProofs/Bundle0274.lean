module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCx2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

private theorem deriv_smul_const_at_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (T : E) :
    deriv (fun t => φ t • T) 0 = deriv φ 0 • T := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ T
  by_cases hT : T = 0
  · simp [hT]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ

  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
  have hℓT : ℓ T ≠ 0 := by
    rw [hℓ]
    exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hT)
  have h2 : DifferentiableAt ℝ (fun t => ℓ (φ t • T) / ℓ T) 0 :=
    ((ℓ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd).div_const _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show φ t = ℓ (φ t • T) / ℓ T
  rw [map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hℓT]

private theorem dLR_smul_const_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : B.Mat k r → ℂ) (T : E)
    (u v : List (B.Mat k r)) : B.dLR u v (fun g => φ g • T) = fun g => B.dLR u v φ g • T := by
  have hR : ∀ v : List (B.Mat k r), B.Rw v (fun g => φ g • T) = fun g => B.Rw v φ g • T := by
    intro v
    induction v with
    | nil => rfl
    | cons X v ih =>
      funext g
      show Formalism.REAL.RdV X (B.Rw v fun g => φ g • T) g = Formalism.REAL.RdV X (B.Rw v φ) g • T
      rw [ih]
      exact deriv_smul_const_at_zero _ T
  unfold B.dLR
  rw [hR v]
  induction u with
  | nil => rfl
  | cons X u ih =>
    funext g
    show B.LdV X (u.foldr B.LdV fun g => B.Rw v φ g • T) g = B.LdV X (u.foldr B.LdV (B.Rw v φ)) g • T
    rw [ih]
    exact deriv_smul_const_at_zero _ T

private theorem ckOn_of_contDiff_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) (UU : Set (B.Mat k r)) : B.CkOn m UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

private theorem pdGood_of_isPolyDeg {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c := by
  obtain ⟨hcd, hwb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r κ c hc
  refine ⟨fun F hF => ?_, fun A m => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => c g • f' g, hU, hgU, hcd.contDiffOn.smul hf', fun g hg hgv => ?_⟩
    simp only [hfe g hg hgv]
  · obtain ⟨C, hC⟩ := hwb m
    refine ⟨2 ^ m * |C|, by positivity, fun F b hF => ?_⟩
    have hab : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ (∅ : Set (B.Mat k r)) →
          ‖B.dLR u v (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) g‖ ≤ C * B.gN g ^ (κ : ℝ) := by
      intro u v hu hv hl g hg _
      have h1 := hC u v hu hv hl g hg
      simp only [List.map_append, List.sum_append] at h1
      simp only [dLR_smul_const_right, norm_smul]
      have h1' : ‖B.dLR u v c g‖ ≤ C * B.gN g ^ (κ : ℝ) := by simpa using h1
      calc ‖B.dLR u v c g‖ * ‖ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ ≤ ‖B.dLR u v c g‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ C * B.gN g ^ (κ : ℝ) := by rw [mul_one]; exact h1'
    obtain ⟨hP1, hP2⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := B.GV k r)
      (a := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) isOpen_empty (fun g hg => Or.inr hg)
      (ckOn_of_contDiff_infty _ (hcd.smul contDiff_const) _ _) hab hF (fun g _ h => by simp at h)
    have hfun : Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) F =
        fun g => c g • F g := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
    rw [hfun] at hP1 hP2
    refine ⟨hP1, fun u v hu hv hl g hg => ?_⟩
    have hb0 : 0 ≤ b := le_trans
      (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))
      (hF.2 [] [] (by simp) (by simp) (by simp) g hg)
    calc _ ≤ 2 ^ m * (|C| * |b|) := hP2 u v hu hv hl g hg
      _ = 2 ^ m * |C| * b := by rw [abs_of_nonneg hb0]; ring

theorem pd_good_pow {d : ℕ} {c : B.Mat k r → ℂ} (hc : pdGood Wp Wq d c) :
    ∀ e : ℕ, pdGood Wp Wq (d * e) (fun g => c g ^ e)
  | 0 => pd_good_congr (fun g _ => by simp) (pd_good_const (Wp := Wp) (Wq := Wq) (d * 0) (1 : ℂ))
  | e + 1 => pd_good_congr (fun g _ => (pow_succ (c g) e).symm)
      (pd_good_mul (by rw [Nat.mul_succ]) (pd_good_pow hc e) hc)

theorem pd_good_of_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c :=
  pdGood_of_isPolyDeg hc

end poly

section decay

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pd_good_Gpow (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) :
    pdGood Wp Wq ((2 * r + 2) * q) (fun g : B.Mat k r => ((Gf k r z z' g ^ q : ℝ) : ℂ)) := by
  have := pd_good_pow (Wp := Wp) (Wq := Wq) (pd_good_of_poly (Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z')) q
  simpa only [Complex.ofReal_pow] using this

theorem inCC_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {A₀ : ℝ} {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) := by
  intro m
  obtain ⟨c, hc⟩ := hf m
  obtain ⟨K, -, hb⟩ := (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).2 (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m
  exact ⟨K * c, hb f c (by rwa [sub_add_cancel])⟩

theorem ckOn_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : B.CkOn ⊤ (B.GV k r) f) : B.CkOn ⊤ (B.GV k r) (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) :=
  (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).1 f hf

end decay

section fpm

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fpm_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) :
    TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ =
      fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g := by
  funext g
  simp only [TBBx4.fpm, ContinuousLinearMap.comp_id]

theorem inCC_fpm_id (p : KB.Pl P Wp Wq) {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (p₀ : ℕ) {A₀ : ℝ}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) m
      (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
  rw [fpm_id]
  exact inCC_Gpow_smul _ _ p₀ hf

end fpm

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def GLFibre : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ j, j + 1 ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ a b : C.LPt, D.IsLocPt a j → D.IsLocPt b j →
      Integrable (fun c : ℂ => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)]) = TBB.NP p nn F j w a b

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def omT (p : KB.Pl P Wp Wq) (N : ℕ) (Q : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(Top.wPt (TBB.TTp p) P.r Q ^ N)

end place

def ptT (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some u => h ++ [(s, u)]

def coT (s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
  | some u => -(G.psi U.betaU ((s : ℂ) * u * x) * ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ))

def epsT (s : ℕ) : ℂ := (-1) ^ (s + 1)

def TopGram1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → (∀ y, 0 < nn y) →
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (L : I → (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef p.T.base (Fi i)) ∧
      ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
        ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'),
          (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ

def TopCore1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), (coT s x j * (omT p N (ptT s h x D j) : ℂ)) •
          p.V F' (ptT s h x D j)‖ ≤ C * ‖x‖⁻¹

def YCont : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
      ContinuousOn (fun c : ℂ => (omT p N (h ++ [(m, c)]) : ℂ) • p.V F' (h ++ [(m, c)])) {0}ᶜ

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPf
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

def LetPt (Y : Finset ℝ) (y : ℝ) : Prop := y ∈ Y ∨ y - 1 ∈ Y

theorem letters_of_admissible_word_are_points {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {w : List C.Letter} (hw : TBB.AdmW P l0 Y w) :
    ∀ l ∈ w, LetPt Y l.2 := by
  intro l hl
  obtain ⟨y, hy, h | h⟩ := hw.2 l hl
  · subst h
    exact Or.inl hy
  · subst h
    right
    simpa using hy

section tools

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem good_finsum {T : (B.Mat k r → E) → B.Mat k r → E} (hT : Qx2.Good k r 0 Set.univ T) {ι : Type*}
    (c : ι → ℂ) (h : ι → B.Mat k r → E) (hs : ∀ i, Q.SmoothLev k r 0 Set.univ (h i)) (s : Finset ι) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ s, c i • h i y) ∧
      ∀ x ∈ Q.Glev k r 0 ∩ Set.univ, T (fun y => ∑ i ∈ s, c i • h i y) x = ∑ i ∈ s, c i • T (h i) x := by
  classical
  letI : NormedAddCommGroup (Q.Mx k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Q.Mx k r) := Matrix.normedSpace
  have hz : Q.SmoothLev k r 0 Set.univ (fun _ : B.Mat k r => (0 : E)) := by
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  have hadd : ∀ (f f₂ : B.Mat k r → E) (a : ℂ), Q.SmoothLev k r 0 Set.univ f → Q.SmoothLev k r 0 Set.univ f₂ →
      Q.SmoothLev k r 0 Set.univ (fun y => f y + a • f₂ y) := by
    intro f f₂ a hf hf₂ g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfe⟩ := hf g₀ hg₀
    obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hfe₂⟩ := hf₂ g₀ hg₀
    refine ⟨U ∩ U₂, fun y => F y + a • F₂ y, hU.inter hU₂, ⟨hgU, hgU₂⟩,
      (hF.mono Set.inter_subset_left).add ((hF₂.mono Set.inter_subset_right).const_smul a), ?_⟩
    intro g hg hgl
    simp only [hfe g hg.1 hgl, hfe₂ g hg.2 hgl]
  have hT0 : ∀ x ∈ Q.Glev k r 0 ∩ Set.univ, T (fun _ => (0 : E)) x = 0 := by
    intro x hx
    have h0 := hT.lin (fun _ => 0) (fun _ => 0) (-1) hz hz x hx
    simp only [smul_zero, add_zero] at h0
    rw [neg_one_smul, add_neg_cancel] at h0
    exact h0
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨hz, hT0⟩
  | @insert i s hi ih =>
    have e : (fun y => ∑ j ∈ insert i s, c j • h j y) = (fun y => (∑ j ∈ s, c j • h j y) + c i • h i y) := by
      funext y
      rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨hadd _ _ _ ih.1 (hs i), fun x hx => ?_⟩
    rw [hT.lin _ _ _ ih.1 (hs i) x hx, ih.2 x hx, Finset.sum_insert hi, add_comm]

theorem norm_prod_map_le {α : Type*} (f : α → ℂ) (g : α → ℝ) :
    ∀ L : List α, (∀ a ∈ L, ‖f a‖ ≤ g a) → ‖(L.map f).prod‖ ≤ (L.map g).prod
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.map_cons, List.prod_cons]
    rw [norm_mul]
    have ha := h a List.mem_cons_self
    have hL := norm_prod_map_le f g L fun b hb => h b (List.mem_cons_of_mem a hb)
    exact mul_le_mul ha hL (norm_nonneg _) ((norm_nonneg _).trans ha)

end tools

section betaT

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_self_real (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∃ t : ℝ, 0 ≤ t ∧ B.beta D F F = t := by
  have hw : ∀ q : (Fin r → ℂ) × ℂ, 0 ≤ bcWeight k r (Tz k r D.z) (Tz k r D.z') q := by
    intro q
    unfold bcWeight
    split_ifs with h
    · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)
    · exact le_refl 0
  refine ⟨∫ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r D.z) (Tz k r D.z') q *
      ‖B.hsVec (B.JF D F (bigCell k r q.1 (D.μsec q.2)))‖ ^ 2,
    MeasureTheory.integral_nonneg (fun q => mul_nonneg (hw q) (sq_nonneg _)), ?_⟩
  unfold B.beta betaBig
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  simp [inner_self_eq_norm_sq_to_K]

theorem beta_zero_left' (D : B.RealPlaceData k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)) : B.beta D 0 G = 0 := by
  have h : ∀ g, B.hsVec (B.JF D 0 g) = 0 := by
    intro g
    have : B.JF D 0 g = 0 := by simp [B.JF, besselJ]
    rw [this]; ext i; simp [B.hsVec]
  simp [B.beta, betaBig, h]

variable [FiniteDimensional ℂ Wp]

theorem beta_sum_left (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type*} (c : ι → ℂ)
    (h : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hh : ∀ i, B.InCC A 5 (h i)) {G : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hG : B.InCC A 5 G) (s : Finset ι) :
    B.beta D (fun g => ∑ i ∈ s, c i • h i g) G = ∑ i ∈ s, c i * B.beta D (h i) G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact beta_zero_left' D G
  | insert a s ha ih =>
    have hS : B.InCC A 5 (fun g => ∑ i ∈ s, c i • h i g) :=
      JCx2.sq_inCC_sum s _ fun i _ => JCx2.sq_inCC_smul (c i) (hh i)
    have e : (fun g => ∑ i ∈ insert a s, c i • h i g) =
        (fun g => ∑ i ∈ s, c i • h i g) + c a • h a := by
      funext g
      simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply]
      rw [add_comm]
    rw [e, (JCx2.sq_beta_sesq D hA hS (hh a) hG (c a)).1, ih, Finset.sum_insert ha, add_comm]

theorem beta_sum_right (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type*}
    (h : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hh : ∀ i, B.InCC A 5 (h i)) {G : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hG : B.InCC A 5 G) (s : Finset ι) :
    B.beta D G (fun g => ∑ i ∈ s, h i g) = ∑ i ∈ s, B.beta D G (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Dx1.LZ.beta_zero_right D G
  | insert a s ha ih =>
    have hS : B.InCC A 5 (fun g => ∑ i ∈ s, h i g) := JCx2.sq_inCC_sum s _ fun i _ => hh i
    have e : (fun g => ∑ i ∈ insert a s, h i g) = (fun g => ∑ i ∈ s, h i g) + (1 : ℂ) • h a := by
      funext g
      simp only [Finset.sum_insert ha, Pi.add_apply, one_smul]
      rw [add_comm]
    rw [e, (JCx2.sq_beta_sesq D hA hS (hh a) hG 1).2, ih, Finset.sum_insert ha, map_one, one_mul, add_comm]

end betaT

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigStr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) : Prop :=
  ∃ (A : ℝ) (n : ℕ) (h : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ev : Fin n → ℝ → ℂ),
    B.AB P.k P.r ≤ A ∧ (∀ i, B.CkOn ⊤ (B.GV P.k P.r) (h i)) ∧ (∀ i, B.InCC A 5 (h i)) ∧
    (∀ g ∈ B.GV P.k P.r, F g = ∑ i, h i g) ∧
    (∀ i y, LetPt Y y → ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) (h i) g = ev i y • h i g) ∧
    (∀ i y, LetPt Y y → ‖ev i y‖ ≤ nn y) ∧
    (∀ i j, i ≠ j → B.beta p.T.base (h i) (h j) = 0)

theorem fold_eig {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (s : ℂ) (Y : Finset ℝ)
    (h : Fin n → B.Mat k r → E) (ev : Fin n → ℝ → ℂ) (hs : ∀ i, B.CkOn ⊤ (B.GV k r) (h i))
    (he : ∀ i y, LetPt Y y → ∀ g ∈ B.GV k r, Q.CV k r (y : ℂ) (h i) g = ev i y • h i g)
    {F : B.Mat k r → E} (hF : ∀ g ∈ B.GV k r, F g = ∑ i, h i g) :
    ∀ L : List C.Letter, (∀ l ∈ L, LetPt Y l.2) → ∀ g ∈ B.GV k r,
      L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F g = ∑ i, (L.map fun a => s * ev i a.2).prod • h i g
  | [], _, g, hg => by simpa using hF g hg
  | a :: L, hL, g, hg => by
    have ih := fold_eig s Y h ev hs he (F := F) hF L (fun l hl => hL l (List.mem_cons_of_mem a hl))
    have hsm : ∀ i, Q.SmoothLev k r 0 Set.univ (h i) := fun i => Dx1.LZ.smooth_of_ck (hs i)
    have hlin := (good_finsum (Dx1.LZ.good_CV (k := k) (r := r) (E := E) (a.2 : ℂ))
      (fun i => (L.map fun a => s * ev i a.2).prod) h hsm Finset.univ).2 g (Dx1.LZ.glev0 hg)
    have hloc := (Dx1.LZ.good_CV (k := k) (r := r) (E := E) (a.2 : ℂ)).loc
      (L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F)
      (fun y => ∑ i, (L.map fun a => s * ev i a.2).prod • h i y) (fun y hy => ih y hy.1.1) g (Dx1.LZ.glev0 hg)
    have ha := hL a List.mem_cons_self
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [hloc, hlin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i a.2 ha g hg, smul_smul, smul_smul]
    ring_nf

theorem limBd_of_eigStr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) (hE : EigStr p nn F Y) : LimBd p nn F Y N := by
  classical
  obtain ⟨A, n, h, ev, hA, hs, hcc, hF, he, hev, horth⟩ := hE
  intro w hw _
  set s : ℂ := M.sgn P p.l0 with hsdef
  have hs1 : ‖s‖ = 1 := by simp [hsdef, M.sgn]
  set c : Fin n → ℂ := fun i => (w.map fun a => s * ev i a.2).prod with hc
  have hFck : B.CkOn ⊤ (B.GV P.k P.r) F :=
    Qb1.ckOn_congr (fun g hg => (hF g hg).symm) (JCx2.sq_ckOn_sum Finset.univ h fun i _ => hs i)
  have hLet := letters_of_admissible_word_are_points hw

  have hRR : p.RR F 0 w [] [] = B.beta p.T.base (fun g => ∑ i, c i • h i g) (fun g => ∑ j, h j g) := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hFck (good_positioned_of_cut hw.1)]
    unfold C7.principalHermitianLattice
    rw [JCx2.sq_beta_congr _ (fold_eig s Y h ev hs he hF w hLet)]
    exact beta_congr_right _ hF
  have hBF : B.beta p.T.base F F = B.beta p.T.base (fun g => ∑ i, (1 : ℂ) • h i g) (fun g => ∑ j, h j g) := by
    rw [JCx2.sq_beta_congr _ (F₂ := fun g => ∑ i, (1 : ℂ) • h i g) (fun g hg => by simp [hF g hg]),
      beta_congr_right _ hF]
  have hSum : B.InCC A 5 (fun g => ∑ j, h j g) := JCx2.sq_inCC_sum _ _ fun i _ => hcc i
  have hexp : ∀ d : Fin n → ℂ, B.beta p.T.base (fun g => ∑ i, d i • h i g) (fun g => ∑ j, h j g) =
      ∑ i, d i * B.beta p.T.base (h i) (h i) := by
    intro d
    rw [beta_sum_left p.T.base hA d h hcc hSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [beta_sum_right p.T.base hA h hcc (hcc i), Finset.sum_eq_single i]
    · intro j _ hji
      exact horth i j (Ne.symm hji)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hRR, hBF, hexp, hexp]
  have hcn : ∀ i, ‖c i‖ ≤ TBB.normC nn w := by
    intro i
    unfold TBB.normC
    refine norm_prod_map_le (fun a => s * ev i a.2) (fun l => nn l.2) w fun a ha => ?_
    rw [norm_mul, hs1, one_mul]
    exact hev i a.2 (hLet a ha)
  simp only [one_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨t, ht, hbt⟩ := beta_self_real p.T.base (h i)
  rw [hbt, Complex.re_mul_ofReal, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans (hcn i)) ht

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

