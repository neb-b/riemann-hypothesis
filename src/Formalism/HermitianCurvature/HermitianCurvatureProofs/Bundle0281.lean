module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0280
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0274
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0279
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0270
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSQQAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0271

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqDecay
section
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CutBP2
open scoped ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem op_clm (Φ : E →L[ℂ] E') (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → E}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) {g : Mat k r} (hg : g ∈ GV k r) :
    Formalism.FourierDecayAlt.P.B4.op b X (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.op b X G g) := by
  unfold Formalism.FourierDecayAlt.P.B4.op
  have hd : DifferentiableAt ℝ (fun t : ℝ => G (Formalism.FourierDecayAlt.P.B4.cv b X t g)) 0 :=
    Formalism.FourierDecayAlt.P.B4.ckOn_diff 0 b hG hX hg
  exact ((Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt).deriv

theorem ckOn_clm {m : ℕ∞} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CkOn m (GV k r) G) :
    CkOn m (GV k r) (fun h => Φ (G h)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', heq⟩ := hG g₀ hg₀
  refine ⟨U, fun h => Φ (f' h), hU, hg, ?_, fun g hgU hgV => by show Φ (G g) = Φ (f' g); rw [heq g hgU hgV]⟩
  exact (Φ.restrictScalars ℝ).contDiff.comp_contDiffOn hf'

theorem W_clm (Φ : E →L[ℂ] E') (w : List (Bool × Mat k r)) (hw : Formalism.FourierDecayAlt.P.B4.AllLie w) {G : Mat k r → E}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) :
    ∀ g ∈ GV k r, Formalism.FourierDecayAlt.P.B4.W w (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.W w G g) := by
  induction w generalizing G with
  | nil =>
    intro g _
    rfl
  | cons x w ih =>
    intro g hg
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hw' : Formalism.FourierDecayAlt.P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hGw : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G := Formalism.FourierDecayAlt.P.B4.ckOn_mono (by simp) hG
    have hG1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Formalism.FourierDecayAlt.P.B4.W w G) :=
      Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives w hw' 1 (by simpa [Nat.add_comm] using hG)
    rw [Formalism.FourierDecayAlt.P.B4.W_cons, Formalism.FourierDecayAlt.P.B4.W_cons,
      Formalism.FourierDecayAlt.P.B4.op_congr x.1 hx (fun h hh => ih hw' hGw h hh) g hg]
    exact op_clm Φ x.1 hx hG1 hg

theorem ccle_clm {A c : ℝ} {m : ℕ} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CCle A m G c) :
    CCle A m (fun h => Φ (G h)) (‖Φ‖ * c) := by
  obtain ⟨hk, hb⟩ := hG
  refine ⟨ckOn_clm Φ hk, fun u v hu hv hl g hg => ?_⟩
  have hw : Formalism.FourierDecayAlt.P.B4.AllLie (Formalism.FourierDecayAlt.P.B4.lr u v) :=
    Formalism.FourierDecayAlt.P.SliceLastLevel.allLie_lr' (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1)
  have hlen : (Formalism.FourierDecayAlt.P.B4.lr u v).length = u.length + v.length := by simp [Formalism.FourierDecayAlt.P.B4.lr]
  have hGk : CkOn (((Formalism.FourierDecayAlt.P.B4.lr u v).length : ℕ) : ℕ∞) (GV k r) G :=
    Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) hk
  rw [Formalism.FourierDecayAlt.P.B4.dLR_eq, W_clm Φ _ hw hGk g hg, ← Formalism.FourierDecayAlt.P.B4.dLR_eq]
  have h1 := hb u v hu hv hl g hg
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg).le _
  calc gN g ^ A * ‖Φ (dLR u v G g)‖ ≤ gN g ^ A * (‖Φ‖ * ‖dLR u v G g‖) :=
        mul_le_mul_of_nonneg_left (Φ.le_opNorm _) hgN
    _ = ‖Φ‖ * (gN g ^ A * ‖dLR u v G g‖) := by ring
    _ ≤ ‖Φ‖ * c := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

end clm

section sum

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rw_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [rw_zero_fnE v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dLR_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (B.Mat k r)) :
    ∀ u : List (B.Mat k r), B.dLR u v (0 : B.Mat k r → E) = 0
  | [] => rw_zero_fnE v
  | X :: u => by
    show B.LdV X (B.dLR u v 0) = 0
    rw [dLR_zero_fnE v u]
    funext g
    simp [B.LdV]

theorem inCC_zero_fnE (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → (Wq →L[ℂ] Wp)) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => rfl⟩,
    fun u v _ _ _ g _ => ?_⟩
  rw [dLR_zero_fnE v u]
  simp

theorem inCC_finsum {A : ℝ} {m : ℕ} : ∀ {n : ℕ} (F : Fin n → Mat k r → (Wq →L[ℂ] Wp)),
    (∀ i, InCC A m (F i)) → InCC A m (fun g => ∑ i, F i g) := by
  intro n
  induction n with
  | zero =>
    intro F _
    have e : (fun g => ∑ i : Fin 0, F i g) = (0 : Mat k r → (Wq →L[ℂ] Wp)) := by
      funext g
      exact Fin.sum_univ_zero _
    rw [e]
    exact inCC_zero_fnE A m
  | succ n ih =>
    intro F h
    simp only [Fin.sum_univ_succ]
    obtain ⟨c₁, h₁⟩ := h 0
    obtain ⟨c₂, h₂⟩ := ih (fun i : Fin n => F i.succ) (fun i => h i.succ)
    exact ⟨c₁ + c₂, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h₁ h₂⟩

end sum

theorem shifted_decay : FpmShDecay := by
  intro P Wp Wq Wq' _ _ _ _ _ _ _ _ _ u u' q f A A₀ d p₀ hf hA m
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  set Gp : B.Mat P.k P.r → ℂ := fun g => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ) with hGp
  have e : fpmSh q f A p₀ = fun g => ∑ i, (Gp g * c i g) • (f g).comp (L i) := by
    funext g
    ext v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [fpmSh, hAe g, map_sum, map_smul, Finset.smul_sum, smul_smul, hGp]
  rw [e]
  refine inCC_finsum _ fun i => ?_
  set Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (L i)
  have hΦ : ∀ x, Φ x = x.comp (L i) := fun x => rfl
  have hgood : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq' ((2 * P.r + 2) * p₀ + d) (fun g => Gp g * c i g) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_mul le_rfl (Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow q.T.base.z q.T.base.z' p₀)
      (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (hc i))
  obtain ⟨K, -, hK⟩ := hgood.2 (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m
  obtain ⟨b, hb⟩ := hf m
  have hb' := ccle_clm Φ hb
  have hA' : A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) = A₀ := by
    push_cast; ring
  rw [← hA'] at hb'
  exact ⟨K * (‖Φ‖ * b), hK _ _ hb'⟩

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem normC_one (w : List C.Letter) : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by
  unfold TBB.normC
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


end place

theorem nfHyp_mono {Cb c c' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ χ' : ℝ → ℝ} {N : ℕ}
    (h : NFHyp Cb c p f A₀ p₀ χ N) (hc : c' ≤ c) (hχ' : C6.IsCut0 χ') : NFHyp Cb c' p f A₀ p₀ χ' N := by
  obtain ⟨-, a2, a3, a4, a5, a6⟩ := h
  refine ⟨hχ', a2, a3, a4, le_trans ?_ a5, a6⟩
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
      x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
    fun x => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hc hX


end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFOpOK (C : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq) : Prop :=
  B.SmoothCoef (B.GPos p.T.base) Th ∧ B.Commutes p.T.base (B.GPos p.T.base) Th ∧
    CutMP.GlobCoef Th (C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) ∧
    (B.opOrder Th : ℝ) ≤ C * CutMP.nDim P.k P.r * ((N : ℝ) + 1)

def NFDomZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ),
    ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → topD p H w c = 0

def NFDomMeas : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      AEStronglyMeasurable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w)
        volume

theorem domination_at_zero_holds : NFDomZero := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hc
  unfold topD TBB.Ew TBB.NP KB.Pl.RR
  generalize TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = a
  generalize TBB.normC (fun x => 1) w = b
  generalize TBB.bigPt P.r c = x at hc ⊢
  unfold D.RRplace
  by_cases hl : D.IsLocPt x (P.r + 1)
  · have hG : ¬ 0 < TBB.Gp p x := fun h => hc ⟨hl, h⟩
    rw [dite_eq_left ⟨hl, hl⟩, dite_eq_right (by omega)]
    have hv : ∀ H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV p.T.base p.ν' p.m₀ H' x = 0 := by
      intro H'
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      apply hG
      unfold TBB.Gp
      exact h
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    have hi0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
      simp [B.hsInner, h0]
    simp [hv]
    split_ifs with hw
    · simp [hi0]
    · unfold Top.topOf
      simp [hv, hi0]
  · simp [hl]

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_congr_gt (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (δ : ℝ)
    (h : ∀ g ∈ B.GV k r, δ < Gf k r Bs.z Bs.z' g → H₁ g = H₂ g)
    (hq : ¬ (0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q) ∨ δ < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q) :
    D.vecV Bs ν' m₀ H₁ q = D.vecV Bs ν' m₀ H₂ q := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    have hδ : δ < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q := hq.resolve_left (not_not.2 hq'.2)
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have hpos : δ < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ hδ
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) H₁ H₂ 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [h _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos)])
      rw [e, one_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

section lift

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem theta_cutF_gt (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ} (hε : 0 < ε)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (e : Wd.Ix (Fin w.length)) :
    ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g →
      p.Θ.Θ w e (D.cutF p.T.base χ F ε) g = p.Θ.Θ w e F g := by
  intro g hg hgε
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hΘ⟩ := hCb w hw e
  have hdom : g ∈ C6.domL p.T.base ∅ := ⟨hg, lt_trans hε hgε, fun l hl => by simp at hl⟩
  rw [hΘ _ g hdom, hΘ _ g hdom]
  have hlen : ∀ T ∈ Dop, T.word.length ≤ o := by
    intro T hT
    obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hIn.2.2 T hT
    omega
  have hc : B.CkOn ⊤ (B.GV P.k P.r) (D.cutF p.T.base χ F ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε
  have hsub := Formalism.FourierDecayAlt.P.PBE.opApply_subGV Dop hlen (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hc)
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) g hg
  have hGc : Continuous (fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hU : IsOpen {x : B.Mat P.k P.r | ε < Gf P.k P.r p.T.base.z p.T.base.z' x} := isOpen_lt continuous_const hGc
  have h0 := Formalism.FourierDecayAlt.P.PBE.opApply_zero_near Dop (F := D.cutF p.T.base χ F ε - F) hU (by
    intro x _ hx
    replace hx : ε < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' x / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [Pi.sub_apply, D.cutF, hχ.2.2 _ h1, Complex.ofReal_one, one_smul, sub_self]) g hg hgε
  rw [hsub] at h0
  exact sub_eq_zero.1 h0

end lift

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rrTop_cutF_eq (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {ε : ℝ} (hε : 0 < ε)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (γ : C.LPt)
    (hγ : ¬ (0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ) ∨
      ε < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ) :
    p.RR (D.cutF p.T.base χ F ε) (P.r + 1) w γ γ = p.RR F (P.r + 1) w γ γ := by
  have hV : ∀ H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → H₁ g = H₂ g) →
      D.vecV p.T.base p.ν' p.m₀ H₁ γ = D.vecV p.T.base p.ν' p.m₀ H₂ γ :=
    fun H₁ H₂ h => vecV_congr_gt p.T.base p.ν' p.m₀ γ ε h hγ
  have hcut : ∀ g ∈ B.GV P.k P.r, ε < Gf P.k P.r p.T.base.z p.T.base.z' g → D.cutF p.T.base χ F ε g = F g := by
    intro g _ hg
    have h1 : 1 ≤ Gf P.k P.r p.T.base.z p.T.base.z' g / ε := by rw [le_div_iff₀ hε]; linarith
    simp only [D.cutF, hχ.2.2 _ h1, Complex.ofReal_one, one_smul]
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt γ (P.r + 1) ∧ D.IsLocPt γ (P.r + 1)
  · rw [dif_pos h1, dif_pos h1, dif_neg (by omega), dif_neg (by omega), if_pos rfl, if_pos rfl]
    by_cases h3 : w = []
    · rw [if_pos h3, if_pos h3, hV _ _ hcut]
    · rw [if_neg h3, if_neg h3]
      unfold Top.topOf
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hV _ _ (theta_cutF_gt p hCb hχ hF hε hw e)]
  · rw [dif_neg h1, dif_neg h1]

theorem nFTopPtw_of (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {χ : ℝ → ℝ}
    (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) :
    ∀ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), topD p (D.cutF p.T.base χ F ε) w c = topD p F w c := by
  intro c
  set γ := TBB.bigPt P.r c
  set Gγ := D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ with hGγ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (¬ (0 < Gγ) ∨ ε < Gγ) := by
    by_cases hG : 0 < Gγ
    · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
      exact ⟨hε.1, Or.inr hε.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ⟨hε, Or.inl hG⟩
  filter_upwards [hev] with ε hε
  unfold topD TBB.Ew TBB.NP
  rw [rrTop_cutF_eq p hCb hχ hF hε.1 hw γ hε.2]

end place

theorem top_pointwise_all_levels_holds : NFTopPtwAll := by
  intro Cb
  refine ⟨0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw _
  obtain ⟨hχ, hCb, hf, -, -, -⟩ := hH
  have hF : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) :=
    ckOn_fpm p p₀ hf (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_const' _)
  exact Filter.Eventually.of_forall fun c => nFTopPtw_of p hCb hχ hF hw.1 c

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopR
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_R (hR : RDSOpR) (hRv : RDSOpRv) : RDIdentSpec :=
  rDIdentSpec_of_open spectral_operator_A_adjoint hR hRv spectral_operator_A spectral_pairing_adjoint spectral_quadratic_adjoint spectral_xi_test spectral_pairing_identity

theorem thmPActualCpt_of_R (hR : RDSOpR) (hRv : RDSOpRv) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_spec (rDIdentSpec_of_R hR hRv)

end Formalism.FourierDecayAlt.P.CutSE
end

