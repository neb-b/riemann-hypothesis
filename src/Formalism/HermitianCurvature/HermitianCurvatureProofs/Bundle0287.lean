module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0283
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibExp
section
namespace Formalism.FourierDecayAlt.P.CutBP.LeibExp

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Gc (z z' : Fin (2 * r + k + 1) → ℂ) : B.Mat k r → ℂ := fun g => ((Gf k r z z' g : ℝ) : ℂ)

theorem gc_poly (z z' : Fin (2 * r + k + 1) → ℂ) : ListSumSplittings.PolyClass (2 * r + 2) (Gc (k := k) (r := r) z z') := by
  apply ListSumSplittings.polyClass_of_isPolyDeg
  obtain ⟨q, hq, h⟩ := Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z'
  exact ⟨q, hq, h⟩

abbrev Tm (k r : ℕ) := ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)

def coefT (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (t : Tm k r) (y : B.Mat k r) : ℂ :=
  ((Ψ t.1 (Gf k r z z' y) : ℝ) : ℂ) * t.2.1 y * ((Gf k r z z' y : ℝ) : ℂ)⁻¹ ^ t.2.2.1

def step (z z' : Fin (2 * r + k + 1) → ℂ) (X : B.Mat k r) (t : Tm k r) : List (Tm k r) :=
  [(t.1 + 1, fun y => Formalism.REAL.RdV X (Gc z z') y * t.2.1 y, t.2.2.1 + 1, t.2.2.2),
   (t.1, Formalism.REAL.RdV X t.2.1, t.2.2.1, t.2.2.2),
   (t.1, fun y => (-(t.2.2.1 : ℂ)) * (Formalism.REAL.RdV X (Gc z z') y * t.2.1 y), t.2.2.1 + 1, t.2.2.2),
   (t.1, t.2.1, t.2.2.1, X :: t.2.2.2)]

theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem term_deriv (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (hΨ : ThChain Ψ) (t : Tm k r)
    (hP : ListSumSplittings.PolyClass 0 t.2.1 ∨ B.CkOn ⊤ (B.GV k r) t.2.1)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) (hv : ∀ Y ∈ t.2.2.2, B.inLie k r Y)
    {X x : B.Mat k r} (hX : B.inLie k r X) (hxG : x ∈ B.GV k r) (hxp : 0 < Gf k r z z' x) :
    HasDerivAt (fun s : ℝ => coefT z z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
        B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
      (((step z z' X t).map fun t' => coefT z z' Ψ t' x • B.Rw t'.2.2.2 F x).sum) 0 := by
  obtain ⟨q, P, j, v⟩ := t
  simp only at hP hv ⊢
  have hPC : B.CkOn ⊤ (B.GV k r) P := by rcases hP with h | h; exact h.1; exact h
  set c : ℝ → B.Mat k r := fun s => x * NormedSpace.exp ((s : ℂ) • X) with hcdef
  have hc0 : c 0 = x := B5.curve_zero x X
  have hGc : HasDerivAt (fun s => Gc z z' (c s)) (Formalism.REAL.RdV X (Gc z z') x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (gc_poly z z').1) hxG hxG hX
  have hdiff : DifferentiableAt ℝ (fun s => Gf k r z z' (c s)) 0 := by
    have h1 : Differentiable ℝ (fun g : B.Mat k r => Gf k r z z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').differentiable (by simp)
    have h2 : Differentiable ℝ c := (B5.curve_contDiff x X).differentiable (by simp)
    exact (h1 (c 0)).comp (0 : ℝ) (h2 0)
  set dG : ℝ := deriv (fun s => Gf k r z z' (c s)) 0 with hdG
  have hGr : HasDerivAt (fun s => Gf k r z z' (c s)) dG 0 := hdiff.hasDerivAt
  have hD : Formalism.REAL.RdV X (Gc z z') x = (dG : ℂ) := by
    have h2 := hGr.ofReal_comp
    exact hGc.unique (by simpa [Gc] using h2)
  have hGx : Gf k r z z' (c 0) = Gf k r z z' x := by rw [hc0]
  have hne : Gf k r z z' (c 0) ≠ 0 := by rw [hGx]; exact hxp.ne'
  have hΨq : HasDerivAt (Ψ q) (Ψ (q + 1) (Gf k r z z' x) / Gf k r z z' x) (Gf k r z z' (c 0)) := by
    rw [hGx]; exact hΨ q _ hxp
  have hψ := (hΨq.comp (0 : ℝ) hGr).ofReal_comp
  have hPd : HasDerivAt (fun s => P (c s)) (Formalism.REAL.RdV X P x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top hPC) hxG hxG hX
  have hI := ((hGr.inv hne).pow j).ofReal_comp
  have hR : HasDerivAt (fun s => B.Rw v F (c s)) (Formalism.REAL.RdV X (B.Rw v F) x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (JFxI.ckOn_Rw_top' hF v hv)) hxG hxG hX
  have hA := ((hψ.mul hPd).mul hI).smul hR
  refine (hA.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [coefT, Function.comp_apply, Pi.pow_apply, Pi.inv_apply, Complex.ofReal_pow, Complex.ofReal_inv]
    rfl
  simp only [step, coefT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc0,
    Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, hD]
  have hRw : B.Rw (X :: v) F x = Formalism.REAL.RdV X (B.Rw v F) x := rfl
  rw [hRw]
  rcases j with _ | j
  · push_cast
    module
  · simp only [Nat.add_sub_cancel]
    push_cast
    module

theorem exp_main (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) :
    ∃ terms : List (Tm k r),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => coefT Bs.z Bs.z' Ψ t x • B.Rw t.2.2.2 F x).sum := by
  induction w with
  | nil =>
    refine ⟨[(0, fun _ => 1, 0, [])], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨le_rfl, ?_, List.Sublist.refl _⟩
      rw [List.length_nil, mul_zero]
      exact ListSumSplittings.polyClass_const 1
    · intro Ψ _ F _ x _
      simp [coefT, B.Rw]
  | cons X w ih =>
    have hwL : ∀ Y ∈ w, B.inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hXL : B.inLie k r X := hw X List.mem_cons_self
    obtain ⟨terms, hprop, hid⟩ := ih hwL
    refine ⟨terms.flatMap (step Bs.z Bs.z' X), ?_, ?_⟩
    · intro t' ht'
      rw [List.mem_flatMap] at ht'
      obtain ⟨t, ht, ht'⟩ := ht'
      obtain ⟨h1, h2, h3⟩ := hprop t ht
      have hGp := gc_poly (k := k) (r := r) Bs.z Bs.z'
      have hdeg : (2 * r + 2) * w.length ≤ (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      have hdeg2 : (2 * r + 2) + (2 * r + 2) * w.length = (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; ring
      simp only [step, List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2
      · exact ⟨by simp only [List.length_cons]; omega,
          ListSumSplittings.polyClass_mono hdeg (ListSumSplittings.polyClass_op h2 false hXL), h3.cons X⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_cmul _ (ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2)
      · exact ⟨by simp only [List.length_cons]; omega, ListSumSplittings.polyClass_mono hdeg h2, h3.cons_cons X⟩
    · intro Ψ hΨ F hF x hx
      have hVo : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
        isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
      have hloc := PositiveOrbitOpen.rdV_local (f₁ := B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y))
        (f₂ := fun y => (terms.map fun t => coefT Bs.z Bs.z' Ψ t y • B.Rw t.2.2.2 F y).sum) hVo
        (fun y hy hyG => hid Ψ hΨ F hF y ⟨hyG, hy, fun l hl => absurd hl (Finset.notMem_empty l)⟩) hXL x hx.2.1 hx.1
      change Formalism.REAL.RdV X (B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y)) x = _
      rw [hloc]
      have hd := JFxI.hasDerivAt_list_sum terms
        (fun t s => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
        (fun t => ((step Bs.z Bs.z' X t).map fun t' => coefT Bs.z Bs.z' Ψ t' x • B.Rw t'.2.2.2 F x).sum)
        (t := 0) (fun t ht => term_deriv Bs.z Bs.z' Ψ hΨ t (Or.inr (hprop t ht).2.1.1) F hF
          (fun Y hY => hwL Y ((hprop t ht).2.2.subset hY)) hXL hx.1 hx.2.1)
      change deriv (fun s : ℝ => (terms.map fun t => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X))).sum) 0 = _
      rw [hd.deriv, sum_flatMap]

end

end Formalism.FourierDecayAlt.P.CutBP.LeibExp

namespace Formalism.FourierDecayAlt.P.CutBP

theorem leibniz_expansion_holds : NFLeibExp := by
  unfold NFLeibExp
  intro k r Wp Wq _ _ _ _ Bs w hw
  exact LeibExp.exp_main Bs w hw

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibOps
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibOps_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem nfLeibOps_hsInner_smul_left (c : ℂ) (A B' : Wq →L[ℂ] Wp) : B.hsInner (c • A) B' = c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_right]

theorem nfLeibOps_hsInner_smul_right (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    B.hsInner A (c • B') = conj c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_left]

def nfLeibOps_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (g : B.Mat k r) : ℂ :=
  t.2.1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1


open Classical in
def nfLeibOps_mk (Bs : B.RealPlaceData k r Wp Wq) (T : B.DTerm k r Wp Wq)
    (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef g := nfLeibOps_sc Bs t g • T.coef g
  coefAdj g := conj (nfLeibOps_sc Bs t g) • T.coefAdj g
  word := if ∀ X ∈ t.2.2.2, B.inLie k r X then t.2.2.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id x A B' := by
    simp only [ContinuousLinearMap.smul_apply]
    rw [nfLeibOps_hsInner_smul_left, nfLeibOps_hsInner_smul_right, T.adj_id, Complex.conj_conj]

theorem nfLeibOps_ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (B.Mat k r)}
    {c : B.Mat k r → ℂ} {f : B.Mat k r → E} (hc : B.CkOn ⊤ UU c) (hf : B.CkOn ⊤ UU f) :
    B.CkOn ⊤ UU (fun g => c g • f g) := by
  unfold B.CkOn at hc hf ⊢
  intro g₀ hg₀
  obtain ⟨U₁, c', hU₁, hg₁, hc', ec⟩ := hc g₀ hg₀
  obtain ⟨U₂, f', hU₂, hg₂, hf', ef⟩ := hf g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => c' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show c g • f g = c' g • f' g
  rw [ec g hg.1 hgG, ef g hg.2 hgG]

theorem nfLeibOps_ckOn_conj {UU : Set (B.Mat k r)} {c : B.Mat k r → ℂ} (hc : B.CkOn ⊤ UU c) :
    B.CkOn ⊤ UU (fun g => conj (c g)) := by
  unfold B.CkOn at hc ⊢
  intro g₀ hg₀
  obtain ⟨U, c', hU, hg, hc', ec⟩ := hc g₀ hg₀
  refine ⟨U, fun g => conj (c' g), hU, hg, ?_, ?_⟩
  · refine (Complex.conjCLE.contDiff.comp_contDiffOn hc').congr (fun g _ => ?_)
    simp
  · intro g hgU hgG
    show conj (c g) = conj (c' g)
    rw [ec g hgU hgG]

theorem nfLeibOps_ckOn_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (D : ℕ)
    (hP : ListSumSplittings.PolyClass D t.2.1) : B.CkOn ⊤ (C6.domL Bs ∅) (nfLeibOps_sc Bs t) := by
  intro g₀ hg₀
  obtain ⟨U1, c1, hU1, hg1, hc1, he1⟩ := hP.1 g₀ hg₀.1
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z')
  have hO : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  refine ⟨U1 ∩ {g | 0 < Gf k r Bs.z Bs.z' g},
    fun g => c1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1, hU1.inter hO, ⟨hg1, hg₀.2.1⟩, ?_, ?_⟩
  · refine (hc1.mono Set.inter_subset_left).mul ?_
    refine ContDiffOn.pow ?_ _
    refine (hGc.contDiffOn.inv fun g hg => ?_).mono Set.inter_subset_right
    · exact_mod_cast (ne_of_gt hg)
  · intro g hg hgG
    simp only [nfLeibOps_sc, he1 g hg.1 hgG]

end ops

theorem nfLeibOps_sum_key {E : Type*} [AddCommGroup E] [Module ℂ E] {α : Type*} (Q : ℕ) (key : α → ℕ)
    (f : ℕ → ℂ) (a : α → E) : ∀ l : List α, (∀ t ∈ l, key t ≤ Q) →
    (l.map fun t => f (key t) • a t).sum =
      ∑ q : Fin (Q + 1), f q • ((l.filter fun t => key t = (q : ℕ)).map a).sum := by
  intro l hl
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun t' ht' => hl t' (by simp [ht']))]
    have hq : key t < Q + 1 := Nat.lt_succ_of_le (hl t (by simp))
    have hsplit : ∀ q : Fin (Q + 1), f q • (((t :: l).filter fun t' => key t' = (q : ℕ)).map a).sum =
        (if key t = (q : ℕ) then f q • a t else 0) +
          f q • ((l.filter fun t' => key t' = (q : ℕ)).map a).sum := by
      intro q
      by_cases h : key t = (q : ℕ)
      · simp [List.filter_cons, h, smul_add]
      · simp [List.filter_cons, h]
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨key t, hq⟩]
    · simp
    · intro b _ hb
      have hne : key t ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [hne]
    · simp

theorem nfLeibOps_of (hE : NFLeibExp) : NFLeibOps := by
  intro k r Wp Wq _ _ _ _ _ Bs Dop hsm
  classical
  let terms : B.DTerm k r Wp Wq → List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) :=
    fun T => (hE k r Wp Wq Bs T.word T.word_lie).choose
  have hspec := fun T : B.DTerm k r Wp Wq => (hE k r Wp Wq Bs T.word T.word_lie).choose_spec
  set Q : ℕ := (Dop.map fun T => T.word.length).sum with hQ
  have hQle : ∀ T ∈ Dop, T.word.length ≤ Q := fun T hT =>
    List.le_sum_of_mem (List.mem_map.2 ⟨T, hT, rfl⟩)
  let LT : B.DTerm k r Wp Wq → Fin (Q + 1) → B.DiffOp k r Wp Wq :=
    fun T q => ((terms T).filter fun t => t.1 = (q : ℕ)).map (nfLeibOps_mk Bs T)
  refine ⟨Q, fun q => Dop.flatMap fun T => LT T q, ?_, ?_, ?_⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    have hP := ((hspec T).1 t htm).2.1
    exact ⟨nfLeibOps_ckOn_smul (nfLeibOps_ckOn_sc Bs t _ hP) (hsm T hT).1,
      nfLeibOps_ckOn_smul (nfLeibOps_ckOn_conj (nfLeibOps_ckOn_sc Bs t _ hP)) (hsm T hT).2⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    obtain ⟨-, hP, hsub⟩ := (hspec T).1 t htm
    refine ⟨T, hT, t.2.1, t.2.2.1, hP, ?_, fun g _ => rfl⟩
    have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (hsub.subset hX)
    simp only [nfLeibOps_mk]
    rw [if_pos hlie]
    exact hsub
  ·
    intro Ψ hΨ F hF x hx
    have hT1 : ∀ T ∈ Dop, T.coef x (B.Rw T.word (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x) =
        ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (LT T q) F x := by
      intro T hT
      rw [(hspec T).2 Ψ hΨ F hF x hx, map_list_sum, List.map_map]
      have e1 : ((terms T).map ((T.coef x) ∘ fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
            ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x))) =
          (terms T).map fun t => (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ)) t.1 •
            (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) t := by
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, map_smul, nfLeibOps_sc, smul_smul, mul_assoc]
      rw [e1]
      refine (nfLeibOps_sum_key Q (fun t => t.1) (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ))
        (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) (terms T)
        (fun t ht => ((hspec T).1 t ht).1.trans (hQle T hT))).trans ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      unfold B.opApply
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      have htm : t ∈ terms T := (List.mem_filter.1 ht).1
      have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (((hspec T).1 t htm).2.2.subset hX)
      simp only [Function.comp_apply, nfLeibOps_mk, if_pos hlie, ContinuousLinearMap.smul_apply]
    have hall : ∀ D' : B.DiffOp k r Wp Wq, (∀ T ∈ D', T ∈ Dop) →
        B.opApply D' (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
          ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (D'.flatMap fun T => LT T q) F x := by
      intro D'
      induction D' with
      | nil => intro _; simp [B.opApply]
      | cons T D' ih =>
        intro hsub
        have eA : ∀ (D'' : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (T :: D'') G x = T.coef x (B.Rw T.word G x) + B.opApply D'' G x := by
          intro D'' G; simp [B.opApply]
        have eB : ∀ (l1 l2 : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (l1 ++ l2) G x = B.opApply l1 G x + B.opApply l2 G x := by
          intro l1 l2 G; simp [B.opApply]
        rw [eA, hT1 T (hsub T List.mem_cons_self), ih fun T' hT' => hsub T' (List.mem_cons_of_mem _ hT'),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [List.flatMap_cons, eB, smul_add]
    exact hall Dop fun T hT => hT

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibVLin
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfVLin_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {ι : Type} (s : Finset ι) (a : Wp →L[ℂ] Wp) (b : Wq →L[ℂ] Wq) (c : ι → ℂ)
    (f : ι → Wq →L[ℂ] Wp) :
    a.comp ((∑ i ∈ s, c i • f i).comp b) = ∑ i ∈ s, c i • a.comp ((f i).comp b) := by
  ext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ContinuousLinearMap.sum_apply, map_sum, map_smul]

theorem vector_linearity_holds : NFVLin := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ Q c H Hq A hA hcont hdec hH pt hpt hGPoint
  unfold D.vecV
  have h : D.IsLocPt pt (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt := ⟨hpt, hGPoint⟩
  simp only [dif_pos h]
  by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN pt (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
  · simp only [dif_pos h']
    have hγ := h'.choose_spec.1
    have hZ := h'.choose_spec.2.1
    have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' pt h'.choose h.1 hZ
    have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
    have hGeq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt = Gf k r Bs.z Bs.z' h'.choose := by
      rw [hGq]
    obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' pt (r + 1) h.1.2 h.1.1
    have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs pt h'.choose h.1 hγ hZ
    have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
      ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
    have hZm := hZ.trans hmono
    obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos hA
    have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
      ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
        fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
    have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG

    have hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp),
        Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS →
        D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) G =
          ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS := by
      intro G hi
      have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) θ' ∧
          Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
      unfold D.orbJ
      rw [dif_pos hex]
      exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
        hex.choose_spec.2 hi

    have hiq : ∀ q, Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose (Hq q) p) Bs.μSS := by
      intro q
      obtain ⟨C, hC⟩ := hdec q (Gf k r Bs.z Bs.z' h'.choose) hpos
      have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose (Hq q)) Bs.μSS :=
        Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb (hcont q)
      refine Integrable.mono' (hmaj.const_mul (max C 0)) (hθ.1.aestronglyMeasurable.smul hm) ?_
      refine hdom (Hq q) (max C 0) (le_max_right _ _) fun p hp => ?_
      have hs := horb p hp
      refine (hC _ hs.1 (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp])).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

    have hae : (fun p => θ p • D.orbIntegrand Bs h'.choose H p) =ᵐ[Bs.μSS]
        fun p => ∑ q, c q (Gf k r Bs.z Bs.z' h'.choose) • (θ p • D.orbIntegrand Bs h'.choose (Hq q) p) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have hs := horb p hp
      simp only [D.orbIntegrand, B.rho]
      rw [hH _ hs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, nfVLin_comp_sum, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm (B.xiTau Bs (1, 1) p), smul_comm (θ p)]
    have hiH : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose H p) Bs.μSS :=
      (integrable_finsetSum _ fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))).congr hae.symm
    have hint : ∀ q ∈ (Finset.univ : Finset (Fin (Q + 1))), Integrable
        (fun a => c q (Gf k r Bs.z Bs.z' h'.choose) • (θ a • D.orbIntegrand Bs h'.choose (Hq q) a)) Bs.μSS :=
      fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))
    rw [hEq H hiH, integral_congr_ae hae, integral_finsetSum Finset.univ hint, hGeq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_smul, hEq (Hq q) (hiq q)]
  · simp only [dif_neg h', smul_zero, Finset.sum_const_zero]

end

end Formalism.FourierDecayAlt.P.CutBP
end

