module

public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0143
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfStepForm

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
section
namespace Formalism.FourierDecayAlt.P.TLB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]


open Classical in
def cTerm (c : ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun _ => c • ContinuousLinearMap.id ℂ _
  coefAdj := fun _ => conj c • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right, Complex.conj_conj]

theorem cTerm_word {c : ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).word = w := by
  unfold cTerm
  dsimp only
  rw [if_pos hw]

theorem cTerm_word_le (c : ℂ) (w : List (B.Mat k r)) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).word.length ≤ w.length := by
  unfold cTerm
  dsimp only
  split_ifs <;> simp

theorem cTerm_apply (c : ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).coef g (B.Rw (cTerm (Wp := Wp) (Wq := Wq) c w).word F g) = c • B.Rw w F g := by
  rw [cTerm_word hw]
  simp [cTerm]

theorem opOrder_le_of (Θ : B.DiffOp k r Wp Wq) (n : ℕ) (h : ∀ T ∈ Θ, T.word.length ≤ n) : B.opOrder Θ ≤ n := by
  induction Θ with
  | nil => simp [B.opOrder]
  | cons T Θ ih =>
    simp only [B.opOrder, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h T List.mem_cons_self) (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

theorem opOrder_cons_eq (T : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ T' ∈ Θ, T'.word.length ≤ T.word.length) : B.opOrder (T :: Θ) = T.word.length := by
  have h2 := opOrder_le_of Θ _ h
  simp only [B.opOrder, List.map_cons, List.foldr_cons] at h2 ⊢
  exact max_eq_left h2

def capOp (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) : B.DiffOp k r Wp Wq :=
  cTerm 0 (List.replicate (2 * r + k + 1) 0) :: Lw.map fun cw => cTerm (s * cw.1) cw.2

theorem zero_lie : B.inLie k r (0 : B.Mat k r) := by
  simp [B.inLie]

theorem opApply_capOp_tail (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Lw.map fun cw => (cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2)) F g =
      s • (Lw.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction Lw with
  | nil => simp [B.opApply]
  | cons cw Lw ih =>
    have ih' := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    simp only [B.opApply, List.map_cons, List.sum_cons, List.map_map] at ih' ⊢
    rw [smul_add, ← ih']
    congr 1
    rw [cTerm_apply _ _ (hL cw List.mem_cons_self), mul_smul]

theorem opApply_capOp (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (capOp k r Wp Wq s Lw) F g = s • (Lw.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  have e : B.opApply (capOp k r Wp Wq s Lw) F g =
      (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) 0)).coef g
        (B.Rw (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) 0)).word F g) +
      B.opApply (Lw.map fun cw => (cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2)) F g := by
    simp [B.opApply, capOp]
  rw [e, opApply_capOp_tail s Lw hL F g]
  simp [cTerm]

theorem opOrder_capOp (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, cw.2.length ≤ 2 * r + k + 1) :
    B.opOrder (capOp k r Wp Wq s Lw) = 2 * r + k + 1 := by
  have hw : (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).word =
      List.replicate (2 * r + k + 1) 0 :=
    cTerm_word fun X hX => by rw [List.eq_of_mem_replicate hX]; exact zero_lie
  unfold capOp
  rw [opOrder_cons_eq, hw, List.length_replicate]
  intro T hT
  rw [hw, List.length_replicate]
  obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
  exact (cTerm_word_le _ _).trans (hL cw hcw)

theorem cTerm_inDDPlus (D : B.RealPlaceData k r Wp Wq) (c : ℂ) (w : List (B.Mat k r)) (o : ℕ) (hw : w.length ≤ o)
    (T : B.DTerm k r Wp Wq) (hT : T = cTerm c w) :
    (B.CkOn ⊤ (C6.domL D ∅) T.coef ∧ B.CkOn ⊤ (C6.domL D ∅) T.coefAdj) ∧
    ∃ (P : B.Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (cc : ℕ) (es : List (Fin 0 × List (B.Mat k r))),
      U.IsPolyDeg 0 P ∧ (∀ l, l ∉ (∅ : Finset (Fin (r + 2))) → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, B.inLie k r X) ∧
      ∀ g ∈ C6.domL D ∅, T.coef g = (P g * C6.monoM D a b cc g) • C6.Epart (fun j : Fin 0 => j.elim0) es g := by
  subst hT
  refine ⟨⟨fun g₀ _ => ⟨Set.univ, fun _ => c • ContinuousLinearMap.id ℂ _, isOpen_univ, trivial, contDiffOn_const,
      fun _ _ _ => rfl⟩, fun g₀ _ => ⟨Set.univ, fun _ => conj c • ContinuousLinearMap.id ℂ _, isOpen_univ, trivial,
      contDiffOn_const, fun _ _ _ => rfl⟩⟩, fun _ => c, fun _ => 0, fun _ => 0, 0, [], ?_, ?_, ?_, by simp, ?_⟩
  · exact ⟨MvPolynomial.C c, by simp, fun g => by simp⟩
  · intro l _ _; exact ⟨rfl, rfl⟩
  · simpa using (cTerm_word_le (Wp := Wp) (Wq := Wq) c w).trans hw
  · intro g _
    simp [C6.monoM, C6.Epart, cTerm]
    rfl

end terms

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem lift_capelli_operators : TL.LiftCap := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨Lw, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum P.k P.r Y
  set s : ℂ := M.sgn P l0 with hs
  have hLie : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie P.k P.r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ Lw, cw.2.length ≤ 2 * P.r + P.k + 1 := fun cw h => (hLw cw h).2
  set Dop := TLB.capOp P.k P.r Wp Wq s Lw with hDop
  have hApp : ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ((2 * P.r + P.k + 1 : ℕ) : ℕ∞) (B.GV P.k P.r) f →
      ∀ g ∈ B.GV P.k P.r, B.opApply Dop f g = s • Q.CV P.k P.r Y f g := by
    intro f hf g hg
    rw [hDop, TLB.opApply_capOp s Lw hLie, hCV _ _ f hf g hg hg]
  refine ⟨0, fun j => j.elim0, Dop, fun j => j.elim0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).1
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).1
  · intro p hp f hf g hg
    rw [hDop, TLB.opOrder_capOp s Lw hlen] at hf
    have hgG : g ∈ B.GV P.k P.r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute P.k P.r Wp Wq Bs Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).2
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).2
  · intro F hF Φ hΦ y hy
    obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
    have hz := Bs.z_mem
    have hz' := Bs.z'_mem
    have hL := hD.2.2.1
    have hst := hD.2.2.2.1
    have hJ := Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
    have hGV : wCell P.k P.r (Fin.last P.r) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last P.r) y.1 * y.2 ∈ JF.Om P.k P.r Bs.z Bs.z' :=
      ⟨hGV, P5.Rad.wCell_mem_omPlus hz hz' hy.1 hy.2.1 hy.2.2⟩
    have h1 := JCx2.rma_QQi X L hL st s hst Y 0 0 Φ hy
    have h2 := (JCx2.rma_sandw X L hL Y P.r le_rfl _ _ (JCx2.rma_base X Y) (JCx2.rma_QL_loc Y)).2 0 0
      (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (resG P.k P.r (Fin.last P.r) (B.JF Bs F)) (fun y' hy' => hΦ y' hy') y hy
    have h3 := Formalism.FourierDecayAlt.P.chain_recursion_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) _ Y 0 0 hz hz'
      (JCx2.rma_isDom_omPlus hz hz') _ hJ y.1 hy.1 y.2 hy.2.1 hh.2
    rw [Fin.val_last] at h3
    have h4 := (JCx2.bcGood_tL (Bs := Bs) (ε := ε) s Y 0 0).2.1 F hN _ hh
    have h5 := Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (F := fun g => s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 F g)
      (F' := B.opApply Dop F) (a := 1) (fun g hg => by
        rw [one_smul, hApp F (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF.1) g hg]; rfl) hGV
    refine Eq.trans h1 ?_
    rw [h2, ← h3]
    simp only [Q.resG]
    have h4' : B.JF Bs (fun g => s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 F g) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) =
        s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 (B.JF Bs F) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) := h4
    rw [h5, one_smul, h4', smul_comm]

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ckOn_top_of_nat {f : B.Mat k r → E} (hf : ∀ m : ℕ, B.CkOn (m : ℕ∞) (B.GV k r) f) :
    B.CkOn ⊤ (B.GV k r) f := by
  intro g₀ hG
  refine ⟨P5.Rad.retDom g₀, fun Y => f (P5.Rad.ret g₀ Y), P5.Rad.isOpen_retDom g₀, P5.Rad.self_mem_retDom hG,
    ?_, ?_⟩
  · intro Y hY
    apply ContDiffAt.contDiffWithinAt
    rw [show (((⊤ : ℕ∞) : WithTop ℕ∞)) = ∞ from rfl, contDiffAt_infty]
    intro n
    obtain ⟨U, F, hU, hYU, hF, hfF⟩ := hf n (P5.Rad.ret g₀ Y) (P5.Rad.ret_mem hG hY)
    have hr : ContDiffAt ℝ ∞ (P5.Rad.ret g₀) Y :=
      (P5.Rad.cd_ret g₀).contDiffAt ((P5.Rad.isOpen_retDom g₀).mem_nhds hY)
    have hFa : ContDiffAt ℝ n F (P5.Rad.ret g₀ Y) := by
      have := hF.contDiffAt (hU.mem_nhds hYU)
      exact_mod_cast this
    have hcomp : ContDiffAt ℝ n (fun Y' => F (P5.Rad.ret g₀ Y')) Y := hFa.comp Y (hr.of_le (mod_cast le_top))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(P5.Rad.isOpen_retDom g₀).mem_nhds hY, hr.continuousAt.preimage_mem_nhds (hU.mem_nhds hYU)]
      with Y' h1 h2
    exact hfF _ h2 (P5.Rad.ret_mem hG h1)
  · intro Y hY hYG
    show f Y = f (P5.Rad.ret g₀ Y)
    rw [P5.Rad.ret_self hG hYG hY.1]

theorem rdV_congrGV {X : B.Mat k r} (hX : B.inLie k r X) {h₁ h₂ : B.Mat k r → E}
    (hh : ∀ g ∈ B.GV k r, h₁ g = h₂ g) : ∀ g ∈ B.GV k r, RdV X h₁ g = RdV X h₂ g := by
  intro g hg
  unfold RdV
  congr 1
  funext t
  exact hh _ (B5.curve_mem hg hX t)

theorem rw_congrGV : ∀ (v : List (B.Mat k r)), (∀ X ∈ v, B.inLie k r X) → ∀ {h₁ h₂ : B.Mat k r → E},
    (∀ g ∈ B.GV k r, h₁ g = h₂ g) → ∀ g ∈ B.GV k r, B.Rw v h₁ g = B.Rw v h₂ g
  | [], _, _, _, hh => hh
  | X :: v, hv, _, _, hh => by
    show ∀ g ∈ B.GV k r, RdV X (B.Rw v _) g = RdV X (B.Rw v _) g
    exact rdV_congrGV (hv X (by simp)) (rw_congrGV v (fun Y hY => hv Y (by simp [hY])) hh)

theorem rdV_zero_near {X : B.Mat k r} (hX : B.inLie k r X) {h : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hh : ∀ g ∈ B.GV k r, g ∈ U → h g = 0) : ∀ g ∈ B.GV k r, g ∈ U → RdV X h g = 0 := by
  intro g hg hgU
  unfold RdV
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := (B5.curve_contDiff g X).continuous
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [B5.curve_zero]; exact hU.mem_nhds hgU
  have hev : (fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hh _ (B5.curve_mem hg hX t) ht
  rw [hev.deriv_eq]
  simp

theorem rw_zero_near : ∀ (v : List (B.Mat k r)), (∀ X ∈ v, B.inLie k r X) → ∀ {h : B.Mat k r → E}
    {U : Set (B.Mat k r)}, IsOpen U → (∀ g ∈ B.GV k r, g ∈ U → h g = 0) →
    ∀ g ∈ B.GV k r, g ∈ U → B.Rw v h g = 0
  | [], _, _, _, _, hh => hh
  | X :: v, hv, _, _, hU, hh => by
    show ∀ g ∈ B.GV k r, g ∈ _ → RdV X (B.Rw v _) g = 0
    exact rdV_zero_near (hv X (by simp)) hU (rw_zero_near v (fun Y hY => hv Y (by simp [hY])) hU hh)

end gen

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_congrGV (Θ : B.DiffOp k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hh : ∀ g ∈ B.GV k r, F₁ g = F₂ g) : ∀ g ∈ B.GV k r, B.opApply Θ F₁ g = B.opApply Θ F₂ g := by
  intro g hg
  unfold B.opApply
  congr 1
  apply List.map_congr_left
  intro T _
  rw [rw_congrGV T.word T.word_lie hh g hg]

theorem opApply_zero_near (Θ : B.DiffOp k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hh : ∀ g ∈ B.GV k r, g ∈ U → F g = 0) : ∀ g ∈ B.GV k r, g ∈ U → B.opApply Θ F g = 0 := by
  intro g hg hgU
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [rw_zero_near T.word T.word_lie hU hh g hg hgU, map_zero]

end ops

section casts

variable {k : ℕ}

theorem castM_GV {a b : ℕ} (e : a = b) {x : B.Mat k a} (hx : x ∈ B.GV k a) : D.castM e x ∈ B.GV k b := by
  subst e; rwa [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem gN_castM {a b : ℕ} (e : a = b) (x : B.Mat k a) : B.gN (D.castM e x) = B.gN x := by
  subst e; rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem Gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (x : B.Mat k a) :
    Gf k a (D.castV e.symm z) (D.castV e.symm z') x = Gf k b z z' (D.castM e x) := by
  subst e; rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self,
    Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end casts

theorem isCompact_gN_le (k r : ℕ) (R : ℝ) : IsCompact {g : B.Mat k r | B.gN g ≤ R} := by
  have hcl : IsClosed {g : B.Mat k r | B.gN g ≤ R} := isClosed_le Formalism.FourierDecayAlt.P.B6.gN_continuous continuous_const
  refine (isCompact_closedBall (0 : B.Mat k r) R).of_isClosed_subset hcl ?_
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Matrix.norm_le_iff ((norm_nonneg _).trans ((Formalism.FourierDecayAlt.P.Dx3.entry_le_gN g 0 0).trans hg))).2 ?_
  intro i j
  exact (Formalism.FourierDecayAlt.P.Dx3.entry_le_gN g i j).trans hg

end Formalism.FourierDecayAlt.P.PBE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Ent

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem site_lc (X : ActualOps P.k P.r z z' π π') {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
    (hAL : IsActualLevel X L) (l : Fin P.r) :
    L.p l ∈ presAlg (lcSub P.k P.r z z' π π') ∧ L.c l ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      L.ci l ∈ presAlg (lcSub P.k P.r z z' π π') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
  · rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
  · rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)

theorem QQ_lc (X : ActualOps P.k P.r z z' π π') (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ presAlg (lcSub P.k P.r z z' π π') :=
  mkPair_mem_preservingAlgebra (t_lc X Y a b) (t_lc X (star Y) b a)

theorem RRi_lc (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRi L st i w ∈ entSub (presAlg (lcSub P.k P.r z z' π π')) := by
  obtain ⟨-, -, hAL, hQQ, -⟩ := hD
  refine rrw_mem (QQi L st i) (QQi_mem L st _ i (fun Y _ a b => ?_) (fun l _ => site_lc X hAL l)) w hw
  rw [hQQ Y, Matrix.smul_apply]
  exact (presAlg (lcSub P.k P.r z z' π π')).smul_mem (QQ_lc X Y a b) _

end Ent

section G

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem int_lc (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ := by
  by_cases hc : c ∈ OmX r
  · exact intOn_cpt μ hμ c hc Φ (lcSub_le_cptSub hΦ) Ψ (lcSub_le_cptSub hΨ)
  · have e : (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) = fun _ => 0 := by
      funext g
      rw [radSp_zero_off Φ (x := (c, Matrix.of g)) (fun h => hc h.1)]
      exact hsInner_zero_left _
    rw [e]; exact integrable_zero _ _ _

end G

section Form

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntG_herKc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) (x y : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D i) x) (hy : InK (herKc S P z z' π π' L st l0 D i) y)
    (c' : Cf P.r i) (a : Ix S) :
    Integrable (fun g : Mt P.k P.r =>
      B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ := by
  have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
    (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
  have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
  have hu : act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' :=
    (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
  exact int_lc μ hD.2.1 hu (hle (hy a)) _

def FormIntOuterCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herKc S P z z' π π' L st l0 D i) y →
      Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))

def StepDensCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0

theorem stepFormCptAll_of (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine ⟨hSD Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ', fun w hw i c hc x y hx hy => ⟨?_, ?_⟩⟩
  · exact fun c' a => formIntG_herKc P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' w hw i c x y hx hy c' a
  · exact hFO Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy

theorem thmPActualCpt_of_outer (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : ThmPActualCpt :=
  thmPActualCpt_of_stepForm (stepFormCptAll_of hSD hFO)

end Form

end Formalism.FourierDecayAlt.P5.HerC
end
end

