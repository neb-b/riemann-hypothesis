module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCV
section
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coefficient_vector_in_class : CVCC := by
  intro k r Wp Wq _ _ _ _ _ _ s Y A m F _ hF
  exact Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class k r _ A m F Y s hF

theorem coefficient_vector_congr : CVCongr := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F F₁ hF hF₁ heq g hg
  have hmono : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) G →
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Set.univ ∩ B.GV k r) G := by
    intro G hG g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, hfe⟩ := hG g₀ hg₀.2
    exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) Set.univ F F₁ Y isOpen_univ
    (hmono F hF) (hmono F₁ hF₁) (fun x hx => heq x hx.2) g ⟨trivial, hg⟩
  simp only [Pi.smul_apply]
  rw [h]

theorem cV_zero {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    Q.CV k r Y (0 : B.Mat k r → E) = 0 := by
  have hop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)),
      Formalism.QuantumDeterminants.Top (Q.EH k r) u a b (0 : B.Mat k r → E) = 0 := by
    intro u a b
    funext g
    simp [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV]
  have hfold : ∀ l : List ((B.Mat k r → E) → (B.Mat k r → E)), (∀ T ∈ l, T 0 = 0) →
      l.foldr (fun T h => T h) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons T l ih =>
      simp only [List.foldr_cons]
      rw [ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT'))]
      exact hl T List.mem_cons_self
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [hfold _ ?_, smul_zero]
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hop _ _ _

theorem coefficient_vector_support : CVSupp := by
  intro k r Wp Wq _ _ _ _ _ _ z z' c s Y F hF hsupp g hg hne
  by_contra hlt
  push_neg at hlt
  have hU : IsOpen {x | Gf k r z z' x < c} :=
    isOpen_lt (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z') continuous_const
  have hF0 : ∀ x ∈ {x | Gf k r z z' x < c} ∩ B.GV k r,
      F x = (0 : B.Mat k r → (Wq →L[ℂ] Wp)) x := by
    intro x hx
    by_contra hne'
    exact absurd (hsupp x hx.2 hne') (not_le.mpr hx.1)
  have hCk0 : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r)
      (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hCkF : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) ({x | Gf k r z z' x < c} ∩ B.GV k r) F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU', hgU, hcd, hfe⟩ := hF g₀ hg₀.2
    exact ⟨U, f', hU', hgU, hcd.of_le (WithTop.coe_le_coe.mpr le_top), hfe⟩
  have h := Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r (Wq →L[ℂ] Wp) {x | Gf k r z z' x < c} F 0 Y hU
    hCkF hCk0 hF0 g ⟨hlt, hg⟩
  apply hne
  simp only [Pi.smul_apply]
  rw [h, cV_zero, Pi.zero_apply, smul_zero]

theorem coefficient_vector_smoothness : CVSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ s Y F hF
  have hadd : ∀ {f g : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) g →
      B.CkOn ⊤ (B.GV k r) (f + g) := by
    intro f g hf hg g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    obtain ⟨U2, f2, hU2, h2, hc2, he2⟩ := hg g₀ hg₀
    refine ⟨U1 ∩ U2, f1 + f2, hU1.inter hU2, ⟨h1, h2⟩,
      (hc1.mono Set.inter_subset_left).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro x hx hxG
    simp [he1 x hx.1 hxG, he2 x hx.2 hxG]
  have hsmul : ∀ (c : ℂ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) f →
      B.CkOn ⊤ (B.GV k r) (c • f) := by
    intro c f hf g₀ hg₀
    obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
    refine ⟨U1, c • f1, hU1, h1, hc1.const_smul c, ?_⟩
    intro x hx hxG
    simp [he1 x hx hxG]
  have hzero : B.CkOn ⊤ (B.GV k r) (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
    fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hrd : ∀ X : B.Mat k r, B.inLie k r X → ∀ {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.REAL.RdV X f) := by
    intro X hX f hf
    have h1 : B.CkOn ((⊤ : ℕ∞) + 1) (B.GV k r) f := by
      rw [top_add]
      exact hf
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX h1
  have hTop : ∀ (u : ℂ) (a b : Fin (2 * r + k + 1)) {f : B.Mat k r → (Wq →L[ℂ] Wp)},
      B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f) := by
    intro u a b f hf
    have e : Formalism.QuantumDeterminants.Top (Q.EH k r) u a b f = (if a = b then u • f else 0) +
        (Formalism.REAL.RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f +
          Complex.I • Formalism.REAL.RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f) := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, Q.EH, Formalism.QuantumDeterminants.EabH, Pi.add_apply, Pi.smul_apply]
      split_ifs <;> simp
    rw [e]
    refine hadd ?_ (hadd (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie1 _) hf) (hsmul _ (hrd _ (Formalism.FourierDecayAlt.P.Qb1.lie2 _) hf)))
    split_ifs
    · exact hsmul u hf
    · exact hzero
  have hfold : ∀ l : List ((B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp))),
      (∀ T ∈ l, ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (T f)) →
      ∀ f, B.CkOn ⊤ (B.GV k r) f → B.CkOn ⊤ (B.GV k r) (l.foldr (fun T h => T h) f) := by
    intro l hl f hf
    induction l with
    | nil => exact hf
    | cons T l ih =>
      simp only [List.foldr_cons]
      exact hl T List.mem_cons_self _ (ih (fun T' hT' => hl T' (List.mem_cons_of_mem _ hT')))
  apply hsmul s
  unfold Q.CV Q.capL Formalism.QuantumDeterminants.qminorOp
  refine Finset.sum_induction _ (fun f => B.CkOn ⊤ (B.GV k r) f) (fun a b ha hb => hadd ha hb) hzero ?_
  intro σ _
  apply hsmul
  refine hfold _ ?_ F hF
  intro T hT f hf
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  exact hTop _ _ _ hf

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section consts

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_const (a : E) : ∀ v : List (B.Mat k r),
    B.Rw v (fun _ => a) = (fun _ => a) ∨ B.Rw v (fun _ => a) = (fun _ => (0 : E))
  | [] => Or.inl rfl
  | X :: v => by
    right
    funext g
    simp only [B.Rw, List.foldr_cons]
    rcases rw_const a v with h | h
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]

theorem dLR_const (a : E) (u v : List (B.Mat k r)) :
    B.dLR u v (fun _ => a) = (fun _ => a) ∨ B.dLR u v (fun _ => a) = (fun _ => (0 : E)) := by
  induction u with
  | nil => exact rw_const a v
  | cons X u ih =>
    right
    simp only [Formalism.FourierDecayAlt.B.dLR, List.foldr_cons] at ih ⊢
    rcases ih with h | h <;> (rw [h]; funext g; simp [Formalism.FourierDecayAlt.B.LdV])

theorem norm_dLR_const_le (a : E) (u v : List (B.Mat k r)) (g : B.Mat k r) : ‖B.dLR u v (fun _ => a) g‖ ≤ ‖a‖ := by
  rcases dLR_const a u v with h | h <;> simp [h]

theorem ckOn_const' {m : ℕ∞} {UU : Set (B.Mat k r)} (a : E) : B.CkOn m UU (fun _ => a) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => a, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

end consts

theorem mem_capOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) {T : B.DTerm k r Wp Wq} (hT : T ∈ TLB.capOp k r Wp Wq s Lw) :
    ∃ (c : ℂ) (w : List (B.Mat k r)), T = TLB.cTerm c w := by
  unfold TLB.capOp at hT
  rcases List.mem_cons.1 hT with h | h
  · exact ⟨0, _, h⟩
  · obtain ⟨cw, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, _, rfl⟩

theorem capacity_theta_facts : CapThFacts := by
  intro k r Wp Wq _ _ _ _ _ _ D s Y ε m
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ capLw k r Y, cw.2.length ≤ 2 * r + k + 1 := fun cw h => (hLw cw h).2
  have hord : B.opOrder (capTh k r Wp Wq s Y) = 2 * r + k + 1 := TLB.opOrder_capOp s _ hlen
  have hApp : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GV k r, B.opApply (capTh k r Wp Wq s Y) F g = s • Q.CV k r Y F g := by
    intro F hF g hg
    unfold capTh
    rw [TLB.opApply_capOp s _ hLie, hCV _ _ F hF g hg hg]
    rfl
  refine ⟨hord, ?_, ?_, ?_, hApp⟩
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  · intro p hp f hf g hg
    rw [hord] at hf
    have hgG : g ∈ B.GV k r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem D hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute k r Wp Wq D Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v _ _ _ g _ _ => ?_⟩
    rw [Real.rpow_zero, mul_one]
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩

theorem beta_form_congr_holds : BetaCongr := by
  intro k r Wp Wq _ _ _ _ _ _ D F F₁ F' F₁' hF hF'
  unfold B.beta
  refine Formalism.FourierDecayAlt.P.JFxG.betaBig_congr D (fun g hg => ?_) (fun g hg => ?_)
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := F₁) (a := 1) (fun g hg => by rw [one_smul, hF g hg]) hg.1
    rw [h, one_smul]
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F') (F' := F₁') (a := 1) (fun g hg => by rw [one_smul, hF' g hg]) hg.1
    rw [h, one_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERComm
section
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem coefficient_vector_commutation : CVComm := by
  intro k r Wp Wq _ _ _ _ _ _ s Y Y' F hF g hg
  have hs : ∀ (Z α : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)),
      Q.CV k r Z (α • f) = α • Q.CV k r Z f := fun Z => P5.tL_smulC 0 0 0 Z 0 0
  have hsm : Q.SmoothLev k r 0 Set.univ F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ ((CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
    exact ⟨U, f', hU, hgU, hc, fun x hx hxl => he x hx ((CapelliUnderIntegral.glev0 x).1 hxl)⟩
  have hc := capelli_commutation _ k r 0 Set.univ F isOpen_univ hsm g
    ⟨(CapelliUnderIntegral.glev0 g).2 hg, trivial⟩ (Q.uC k r 0 Y) (Q.uC k r 0 Y')
  simp only [Pi.smul_apply, hs]
  exact congrArg (fun t => s • s • t) hc

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERHaarPos
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

theorem haar_open_pos {k r : ℕ} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {O : Set (Mt k r)}
    (hO : IsOpen O) {g₀ : Mt k r} (hg₀ : Matrix.of g₀ ∈ B.GV k r) (hg₀O : g₀ ∈ O) : μ O ≠ 0 := by
  intro h0
  have hnull : ∀ b ∈ B.GV k r, μ (lmulM (k := k) (r := r) b ⁻¹' O) = 0 := by
    intro b hb
    have hm : Measurable (lmulM (k := k) (r := r) b) := (BesselUnitaryEquiv.continuous_lmulM b).measurable
    rw [← Measure.map_apply hm hO.measurableSet, hμ.left b hb, h0]
  let U : {b : B.Mat k r // b ∈ B.GV k r} → Set (Mt k r) := fun b => lmulM (k := k) (r := r) b.1 ⁻¹' O
  have hUo : ∀ i, IsOpen (U i) := fun i => hO.preimage (BesselUnitaryEquiv.continuous_lmulM i.1)
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hcov : {x : Mt k r | Matrix.of x ∈ B.GV k r} ⊆ ⋃ i, U i := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨Matrix.of g₀ * (Matrix.of x)⁻¹,
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hg₀ (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem hx)⟩, ?_⟩
    have hx' : Matrix.of x ∈ B.GV k r := hx
    have e : lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x = g₀ := by
      unfold lmulM
      rw [mul_assoc, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hx').2, mul_one]
      rfl
    show lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x ∈ O
    rw [e]
    exact hg₀O
  have hGV0 : μ {x : Mt k r | Matrix.of x ∈ B.GV k r} = 0 := by
    refine measure_mono_null (hcov.trans hT.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun i _ => hnull i.1 i.2
  have hsub : (Set.univ : Set (Mt k r)) ⊆ {x : Mt k r | Matrix.of x ∈ B.GV k r} ∪ (B.GV k r)ᶜ := by
    intro x _
    by_cases hx : Matrix.of x ∈ B.GV k r
    · exact Or.inl hx
    · exact Or.inr hx
  have huniv : μ Set.univ = 0 := measure_mono_null hsub (measure_union_null hGV0 hμ.conc)
  exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyTr
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem En.bessel_folding_at_built_place : En.BesselFoldBuilt := En.besselFoldBuilt_of En.coefficient_vector_in_L2_class

theorem energyTr_of_betaFrame (h : En.BetaFrame) : EnergyTr :=
  En.energyTr_of_parts En.folding_reversal_holds En.admissible_length_holds En.bessel_folding_at_built_place En.L2_bound_at_built_place_holds h

theorem energy_trace_identity_holds : EnergyTr := energyTr_of_betaFrame En.beta_frame_identity_holds

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAlg
section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inCC_antiA {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {A A' : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : A' ≤ A) (hF : B.InCC A m F) : B.InCC A' m F := by
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hc1, fun u w hu hw hl g hg => ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 h) (norm_nonneg _)).trans
    (hc2 u w hu hw hl g hg)

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem cCg_antiA {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {A A' Bg : ℝ} {F : GFn S v} (h : A' ≤ A)
    (hF : CCg S v A Bg F) : CCg S v A' Bg F :=
  fun m => inCC_antiA (by linarith) (hF m)

theorem locCC_antiA {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A A' Bg : ℝ} {J : GFn S v} (h : A' ≤ A) (hJ : LocCC S T v A Bg J) : LocCC S T v A' Bg J := by
  refine ⟨hJ.1, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  exact ⟨F, h1, cCg_antiA h h2, h3⟩

theorem locCC_JF {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} {F : GFn S v} (hF : B.CkOn ⊤ (B.GV S.G.k S.G.r) F) (hA : ∀ m : ℕ, B.InCC A m F)
    (hFF : B.JF (T v).base F ∈ smoothFormsPositiveCone S T v) (hBg : 0 ≤ Bg) : LocCC S T v A Bg (B.JF (T v).base F) :=
  ⟨hFF, fun _ _ => ⟨F, hF, fun m => inCC_antiA (sub_le_self _ (mul_nonneg hBg (Nat.cast_nonneg m))) (hA m),
    fun _ _ _ => rfl⟩⟩

theorem locCC_smul {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {A Bg : ℝ} (c : ℂ) {J : GFn S v} (hJ : LocCC S T v A Bg J) : LocCC S T v A Bg (c • J) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_smul hJ.1 c, fun δ hδ => ?_⟩
  obtain ⟨F, h1, h2, h3⟩ := hJ.2 δ hδ
  refine ⟨c • F, Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' c h1, fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c0, hc0⟩ := h2 m
    exact ⟨‖c‖ * c0, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul c hc0⟩
  · rw [Formalism.FourierDecayAlt.P.CutMP.En.JF_smul', Pi.smul_apply, h3 x hx hG]

end loc

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLZero
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_zero_holds : SAZero := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he X hX y hy h0
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hw : 0 < Real.sqrt (MA.wq S.G.k y (D.parOf S v).TT) := by
    apply Real.sqrt_pos.2
    unfold MA.wq
    exact mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hy.1 l)) _)
      (pow_pos (sub_pos.2 hy.2) _)
  have hin : ∀ π, inner ℂ (B.hsVec (e π y.2)) (B.hsVec (X (B.gq (T v).base y))) = 0 := by
    intro π
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he X hX π
    have h := h0 π
    unfold trJ at h
    rw [En.toSm_val_of_mem _ hsm] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (Complex.ofReal_ne_zero.2 hw.ne')
    · exact h
  have hfib := En.fibre_membership_holds E Wp Wq S T v hplace X hX y hy
  rw [(he.2 y.2 hy.2).2.2 _ hfib]
  simp [hin]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {Φ Ψ : RadSp k r z z' π π'}
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : (c, g) ∈ DomR k r z z'
  · exact h (c, g) hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

end Formalism.FourierDecayAlt.P.PBFV

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

