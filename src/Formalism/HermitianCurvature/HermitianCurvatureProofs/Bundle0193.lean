module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSelfNeZero
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_self_ne_zero {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  rw [Tz, h] at hT
  simp at hT

theorem herm_proj_zero (x z : Fin (2 * r + k + 1) → ℂ) (hc : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (x - (herm (Hpk k r) x z / herm (Hpk k r) z z) • z) z = 0 := by
  rw [herm_sub_left, herm_smul_left]
  field_simp
  ring

theorem coreW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ξ : B.Mat k r)
    (h1 : ∀ u, inWb k r u → inWb k r (ξ *ᵥ u))
    (h2 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) (ξ *ᵥ u) v = -herm (Hpk k r) u (ξ *ᵥ v))
    (h3 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
      herm (Hpk k r) (ξ *ᵥ u) v = 0)
    (N : ℕ) (h4 : ∀ u, inWb k r u → (ξ ^ N) *ᵥ u = 0) :
    ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
  set c := herm (Hpk k r) z z with hcdef
  have hc0 : c ≠ 0 := herm_self_ne_zero hT

  have stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z := by
    intro w hw hwz
    set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef
    have hy : inWb k r y := inWb_sub (h1 w hw) (inWb_smul _ hz)
    have hyz : herm (Hpk k r) y z = 0 := herm_proj_zero _ _ hc0
    have hyy : herm (Hpk k r) y y = 0 := by
      have e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0 := h3 w y hw hy hwz hyz
      have e2 : herm (Hpk k r) z y = 0 := by rw [herm_swap, hyz, star_zero]
      calc herm (Hpk k r) y y
          = herm (Hpk k r) (ξ *ᵥ w) y - (herm (Hpk k r) (ξ *ᵥ w) z / c) * herm (Hpk k r) z y := by
            conv_lhs => rw [hydef]
            rw [herm_sub_left, herm_smul_left]
        _ = 0 := by rw [e1, e2]; ring
    have : y = 0 := wb_definite hz hT hy hyz (by rw [hyy]; simp)
    exact sub_eq_zero.1 this
  set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ
  set b := ξ *ᵥ z - μ • z with hbdef
  have hb : inWb k r b := inWb_sub (h1 z hz) (inWb_smul _ hz)
  have hbz : herm (Hpk k r) b z = 0 := herm_proj_zero _ _ hc0
  have hξz : ξ *ᵥ z = μ • z + b := by rw [hbdef]; abel

  have stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z := by
    intro w hw hwz
    rw [stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]
    congr 1
    ring
  have hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z := stepB b hb hbz
  have hNz := h4 z hz

  have hb0 : b = 0 := by
    by_contra hb0
    have hbb : herm (Hpk k r) b b ≠ 0 := by
      intro h
      exact hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))
    set l := -(herm (Hpk k r) b b) / c with hl
    have hl0 : l ≠ 0 := div_ne_zero (neg_ne_zero.2 hbb) hc0
    let f : ℕ → ℂ × ℂ := fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0)
      (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m
    have hf0 : f 0 = (1, 0) := rfl
    have hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1) := fun m => rfl
    have hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b := by
      intro m
      induction m with
      | zero => rw [hf0, pow_zero, one_mulVec]; simp
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]
        module
    rw [hpow] at hNz
    have hp : (f N).1 = 0 := by
      have := congrArg (fun x => herm (Hpk k r) x z) hNz
      simp only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hc0
    have hq : (f N).2 = 0 := by
      rw [hp, zero_smul, zero_add] at hNz
      exact (smul_eq_zero.1 hNz).resolve_right hb0
    have hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0 := by
      intro m
      induction m with
      | zero => left; rw [hf0]; exact one_ne_zero
      | succ m ih =>
        by_contra hcon
        push Not at hcon
        rw [hfs] at hcon
        obtain ⟨e1, e2⟩ := hcon
        simp only at e1 e2
        rw [e2, mul_zero, zero_add] at e1
        have : (f m).2 = 0 := (mul_eq_zero.1 e1).resolve_left hl0
        rcases ih with h | h
        · exact h e2
        · exact h this
    rcases hnz N with h | h
    · exact h hp
    · exact h hq

  have hξz' : ξ *ᵥ z = μ • z := by rw [hξz, hb0, add_zero]
  have hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]
  rw [hpow2] at hNz
  have hμ0 : μ = 0 := by
    have := congrArg (fun x => herm (Hpk k r) x z) hNz
    simp only [herm_smul_left, herm_zero_left] at this
    exact pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1
  have hξz0 : ξ *ᵥ z = 0 := by rw [hξz', hμ0, zero_smul]
  intro u hu
  set α := herm (Hpk k r) u z / c
  have hu' : inWb k r (u - α • z) := inWb_sub hu (inWb_smul _ hz)
  have hu'z : herm (Hpk k r) (u - α • z) z = 0 := herm_proj_zero _ _ hc0
  have e : u = α • z + (u - α • z) := by abel
  rw [e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInvariantCellAction
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ}

def lr (hr : 1 ≤ r) : Fin r := ⟨r - 1, by omega⟩

theorem lr_succ (hr : 1 ≤ r) : (lr hr).succ = Fin.last r := Fin.ext (by simp [lr]; omega)

section Br1

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem br1 (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 D) {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) :
    resG k r l.castSucc J c ∈ FFl k r z z' π π' l.castSucc (Qx6.Dcell D l.castSucc c) ∧
      IsDom k r z z' l.castSucc (Qx6.Dcell D l.castSucc c) :=
  ⟨(Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ l.castSucc).2 c hc,
    Qx6.dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.castSucc c hc⟩

end Br1

theorem cell_preimage_mem_domain {D : Set (Mx k r)} {c : Fin r → ℂ} (l : Fin r) {g : Mx k r}
    (hg : wCell k r l.succ c * g ∈ D) : g ∈ Qx6.Dc1 l (Qx6.Dcell D l.castSucc c) c := by
  show wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D
  rw [← Matrix.mul_assoc, ← Qx6.wCell_succ]
  exact hg

section Br2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem br2 (l : Fin r) (Θ : (Mx k r → X) → (Mx k r → X)) (hS : Formalism.FourierDecayAlt.P5.SmulC Θ) (c : Fin r → ℂ)
    (hL : ∀ f : Mx k r → X,
      Θ (fun x => f (wCell k r l.castSucc c * x)) = fun x => Θ f (wCell k r l.castSucc c * x))
    (J : Mx k r → X) (g : Mx k r) :
    resG k r l.succ (Θ J) c g =
      ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Θ (resG k r l.castSucc J c) (w1 k r l (c l) * g) := by
  rw [Qx6.resG_succ]
  show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • resG k r l.castSucc (Θ J) c (w1 k r l (c l) * g) = _
  congr 1
  have e : resG k r l.castSucc J c =
      ((Qx6.gam k r l.castSucc c : ℝ) : ℂ) • fun x => J (wCell k r l.castSucc c * x) := by
    funext x
    rfl
  rw [e, hS, hL]
  rfl

end Br2

theorem unipotent_fixes_base_vector (l : Fin r) (a : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    w1 k r l a *ᵥ z = z := by
  have hl := l.isLt
  have ze : z (eI k r l) = 0 := hz _ (Or.inl (by simp [eI]))
  have zs : z (esI k r l) = 0 := hz _ (Or.inr (by simp [esI]; omega))
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Qx3.sw k l p)]
  · rw [Qx3.w1_apply, Qx3.sw_sw, if_pos rfl]
    rcases Qx3.tri l p with h | h | ⟨h1, h2⟩
    · subst h; rw [Qx3.sw_e, zs, ze, mul_zero]
    · subst h; rw [Qx3.sw_es, ze, zs, mul_zero]
    · rw [Qx3.sw_o l h1 h2, Qx3.dd_o l a h1 h2, one_mul]
  · intro q _ hq
    have : p ≠ Qx3.sw k l q := fun h => hq (by rw [h, Qx3.sw_sw])
    rw [Qx3.w1_apply, if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wCell_fix_wb (i : Fin (r + 1)) (c : Fin r → ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    wCell k r i c *ᵥ z = z := by
  unfold wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_base_vector a _ hz]

theorem hermitian_invariant_unipotent (l : Fin r) {a : ℂ} (ha : a ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((w1 k r l a * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← unipotent_fixes_base_vector l a hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Qx3.weyl_cell_mem_unitary l ha) _ _

theorem hermitian_invariant_cell_action (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((wCell k r i c * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← wCell_fix_wb i c hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Formalism.FourierDecayAlt.P.PBF.prod_w1_mem_unitary_Hpk c hc _) _ _

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
section
namespace Formalism.FourierDecayAlt.P.TLB

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section mulAt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

def MulAt (x : (Fin r → ℂ) × Q.Mx k r) (T : Module.End ℂ (Q.RadSp k r z z' π π')) (s : ℂ) : Prop :=
  ∀ Φ : Q.RadSp k r z z' π π', (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = s • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

theorem mulAt_one (x : (Fin r → ℂ) × Q.Mx k r) : MulAt (z := z) (z' := z') (π := π) (π' := π') x 1 1 := by
  intro Φ; simp

theorem mulAt_mul {x : (Fin r → ℂ) × Q.Mx k r} {T₁ T₂ : Module.End ℂ (Q.RadSp k r z z' π π')} {s₁ s₂ : ℂ}
    (h₁ : MulAt x T₁ s₁) (h₂ : MulAt x T₂ s₂) : MulAt x (T₁ * T₂) (s₁ * s₂) := by
  intro Φ
  rw [Module.End.mul_apply, h₁, h₂, smul_smul]

theorem pr_mul_fst (a b : Q.Pr (Q.RadSp k r z z' π π')) : (a * b).1 = a.1 * b.1 := rfl

theorem pr_one_fst : (1 : Q.Pr (Q.RadSp k r z z' π π')).1 = 1 := rfl

theorem mulAt_ofFn {x : (Fin r → ℂ) × Q.Mx k r} :
    ∀ {n : ℕ} (T : Fin n → Q.Pr (Q.RadSp k r z z' π π')) (s : Fin n → ℂ), (∀ i, MulAt x (T i).1 (s i)) →
      MulAt x (List.ofFn T).prod.1 (∏ i, s i)
  | 0, T, s, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, pr_one_fst]
    exact mulAt_one x
  | n + 1, T, s, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, pr_mul_fst]
    exact mulAt_mul (h 0) (mulAt_ofFn (fun i => T i.succ) (fun i => s i.succ) fun i => h i.succ)

end mulAt

section fns

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fibBound_one {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) : C6.FibBound D (fun _ => (1 : C6.EndH Wp Wq)) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 1, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun ε _ i => ⟨‖(1 : C6.EndH Wp Wq)‖, fun u v _ g hg _ => ?_⟩⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  calc ‖Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw (Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) (fun _ => (1 : C6.EndH Wp Wq)) g‖
      ≤ ‖(1 : C6.EndH Wp Wq)‖ := JCx2.pd_Dw_const _ _ _
    _ ≤ ‖(1 : C6.EndH Wp Wq)‖ * B.gN g ^ (3 * (r + 1) * i) :=
      le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg))

theorem liftScalar (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) (κ i j c : ℕ) (Pol : B.Mat Pa.k Pa.r → ℂ)
    (a : Q.Pr (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')) (hP : U.IsPolyDeg κ Pol)
    (hinv : ∀ p, Bs.inSS p → ∀ g, Pol (B.sgs p g) = Pol g)
    (hrad : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x a.1
      (Pol (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) *
        (Dmin Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) (Fin.last _))⁻¹ ^ i *
        (star (Dmin Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) (Fin.last _)))⁻¹ ^ j *
        ((Gf Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) : ℝ) : ℂ)⁻¹ ^ c)) :
    TL.Lifts Pa Bs 0 κ a := by
  refine Formalism.FourierDecayAlt.P.lift_zero_order Wp Wq Pa Bs κ i j c Pol (fun _ => 1) a hP (fibBound_one Bs) ?_ ?_
  · intro p hp g _ J
    simp only [_root_.smul_apply, one_apply_eq_self]
    rw [hinv p hp g, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx
    rw [hrad x hx Φ]
    simp

end fns

section acts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  (X : Q.ActualOps k r z z' π π') (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r)

theorem act_c (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.c l).1 (x.1 l) := by
  intro Φ
  rw [hL.2.2.1 l]
  show (X.op l 1 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_ci (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.ci l).1 (x.1 l)⁻¹ := by
  intro Φ
  rw [hL.2.2.2.1 l]
  show (X.op l 2 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_cb (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.cb l).1 (star (x.1 l)) := by
  intro Φ
  rw [hL.2.2.2.2.1 l]
  show (X.op l 4 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_cbi (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.cbi l).1 (star (x.1 l))⁻¹ := by
  intro Φ
  rw [hL.2.2.2.2.2.1 l]
  show (X.op l 5 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_fn (x : (Fin r → ℂ) × Q.Mx k r) (hx : x ∈ Q.DomR k r z z') (j : Fin 6) :
    MulAt x (X.fn j) (Q.fnVal k r z z' j x.2) := fun Φ => X.fn_apply j Φ x hx

end acts

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.TLB
open scoped ComplexConjugate

theorem lift_of_functions : TL.LiftFns := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X L hL
  have hcell := big_cell_values Pa.k Pa.r Wp Wq Bs
  have hpd1 : U.IsPolyDeg 0 (fun _ : B.Mat Pa.k Pa.r => (1 : ℂ)) := ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) := fun x =>
    mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (∏ a, star (x.1 a)) := fun x =>
    mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹) := fun x =>
    mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have inv_last : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) (Fin.last _) =
      Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _) := fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _
  have inv_r : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) ⟨Pa.r, by omega⟩ =
      Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩ := fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine liftScalar Pa Bs 0 0 0 0 (fun _ => 1) 1 hpd1 (fun _ _ _ => rfl) fun x _ => ?_
    simp only [pow_zero, mul_one]
    exact mulAt_one x
  · refine liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _)) L.D
      (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) inv_last fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.2.1]
    exact mulAt_mul (hDr x) (hz x hx)
  · refine liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _))) L.Db
      (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) (fun p hp g => by rw [inv_last p hp g])
      fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.2.1, star_mul', star_prod]
    exact mulAt_mul (hDrb x) (hzb x hx)
  · refine liftScalar Pa Bs Pa.r 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩) L.Dr
      (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) inv_r fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.1]
    exact hDr x
  · refine liftScalar Pa Bs Pa.r 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩)) L.Drb
      (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) (fun p hp g => by rw [inv_r p hp g])
      fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.1, star_prod]
    exact hDrb x
  · refine liftScalar Pa Bs 0 1 0 0 (fun _ => 1) L.Di hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.1, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  · refine liftScalar Pa Bs 0 0 1 0 (fun _ => 1) L.Dbi hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.1, star_mul', star_prod, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  · refine liftScalar Pa Bs 0 0 0 1 (fun _ => 1) (TL.gI L) hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv, ← Finset.prod_inv_distrib,
      map_prod, ← Finset.prod_inv_distrib]
    exact mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def JAAop : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (u : ℂ), KB.CptCoef Bs F → ∀ g ∈ JF.Om k r Bs.z Bs.z',
    B.JF Bs (C3.AAop k r r le_rfl u F) g = C3.AAop k r r le_rfl u (B.JF Bs F) g

def AACell : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (u : ℂ) (c : Fin r → ℂ)
    (g : B.Mat k r), g ∈ Q.Glev k r (Fin.last r) →
    C3.AAop k r r le_rfl u f (Q.wCell k r (Fin.last r) c * g) =
      (∏ a, c a) • qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) u f
        (Q.wCell k r (Fin.last r) c * g)

def MinorCell : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℂ), KB.CptCoef Bs F → ∀ x ∈ Q.DomR k r Bs.z Bs.z',
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) (B.JF Bs F)) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2

def RadSideA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps k r z z' π π')
    (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r) (y : ℂ), Q.IsActualLevel X L →
    ∀ (Ψ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      (((L.Ar y).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.crd (Q.vAB r y r).1 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def AACpt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℝ),
    KB.CptCoef Bs F → KB.CptCoef Bs (aaTop Bs y F)

def RadAATopOfParts : Prop := JAAop → AACell → MinorCell → RadSideA → AACpt → RadAATop

end Formalism.FourierDecayAlt.P.PBN
end
end

