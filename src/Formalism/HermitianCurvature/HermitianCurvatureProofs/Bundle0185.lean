module

public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.Bundle0007

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftZeroOrder
section
namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.TLB
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lift_zero_order : TL.LiftZero := by
  intro Wp Wq _ _ _ _ _ _ P Bs κ i j c Pol E a
  intro cf hPol hE hcomm ha
  obtain ⟨q, hqdeg, hq⟩ := id hPol
  let fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq := fun _ => E
  let t : MinorPolynomials.CT P.k P.r 1 :=
    ⟨q, fun l => if l = Fin.last (P.r + 1) then i else 0,
      fun l => if l = Fin.last (P.r + 1) then j else 0, c, [((0 : Fin 1), [])]⟩
  let T0 : B.DTerm P.k P.r Wp Wq :=
    { coef := MinorPolynomials.cv Bs fib t
      coefAdj := fun g => HilbertSchmidtVectorization.adjH (MinorPolynomials.cv Bs fib t g)
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun g A J => HilbertSchmidtVectorization.adjH_spec (MinorPolynomials.cv Bs fib t g) A J }
  have hcoef : ∀ g, T0.coef g = cf g := by
    intro g
    simp only [T0, MinorPolynomials.cv, MinorPolynomials.cvs, C6.Epart, C6.monoM, t, fib, cf]
    rw [Finset.prod_eq_single (Fin.last (P.r + 1)) (fun l _ hl => by simp [hl])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, B.Rw, List.foldr_nil]
    rw [hq g]
    simp only [PI.UnitaryGroupMassFormula.UsCompose.vars]
    congr 1
    ring

  have hfib : ∀ j : Fin 1, C6.FibBound Bs (fib j) := fun _ => hE
  have hgood : MinorPolynomials.Good (∅ : Finset (Fin (P.r + 2))) (t, ([] : List (B.Mat P.k P.r))) := by
    refine ⟨fun l hl => ?_, by simp [t], by simp⟩
    right
    by_contra h
    simp [t, h] at hl
  have hadj : ∀ {S : Set (B.Mat P.k P.r)} {f : B.Mat P.k P.r → C6.EndH Wp Wq},
      B.CkOn ⊤ S f → B.CkOn ⊤ S (fun x => HilbertSchmidtVectorization.adjH (f x)) := by
    intro S f hf g0 hg0
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hf g0 hg0
    refine ⟨U, fun x => HilbertSchmidtVectorization.adjR (f' x), hU, hgU, (HilbertSchmidtVectorization.adjR (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn hf', ?_⟩
    intro g hg hgv
    show HilbertSchmidtVectorization.adjH (f g) = HilbertSchmidtVectorization.adjH (f' g)
    rw [heq g hg hgv]
  have hsmooth : B.SmoothCoef (C6.domL Bs ∅) [T0] := by
    intro T hT
    rw [List.mem_singleton] at hT
    subst hT
    exact ⟨MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood,
      hadj (MinorPolynomials.ckOn_cv Bs fib (fun j => (hfib j).1) hgood)⟩
  have hop : ∀ (F : B.Mat P.k P.r → Wq →L[ℂ] Wp) g, B.opApply [T0] F g = cf g (F g) := by
    intro F g
    simp only [B.opApply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hcoef]
    rfl
  have hord : B.opOrder [T0] = 0 := by
    rfl
  have hcomD : B.Commutes Bs (C6.domL Bs ∅) [T0] := by
    intro p hp f _ g hg
    rw [hop]
    simp only [B.rho]
    rw [hop]
    exact hcomm p hp g hg (f (B.sgs p g))
  have hDD : C6.InDDPlus Bs fib ∅ 0 κ [T0] := by
    refine ⟨hsmooth, hcomD, fun T hT => ?_⟩
    rw [List.mem_singleton] at hT
    subst hT
    refine ⟨Pol, t.a, t.b, c, [((0 : Fin 1), [])], hPol, fun l _ hl => by simp [t, hl], ?_, by simp, ?_⟩
    · exact le_rfl
    · intro g _
      simp only [T0, MinorPolynomials.cv, MinorPolynomials.cvs, t]
      rw [hq g]
      rfl
  refine ⟨1, fib, [T0], hfib, hDD, ?_⟩
  intro F hF Φ hΦ x hx
  rw [ha Φ x hx, hΦ x hx]
  obtain ⟨ε, _, hnice⟩ := TLB.nice_of_cpt hF
  have hcomO : B.Commutes Bs (JF.Om P.k P.r Bs.z Bs.z') [T0] := by
    intro p hp f hf g hg
    exact hcomD p hp f hf g ⟨hg.1, hg.2.2, by simp⟩
  have hJ := orbital_commutes_on_open_set P.k P.r Wp Wq Bs
    (12 * ((P.r : ℝ) + 1) ^ 2 * (((0 : ℕ) : ℝ) + (P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1)) 0 F [T0]
    (JF.Om P.k P.r Bs.z Bs.z') subset_rfl hord.le (OrbitalIntegralIdentities.thrW_of P.k P.r 0 _ le_rfl) (hnice.2.1 _ 0) hcomO
    _ (TLB.wCell_om Bs hx)
  rw [hop] at hJ
  simp only [Q.resG, map_smul]
  rw [hJ]

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeSubStates
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_wsum {ι : Type} [Fintype ι] (Y : Finset α) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (V : ι → α → H) :
    TB.PSDOn Y (fun P Q => ∑ i, (d i : ℂ) * gramH (V i) P Q) := by
  have h := loe_sum (Finset.univ : Finset ι) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun i P Q => (d i : ℂ) * gramH (V i) P Q) fun i _ => by
      have := loe_smul (d i) (hd i) (loe_zero_of_psd (psd_gramH Y (V i)))
      refine loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem loe_sub_states {ι ι' : Type} [Fintype ι] [Fintype ι'] (Y : Finset α) (g : ι → ι') (hg : Function.Injective g)
    (K : ι' → α → α → ℂ) (hK : ∀ j, TB.PSDOn Y (K j)) :
    Loe Y (fun x y => ∑ i, K (g i) x y) (fun x y => ∑ j, K j x y) := by
  have e : ∀ x y, ∑ j, K j x y = ∑ j ∈ Finset.univ.image g, K j x y +
      ∑ j ∈ Finset.univ \ Finset.univ.image g, K j x y := by
    intro x y
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have e2 : ∀ x y, ∑ j ∈ Finset.univ.image g, K j x y = ∑ i, K (g i) x y := by
    intro x y
    rw [Finset.sum_image fun i _ i' _ h => hg h]
  have h1 := loe_sum (Finset.univ \ Finset.univ.image g) (Y := Y) (A := fun _ _ _ => (0 : ℂ)) (B := K)
    fun j _ => loe_zero_of_psd (hK j)
  have h2 := loe_add (loe_refl Y (fun x y => ∑ i, K (g i) x y)) h1
  refine loe_congr (fun x _ y _ => by simp) (fun x _ y _ => ?_) h2
  rw [e, e2]

theorem top_kernel {Ea R N : Type} {Ew : N → Type} [Fintype Ea] [∀ n, Fintype (Ew n)] [Fintype R] [Fintype N]
    (Y : Finset α) (g : ∀ n, Ea → Ew n) (hg : ∀ n, Function.Injective (g n)) (Va : Ea → R → α → H)
    (Vn : ∀ n, Ew n → R → α → H) (da : Ea → R → ℝ) (dn : ∀ n, Ew n → R → ℝ) (hda : ∀ e ρ, 0 ≤ da e ρ)
    (hdn : ∀ n e ρ, 0 ≤ dn n e ρ)
    (lam : N → ℝ) (Pn : N → ℝ) (hPn : ∀ n, 0 < Pn n) (c : ℂ) (C0 : ℝ) (K : ℕ) (hC0 : 0 ≤ C0)
    (hdeg : ∀ P ∈ Y, ∀ e ρ, Va e ρ P = c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P)
    (hwt : ∀ n e ρ, da e ρ * Pn n ≤ C0 ^ K * dn n (g n e) ρ) :
    Loe Y (fun P Q => ∑ e, ∑ ρ, (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => ((‖c‖ ^ 2 * (∑ n, |lam n|) * C0 ^ K : ℝ) : ℂ) *
        ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) := by
  set Λ : ℝ := ∑ n, |lam n| with hΛ

  have s1 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * (((∑ n, ‖(lam n : ℂ)‖ : ℝ) : ℂ) *
        ∑ n, ((‖(lam n : ℂ)‖ : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ
    have hc := loe_convex Y (fun n => (lam n : ℂ)) (fun n P => Vn n (g n e) ρ P)
    have hc2 := loe_smul (da e ρ * ‖c‖ ^ 2) (mul_nonneg (hda e ρ) (sq_nonneg _)) hc
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => by push_cast; ring) hc2
    have : gramH (Va e ρ) P Q = gramH (fun P => c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P) P Q := by
      unfold gramH; rw [hdeg P hP e ρ, hdeg Q hQ e ρ]
    rw [this, gramH_smul]
    push_cast; ring
  have hnorm : ∀ n, ‖(lam n : ℂ)‖ = |lam n| := fun n => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at s1

  have s2 : ∀ e ρ n, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ n
    have h := loe_scale (psd_gramH Y (Vn n (g n e) ρ)) (r := da e ρ) (r' := C0 ^ K / Pn n * dn n (g n e) ρ) (by
      have := hwt n e ρ
      rw [sub_nonneg, div_mul_eq_mul_div, le_div_iff₀ (hPn n)]
      linarith)
    refine loe_congr (fun _ _ _ _ => rfl) (fun P _ Q _ => by push_cast; ring) h

  have s3 : ∀ n, Loe Y (fun P Q => ∑ e, ∑ ρ, (dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) :=
    fun n => loe_sub_states Y (g n) (hg n) (fun e' P Q => ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q)
      fun e' => psd_wsum Y (fun ρ => dn n e' ρ) (fun ρ => hdn n e' ρ) (fun ρ => Vn n e' ρ)

  have c1 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => s1 e ρ
  refine loe_trans c1 ?_

  have c2 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * ((Λ : ℂ) *
        ∑ n, ((|lam n| : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q))
      (fun P Q => ((‖c‖ ^ 2 * Λ : ℝ) : ℂ) * ∑ n, ((|lam n| : ℝ) : ℂ) *
        (((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q))) := by
    intro e ρ
    have h := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
      (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n|) (abs_nonneg _) (s2 e ρ n))
    refine loe_congr (fun P _ Q _ => ?_) (fun _ _ _ _ => rfl) h
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  have c3 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => c2 e ρ
  refine loe_trans (loe_congr (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) c3) ?_
  have c4 := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
    (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n| * (C0 ^ K / Pn n))
      (mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg hC0 _) (hPn n).le)) (s3 n))
  refine loe_congr (fun P _ Q _ => ?_) (fun P _ Q _ => ?_) c4
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring

end abstract

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem om_cast {a b : ℕ} (h : a = b) (v v' : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ JF.Om k a v v') :
    D.castM h g ∈ JF.Om k b (D.castV h v) (D.castV h v') := by
  subst h; rwa [Dx2.MN.castM_rfl, Dx2.Tower.castV_rfl, Dx2.Tower.castV_rfl]

theorem lowV_lift (ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) : U.lowV k 1 ρ (liftVec k 1 ρ v) = v := by
  funext i
  simp only [U.lowV, liftVec]
  rw [dite_eq_left (by omega)]
  congr 1; ext; simp

theorem mcOm : MCOm := by
  intro k ρ z0 z0' hz0 hz0' c hc γ hγ hγO
  apply om_cast
  set Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c with hZd
  have hZdet : Z.det = c := by rw [Matrix.det_unique]; rfl
  have hz := Qx4.lift_inWb hz0
  have hz' := Qx4.lift_inWb hz0'
  have hZ : Zhat k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
      Matrix.reindex (Ux3.eC 1 ρ) (Ux3.eC 1 ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ z0 z0' γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 _ _ hz hz', Formalism.QuantumDeterminants.Zhat_eq, lowV_lift, lowV_lift]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k 1 ρ).1 Z γ (by rw [hZdet]; exact hc) hγ, ?_, ?_⟩
  · intro l hl
    obtain ⟨lv, hlv⟩ := l
    rcases Nat.eq_zero_or_pos lv with h0 | hpos
    · subst h0
      unfold Dmin
      rw [Matrix.det_isEmpty]; exact one_ne_zero
    · obtain ⟨l', rfl⟩ : ∃ l', lv = 1 + l' := ⟨lv - 1, by omega⟩
      have hl' : l' ≤ ρ := by simp only at hl; omega
      unfold Dmin
      rw [hZ, Ux3.minor_blocks Z _ l' (by omega) (by omega), hZdet]
      refine mul_ne_zero hc ?_
      exact hγO.1 ⟨l', by omega⟩ hl'
  · have h1 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) (Fin.last _) =
        Z.det * Dmin k ρ z0 z0' γ (Fin.last _) := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ (ρ + 1) le_rfl _
    have h0 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) ⟨1 + ρ, by omega⟩ =
        Z.det * Dmin k ρ z0 z0' γ ⟨ρ, by omega⟩ := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ ρ (by omega) _
    have ht : Tz k (1 + ρ) (liftVec k 1 ρ z0) = Tz k ρ z0 := by rw [Ux3.tz_low _ hz, lowV_lift]
    have ht' : Tz k (1 + ρ) (liftVec k 1 ρ z0') = Tz k ρ z0' := by rw [Ux3.tz_low _ hz', lowV_lift]
    have hG : Gf k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
        Complex.normSq c * Gf k ρ z0 z0' γ := by
      unfold Gf
      rw [h1, h0, ht, ht', hZdet, Complex.normSq_mul, Complex.normSq_mul]
      ring
    rw [hG]
    exact mul_pos (Complex.normSq_pos.2 hc) hγO.2

theorem jfStep : JFStep := jfStep_of mcOm

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section BS

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def BSR (R : ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) : Prop := ∀ g ∈ GV k r, F g ≠ 0 → gN g ≤ R

theorem smoothLev_of_ckOn {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F) (D : Set (Mx k r)) :
    SmoothLev k r 0 D F := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hF g₀ hg₀.1.1
  exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩

theorem mem_level_zero_of_mem_group {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem tL_zero_fn (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) {g : Mat k r} (hg : g ∈ GV k r) :
    tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
  have h0 : SmoothLev k r 0 Set.univ (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) :=
    fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have := (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' 0 Set.univ Y a b _ _ 1 isOpen_univ h0 h0 g
    ⟨mem_level_zero_of_mem_group hg, trivial⟩).1
  simp only [one_smul, add_zero] at this
  have h2 : tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
      tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
      tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g := this.symm
  simpa using h2

theorem bsr_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ⊤ (GV k r) F) {R : ℝ} (hR : BSR R F) : BSR R (tL k r z z' 0 Y a b F) := by
  intro g hg hne
  by_contra hgt
  push Not at hgt
  let D : Set (Mx k r) := {h | R < gN h}
  have hD : IsOpen D := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
  have h0 : SmoothLev k r 0 D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) :=
    fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hloc := (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' 0 D Y a b F _ 1 hD
    (smoothLev_of_ckOn hF D) h0 g ⟨mem_level_zero_of_mem_group hg, hgt⟩).2 (fun x hx => by
      by_contra hx0
      have := hR x hx.1.1 hx0
      exact absurd hx.2 (not_lt.2 this))
  exact hne (hloc.trans (tL_zero_fn z z' Y a b hg))

end BS

section Wcell

variable {k r : ℕ}

theorem prod_w1_mem_unitary_Hpk (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (l : List (Fin r)) :
    (l.map fun a => w1 k r a (c a)).prod ∈ UH (Hpk k r) := by
  induction l with
  | nil =>
    show Matrix.conjTranspose (1 : Mx k r) * Hpk k r * 1 = Hpk k r
    simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_unitary a (hc a)) ih

theorem wCell_mul_GV {i : Fin (r + 1)} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r)) : wCell k r i c * g ∈ GV k r :=
  Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (prod_w1_mem_unitary_Hpk c hc _) hg.1

end Wcell

section Pics

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pic_of_cptClause (D : RealPlaceData k r Wp Wq) {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (K0 : Submodule ℂ (RadSp k r D.z D.z' π π'))
    (hJc : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (JF D F) x.1 x.2)
    {F : Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hε : 0 < ε) (hF : JC.NiceCoef D ε F) {R : ℝ} (hR : BSR R F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (JF D F) x.1 x.2 := by
  classical
  let Ft : Mat k r → (Wq →L[ℂ] Wp) := Set.indicator (GV k r) F
  have hE : ∀ g ∈ GV k r, F g = Ft g := fun g hg => (Set.indicator_of_mem hg F).symm
  have hFt : JC.NiceCoef D ε Ft := Formalism.FourierDecayAlt.P.JCx2.mn_nice_congr hE hF
  have hcs : HasCompactSupport Ft := by
    refine HasCompactSupport.intro (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) fun g hg => ?_
    by_cases hgG : g ∈ GV k r
    · show Set.indicator (GV k r) F g = 0
      rw [Set.indicator_of_mem hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · exact Set.indicator_of_notMem hgG F
  obtain ⟨Φ, hΦ, hpic⟩ := hJc Ft ε hε hFt.2.1 hcs hFt.2.2
  refine ⟨Φ, hΦ, fun x hx => (hpic x hx).trans ?_⟩
  unfold resG
  have hmem := wCell_mul_GV (k := k) (i := Fin.last r) (fun a => hx.1 a) hx.2.1
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := Ft) (a := 1) (fun g hg => by rw [hE g hg, one_smul]) hmem, one_smul]

end Pics

section Closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bsr_sum {k r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat k r → (Wq →L[ℂ] Wp)) {R : ℝ}
    (h : ∀ i ∈ s, BSR R (f i)) : BSR R (fun g => ∑ i ∈ s, f i g) := by
  intro g hg hne
  obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h i hi g hg hne'

theorem actOp_nice_bsr (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1))
    (w : List C.Letter) (F : Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) {ε R : ℝ}
    (hF : ∀ a, JC.NiceCoef (T.bs j) ε (F a)) (hR : ∀ a, BSR R (F a)) (a : Ix (Fin w.length)) :
    JC.NiceCoef (T.bs j) ε (D.actOp (D.RRlev T s j w) F a) ∧ BSR R (D.actOp (D.RRlev T s j w) F a) := by
  let S : D.Op (Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) → Prop := fun Θ => ∀ G, JC.NiceCoef (T.bs j) ε G → BSR R G →
    JC.NiceCoef (T.bs j) ε (D.ap Θ G) ∧ BSR R (D.ap Θ G)
  have hcl : Formalism.FourierDecayAlt.P.JCx2.mnClosed S :=
    { zero := fun G _ _ => ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero, fun g _ h => absurd rfl h⟩
      one := fun G hG hR => ⟨hG, hR⟩
      add := fun a b ha hb G hG hR => by
        obtain ⟨h1, h2⟩ := ha G hG hR
        obtain ⟨h3, h4⟩ := hb G hG hR
        refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_add h1 h3, fun g hg hne => ?_⟩
        by_cases h : D.ap a G g = 0
        · have : D.ap b G g ≠ 0 := by
            intro h'; apply hne; show D.ap a G g + D.ap b G g = 0; rw [h, h', add_zero]
          exact h4 g hg this
        · exact h2 g hg h
      mul := fun a b ha hb G hG hR => by
        obtain ⟨h1, h2⟩ := hb G hG hR
        exact ha _ h1 h2
      cop := fun c G hG hR => ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul c hG, fun g hg hne => hR g hg (by
        intro h0; apply hne; show c • G g = 0; rw [h0, smul_zero])⟩ }
  have hQQ : ∀ Y p q, S (D.QQlev T s j Y p q) := fun Y p q G hG hRG => by
    refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul s (Formalism.FourierDecayAlt.P.JCx2.mn_tL_nice (T.bs j) ε G Y p q hG), fun g hg hne => ?_⟩
    refine bsr_tL (T.bs j).z (T.bs j).z' Y p q hG.1 hRG g hg ?_
    intro h0; apply hne; show s • tL P0.k (P0.r - j) (T.bs j).z (T.bs j).z' 0 Y p q G g = 0; rw [h0, smul_zero]
  have hR' := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure hcl (D.QQlev T s j) hQQ (D.positionted w)
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' _ _ fun b _ => (hR' a b (F b) (hF b) (hR b)).1, ?_⟩
  intro g hg hne
  have e : D.actOp (D.RRlev T s j w) F a g = ∑ b, D.ap (D.RRlev T s j w a b) (F b) g := by
    simp only [D.actOp, Finset.sum_apply]
  exact bsr_sum Finset.univ (fun b => D.ap (D.RRlev T s j w a b) (F b))
    (fun b _ => (hR' a b (F b) (hF b) (hR b)).2) g hg (fun h0 => hne (e.trans h0))

theorem cpt_nice_bsr {k r : ℕ} {Bs : RealPlaceData k r Wp Wq} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    (∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F) ∧ ∃ R, BSR R F :=
  ⟨Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF, hF.2.1⟩

end Closure

end

end Formalism.FourierDecayAlt.P.PBF
end

