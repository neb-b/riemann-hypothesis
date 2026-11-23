module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.RegLine
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖eval z (map (Int.castRingHom ℂ) t)‖ / E.h z

theorem logNorm_eq_log_secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm E t z = Real.log (secNorm E t z) := rfl

theorem secNorm_smul {E : HermLine ι} {t : MRing ι} {a : K → ℕ} (hE : ∀ k, E.a k = a k)
    (ht : IsMultiHomog t a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    secNorm E t (fun p => c p.1 * z p) = secNorm E t z := by
  have he := eval_bsmul_of_isMultiHomog ht c z
  have hh : E.h (bsmul c z) = (∏ k, ‖c k‖ ^ E.a k) * E.h z := E.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ E.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ E.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hE k, zpow_natCast]
  change ‖eval (bsmul c z) (map (Int.castRingHom ℂ) t)‖ / E.h (bsmul c z) = _
  rw [he, hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
  rfl

def regLine (E : HermLine ι) (t : MRing ι) (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a)
    (ε : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun z => -(Real.log (secNorm E t z ^ 2 + ε) / 2)) (by
    intro c z hc
    obtain ⟨a, hE, hta⟩ := ht
    simp only [secNorm_smul hE hta hc z])

variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}

theorem regLine_a : (regLine E t ht ε).a = 0 := rfl

theorem regLine_h (z : (Σ k, ι k) → ℂ) :
    (regLine E t ht ε).h z = Real.exp (Real.log (secNorm E t z ^ 2 + ε) / 2) := by
  simp [regLine, HermLine.ofWeight]

theorem log_regLine_h (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by
  rw [regLine_h, Real.log_exp]

theorem contDiff_eval_map (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by
  induction t using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ (fun _ => ℂ) v)

theorem isSmoothHerm_regLine (hE : IsSmoothHerm E) (hε : 0 < ε) : IsSmoothHerm (regLine E t ht ε) := by
  unfold IsSmoothHerm
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_eval_map t)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2 / E.h z ^ 2 + ε)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hn.contDiffOn.div (hE.pow 2) fun z hz => pow_ne_zero _ (E.pos z hz).ne').add contDiffOn_const
  have hl := (hq.log fun z hz => (add_pos_of_nonneg_of_pos
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) hε).ne').div_const 2
  refine (Real.contDiff_exp.comp_contDiffOn hl).congr fun z _ => ?_
  rw [regLine_h, secNorm, div_pow]
  rfl

theorem logNorm_le_log_regLine_h (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by
  rw [log_regLine_h, logNorm_eq_log_secNorm]
  have hpos : 0 < secNorm E t z := div_pos (norm_pos_iff.mpr ht0) (E.pos z hz)
  have h2 : Real.log (secNorm E t z) = Real.log (secNorm E t z ^ 2) / 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) (by norm_num)

end Objects

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    IsLocalRing (locRing P W) ∧
      ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
        (y : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
        (IsUnit y ↔ u ∉ W)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingPow.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ P))
    (u v : MRing ι) (b : K → ℕ) (y : FractionRing (MRing ι ⧸ P)),
    P.IsPrime → IsMultiHomogIdeal P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsMultiHomog t a → t ∉ W → x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    IsMultiHomog u b → IsMultiHomog v b → u ∈ W → v ∉ W → y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
    ∃ n : ℕ, ∃ z ∈ locRing P W, y ^ n = x * z

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAddFirst
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsAddFirst.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (M N E : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm E → IsSectionOn Q E t →
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (logNorm E t) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (logNorm E t) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (logNorm E t)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRatioAlgDep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RatioAlgDep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d : ℕ)
    (c : ∀ k, ι k) (p : Fin d → Σ k, ι k),
    IsArithVar Q d →
    ∃ f : MvPolynomial (Fin d) ℤ, f ≠ 0 ∧
      ∀ z : (Σ k, ι k) → ℂ, (∀ g ∈ Q, eval z (map (Int.castRingHom ℂ) g) = 0) →
        (∀ k, z ⟨k, c k⟩ ≠ 0) →
          eval (fun j => z (p j) / z ⟨(p j).1, c (p j).1⟩) (map (Int.castRingHom ℂ) f) = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StSheetHessPSD
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

def SheetHessPSD.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (M : HermLine ι) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
    IsSmoothHerm M → IsSemiPosHerm M → IsSheet P Ψ y w γ →
    (cxHessian (fun y' => Real.log (M.h (γ y'))) y).PosSemidef

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemFunFieldSpecZ
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : funField P),
    IsArithVar P 1 → b ≠ 0 → (∀ W, IsClosedPt W → P ≤ W → (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W b) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W b)) =
        ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ b‖

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.XcNotMemOfIsRelevant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (x : funField P) (t : Ideal (MRing ι) → MRing ι)
    (yf yg : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) →
    (∀ W ∈ divSupp P f ∪ divSupp P g, IsMultiHomog (t W) a ∧ t W ∉ W ∧
      yf W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ∧
      yg W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
    ∑ᶠ W ∈ divSupp P f, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) -
        ∑ᶠ W ∈ divSupp P g, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) =
      ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ x‖

end

end GroundTheory.Heights₂.Heights.Inter
end

