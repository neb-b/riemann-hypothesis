module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassCoeffsIntegralAverageChangeOfVariable
section
noncomputable section

open WeierstrassCurve
open scoped BigOperators

namespace GlobalTheory.CMModel

theorem avg_mem_of_card_unit (V : ValuationSubring ℂ) {ι : Type} [Fintype ι] (f : ι → ℂ)
    (hc : V.valuation (Fintype.card ι : ℂ) = 1) (hf : ∀ i, f i ∈ V) :
    (∑ i, f i) / Fintype.card ι ∈ V := by
  rw [div_eq_mul_inv]
  refine V.mul_mem _ _ (sum_mem (S := V) fun i _ => hf i) ?_
  rw [← V.valuation_le_one_iff, map_inv₀, hc, inv_one]

theorem intV_average (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι]
    (X Y : ι → ℂ)
    (h : IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)))
    (hc : V.valuation (Fintype.card ι : ℂ) = 1)
    (hX : ∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V)
    (hY : ∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V)
    (h2 : ∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) :
    IntV V ((⟨u, (∑ i, X i) / Fintype.card ι,
      (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι,
      (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) •
      (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact zero_ne_one hc
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hr := avg_mem_of_card_unit V _ hc hX
  have ht := avg_mem_of_card_unit V _ hc hY
  have hs := avg_mem_of_card_unit V _ hc fun i =>
    _root_.GlobalTheory.CMModel.tangentSlope_mem V a₄ a₆ r s t (X i) (Y i) u h (hX i) (hY i) (h2 i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hr hs ht
  set A := ∑ i, X i
  set B := ∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)
  set D := ∑ i, Y i
  set n : ℂ := ((Fintype.card ι : ℕ) : ℂ)
  have key : (⟨u, A / n, B / n, D / n⟩ : VariableChange ℂ) =
      (⟨1, (A - n * r) / (u : ℂ) ^ 2 / n, (B - n * s) / (u : ℂ) / n,
        (D - n * t - s * (A - n * r)) / (u : ℂ) ^ 3 / n⟩ : VariableChange ℂ) * ⟨u, r, s, t⟩ := by
    rw [VariableChange.mul_def]
    ext
    · simp
    all_goals
      simp only []
      field_simp
      ring
  rw [key, mul_smul]
  exact GlobalTheory.coeff_mem_variableChange V.toSubring h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hr hs ht rfl

end GlobalTheory.CMModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1Bound
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.divided_weight_small_block_le_neg_three_mul {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (τ : ι) :
    ∀ (k : ℕ) (hk : W.p + k < N), W.u1 τ ⟨W.p + k, hk⟩ ≤ -(3 * (N : ℤ)) := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  intro k
  induction k with
  | zero =>
    intro hk
    have h1 := hH.kc_pos
    have h2 := hH.kc_lt
    have hg := ((_root_.GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ ⟨W.p - 1, by omega⟩ ⟨W.p + 0, hk⟩ (by simp; omega)).2.1 (by simp)).2
    have he := (_root_.GlobalTheory.MeanTop.divided_entries ι N W hH hD τ ⟨W.p - 1, by omega⟩).2.1 (by simp; omega)
    have h3 := hH.h2.2
    have hN : (0 : ℤ) ≤ 24 * (N : ℤ) * W.T := by positivity
    have h4 : 0 ≤ W.u1 τ ⟨W.p - 1, by omega⟩ - W.u1 τ ⟨W.p + 0, hk⟩ - 3 * N := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    linarith
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hg := (_root_.GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ ⟨W.p + k, by omega⟩ ⟨W.p + (k + 1), hk⟩ (by simp; omega)).1 (by simp)
    have hN : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    linarith

theorem Wts.abs_u'_le {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |W.u' τ i| ≤ |W.u1 τ i| := by
  unfold Wts.u'
  split_ifs with h
  · exact le_rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
    have hlt : W.p + k < N := hk ▸ i.2
    have hi : i = ⟨W.p + k, hlt⟩ := Fin.ext hk
    have h1 := W.divided_weight_small_block_le_neg_three_mul hH hD τ k hlt
    rw [← hi] at h1
    have hN : (0 : ℤ) ≤ N := by positivity
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem divided_weight_size : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → (W.T : ℝ) * l1 W.u1 ≤ l1 W.u + (Fintype.card ι : ℝ) * N * (W.c0 + 4 * N) ∧ l1 W.u' ≤ l1 W.u1 ∧ ∀ τ i, |W.u' τ i| ≤ |W.u1 τ i| := by
  intro ι _ N W hH hD
  refine ⟨?_, ?_, fun τ i => W.abs_u'_le hH hD τ i⟩
  · have key : ∀ τ i, (W.T : ℝ) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + (W.c0 + 4 * N) := by
      intro τ i
      have h1 := (_root_.GlobalTheory.MeanTop.divided_entries ι N W hH hD τ i).1
      have h0 : (0 : ℤ) ≤ ((W.Dd : ℤ) + 1) * |W.u1 τ i| := by positivity
      have h2 : (W.T : ℤ) * |W.u1 τ i| ≤ |W.u τ i| + (W.c0 + 4 * N) := by nlinarith
      exact_mod_cast h2
    unfold l1
    calc (W.T : ℝ) * ∑ τ, ∑ i, |(W.u1 τ i : ℝ)|
        = ∑ τ, ∑ i, (W.T : ℝ) * |(W.u1 τ i : ℝ)| := by simp only [Finset.mul_sum]
      _ ≤ ∑ τ, ∑ i : Fin N, (|(W.u τ i : ℝ)| + (W.c0 + 4 * N)) :=
          Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => key τ i
      _ = _ := by
          simp only [Finset.sum_add_distrib (f := fun i => |(W.u _ i : ℝ)|), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  · unfold l1
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast W.abs_u'_le hH hD τ i

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPull

theorem weilIs_diag_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left),
    IsAbelianScheme A → P.IsLB → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    Out.WeilIs (G2 A) P n (lift u u) (lift v v) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n u v c' →
    c = c' := by
  intro S A _ _ P hA hP n T u v c c' h h'
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hw : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1) (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    have h1 : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1).IsLB := LB.isLB_linComb hL _ _
    refine (CechPic.cls_eq_iff h1 hL).1 ?_
    rw [CechPic.cls_lbPow hL, one_smul]
  have hu : u ≫ lift (𝟙 A) (𝟙 A) = lift u u := by simp
  have hv : v ≫ lift (𝟙 A) (𝟙 A) = lift v v := by simp
  rw [← hu, ← hv] at h
  have h2 := WeilIsogeny.weilIs_pull_hom globalFns_holds hA hL hP (lift (𝟙 A) (𝟙 A)) hw h
  rw [Nat.cast_one, Int.mul_one] at h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hA hL h2 h'

end GlobalTheory.DiagPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitone
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.JSW

theorem whittaker_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, ¬ Antitone l → W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i)) = 0 := by
  intro E _ _ w n ψ hψ W hWN hWK ϖ hϖ l hl

  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)

  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := l j - l i with hm
  have hlj : l j = l i + m := by omega
  have hm1 : 1 ≤ m := by omega
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy

  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

  have hu : T x ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : GlobalTheory.Whittaker.superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

  have hk : T c ∈ KGL w (n := n) := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp

  set D := Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
    (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i) with hD
  have hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => (ϖ : w.adicCompletion E) ^ l a := by
    rw [hD]
    ext p q
    simp [Matrix.diagonal_apply]
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hlj, pow_add]
      congr 1
      ring
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

end GlobalTheory.JSW
end
end

