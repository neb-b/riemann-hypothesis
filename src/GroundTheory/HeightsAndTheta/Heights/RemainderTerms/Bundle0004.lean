module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics

open MvPolynomial Finset

theorem card_monotone_equiv_congr {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {n n' : ℕ} (h : n = n') :
    Nat.card {T : α ≃ Fin n // Monotone T} = Nat.card {T : β ≃ Fin n' // Monotone T} := by
  subst h
  exact Nat.card_congr
    { toFun := fun T => ⟨e.symm.toEquiv.trans T.1, fun a b hab => T.2 (e.symm.monotone hab)⟩
      invFun := fun T => ⟨e.toEquiv.trans T.1, fun a b hab => T.2 (e.monotone hab)⟩
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp }

theorem mem_youngCells {m : ℕ} (lam : Fin m → ℕ) (x : Fin m × ℕ) :
    x ∈ RestTerms.youngCells lam ↔ x.2 < lam x.1 := by
  unfold RestTerms.youngCells
  simp only [mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨lt_of_lt_of_le h (Finset.single_le_sum (fun i _ => Nat.zero_le (lam i))
      (mem_univ x.1)), h⟩

theorem mem_shapeCells {r : ℕ} (la : Fin r → ℕ) (x : ℕ × ℕ) :
    x ∈ IndefiniteRowSideFullHecke.RestTerms.shapeCells la ↔ ∃ h : x.1 < r, x.2 < la ⟨x.1, h⟩ := by
  unfold IndefiniteRowSideFullHecke.RestTerms.shapeCells
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_range]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a.2, hb⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x.1, h⟩, x.2, hx, rfl⟩

def cellIso {r : ℕ} (la : Fin r → ℕ) :
    RestTerms.youngCells la ≃o IndefiniteRowSideFullHecke.RestTerms.shapeCells la where
  toFun p := ⟨((p.1.1 : ℕ), p.1.2),
    (mem_shapeCells la _).2 ⟨p.1.1.2, (mem_youngCells la _).1 p.2⟩⟩
  invFun q := ⟨(⟨q.1.1, ((mem_shapeCells la _).1 q.2).1⟩, q.1.2),
    (mem_youngCells la _).2 ((mem_shapeCells la _).1 q.2).2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨c, d⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]

theorem numStandardTable_eq_card_monotone {m : ℕ} (lam : Fin m → ℕ) :
    RestTerms.numStandardTable lam =
      Nat.card {T : RestTerms.youngCells lam ≃ Fin (RestTerms.youngCells lam).card //
        Monotone T} := by
  unfold RestTerms.numStandardTable
  refine Nat.card_congr (Equiv.subtypeEquivRight fun T => ?_)
  constructor
  · intro h p q hpq
    have h' := Prod.le_def.1 (Subtype.coe_le_coe.2 hpq)
    exact h p q h'.1 h'.2
  · intro h p q h1 h2
    exact h (Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h1, h2⟩))

theorem numSYT_eq {r : ℕ} (la : Fin r → ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT la = RestTerms.numStandardTable la := by
  rw [numStandardTable_eq_card_monotone]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  refine (card_monotone_equiv_congr (cellIso la) ?_).symm
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (cellIso la).toEquiv

theorem shapeCells_hookShape (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.shapeCells (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      IndefiniteRowSideFullHecke.RestTerms.shapeCells (RestTerms.hookShape r k b) := by
  ext x
  rw [mem_shapeCells, mem_shapeCells]
  simp only [RestTerms.hookShape, IndefiniteRowSideFullHecke.RestTerms.hookShape]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨by omega, ?_⟩
    split_ifs at hx ⊢ <;> omega
  · rintro ⟨h, hx⟩
    have h' : x.1 < b + 1 := by
      by_contra hc
      split_ifs at hx <;> omega
    refine ⟨h', ?_⟩
    split_ifs at hx ⊢ <;> omega

theorem numSYT_hookShape (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      RestTerms.numStandardTable (RestTerms.hookShape r k b) := by
  rw [← numSYT_eq]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  rw [shapeCells_hookShape r k b hb]

end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTopGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAboveTopGeneral.proof (h1 : CoinvAboveTop.Statement) :
    CoinvAboveTopGeneral.Statement := by
  intro K _ _ β ι _ _ _ _ d H hH hd
  set eβ := Fintype.equivFin β
  set eι := Fintype.equivFin ι
  set ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) := eβ.prodCongr eι with hψ
  obtain ⟨Q', hQ'h, hQ'⟩ := h1 K (Fintype.card β) (Fintype.card ι) d (rename ψ H)
    hH.rename_isHomogeneous hd
  refine ⟨fun m b => rename ψ.symm (Q' m (eβ b)),
    fun m b => (hQ'h m (eβ b)).rename_isHomogeneous, ?_⟩
  have hback : H = rename ψ.symm (rename ψ H) := by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hback, hQ', map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Equiv.sum_comp eβ.symm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [map_mul]
  simp only [Equiv.apply_symm_apply]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [bps, map_sum, ← Equiv.sum_comp eι.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hψ]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAtTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by
  intro K _ _ f n H hH
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, -, hQ⟩ := h2 K f n (H - v) hJ (coinvTop f n)
  obtain ⟨-, c, hc⟩ := h3 K f n v hv
  refine ⟨c, ?_⟩
  have hcomp : H - C c * monomial (staircase f n) 1 =
      homogeneousComponent (coinvTop f n) (H - v) := by
    rw [map_sub, homogeneousComponent_eq_self hH, hc]
  rw [hcomp, hQ]
  refine Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_
  rw [Finset.mem_Icc] at hm
  exact Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem Coinv.bps_isHomogeneous (K : Type) [Field K] (f n m : ℕ) (b : Fin f) :
    (bps K f n m b).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem CoinvIdealComponent.proof (h1 : CoinvIdealRepresentation.Statement)
    (h2 : HomogeneousComponentMul.Statement) : CoinvIdealComponent.Statement := by
  intro K _ f n J hJ d
  obtain ⟨a, rfl⟩ := h1 K f n J hJ
  refine ⟨fun m b => if m ≤ d then homogeneousComponent (d - m) (a m b) else 0, ?_, ?_⟩
  · intro m b
    dsimp only
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h2 (Fin f × Fin n) K (bps K f n m b) (a m b) m d (bps_isHomogeneous K f n m b)]
    by_cases hmd : m ≤ d <;> simp [hmd]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section


open Coinv in
theorem CoinvIdealRepresentation.proof : CoinvIdealRepresentation.Statement := by
  intro K _ f n J hJ
  induction hJ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m₀, b₀, h1, h2, rfl⟩ := hx
    refine ⟨fun m b => if m = m₀ ∧ b = b₀ then 1 else 0, ?_⟩
    have hm₀ : m₀ ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
    symm
    rw [Finset.sum_eq_single m₀]
    · rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ b₀) h
    · intro m _ hm
      apply Finset.sum_eq_zero
      intro b _
      simp [hm]
    · intro h
      exact absurd hm₀ h
  | zero =>
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    refine ⟨a + a', ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨fun m b => r * a m b, ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvMonomialReduction.proof (h1 : CoinvStepReduction.Statement) :
    CoinvMonomialReduction.Statement := by
  intro K _ _ f n e
  classical
  let r : Fin f × Fin n → Fin f × Fin n → Prop := fun u v => toLex u < toLex v
  have : IsStrictTotalOrder (Fin f × Fin n) r :=
    inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))
  have wf : WellFounded
      (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFounded_of_finite r wellFounded_lt
  induction e using wf.induction with
  | _ e ih =>
  by_cases hu : IsUnderStaircase e
  · exact ⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩
  · simp only [IsUnderStaircase, not_forall, not_le] at hu
    obtain ⟨⟨b, k⟩, hbk⟩ := hu
    obtain ⟨T, c, hT, hmem⟩ := h1 K f n b k e (by simpa using hbk)
    have hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e := by
      intro e' he'
      refine Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩
      exact Prod.Lex.toLex_lt_toLex.mp hj
    choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')
    refine ⟨∑ e' ∈ T, c e' • w e',
      Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩
    have hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' =
        (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) +
          ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e') := by
      simp only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvPolynomialReduction.proof (h1 : CoinvMonomialReduction.Statement) :
    CoinvPolynomialReduction.Statement := by
  intro K _ _ f n H
  choose v hv hvI using fun d => h1 K f n d
  refine ⟨∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hv d)
  · have e1 : H - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d := by
      rw [← H.as_sum]
    have e2 : (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        ∑ d ∈ H.support, C (AddMonoidAlgebra.coeff H d) * (monomial d (1 : K) - v d) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_sub, C_mul_monomial, mul_one, smul_eq_C_mul]
    rw [e1, e2]
    exact Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hvI d)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Coinv

noncomputable section

theorem CoinvStaircaseComponent.proof (h1 : CoinvStaircaseDegree.Statement) :
    CoinvStaircaseComponent.Statement := by
  intro K _ f n v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    obtain ⟨hle, heq⟩ := h1 f n e he
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · rw [homogeneousComponent_of_mem hhom]
      by_cases h : coinvTop f n = e.degree
      · refine ⟨1, ?_⟩
        rw [if_pos h, heq h.symm, C_1, one_mul]
      · exact ⟨0, by rw [if_neg h, C_0, zero_mul]⟩
  | zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    obtain ⟨hy1, cy, hy2⟩ := hy
    refine ⟨fun d hd => by rw [map_add (f := _), hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩
    rw [map_add (f := _), hx2, hy2, C_add, add_mul]
  | smul a x _ hx =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    refine ⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩
    rw [map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem Coinv.sum_staircase_exponents (f n : ℕ) :
    ∑ v : Fin f × Fin n, (v.2 : ℕ) = coinvTop f n := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rfl

theorem CoinvStaircaseDegree.proof : CoinvStaircaseDegree.Statement := by
  intro f n e he
  have hle : ∀ v ∈ (Finset.univ : Finset (Fin f × Fin n)), e v ≤ (v.2 : ℕ) := fun v _ => he v
  rw [Finsupp.degree_eq_sum, ← Coinv.sum_staircase_exponents f n]
  refine ⟨Finset.sum_le_sum hle, fun hEq => ?_⟩
  have hall := (Finset.sum_eq_sum_iff_of_le hle).1 hEq
  ext v
  simp [staircase, hall v (Finset.mem_univ v)]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem HomogeneousComponentMul.proof : HomogeneousComponentMul.Statement := by
  intro σ R _ p a m d hp
  have hterm : ∀ i, homogeneousComponent d (p * homogeneousComponent i a) =
      if d = m + i then p * homogeneousComponent i a else 0 := fun i =>
    homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr (hp.mul (homogeneousComponent_isHomogeneous i a)))
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]
  simp_rw [hterm]
  split_ifs with hmd
  · have hcongr : ∀ i ∈ range (a.totalDegree + 1),
        (if d = m + i then p * homogeneousComponent i a else 0) =
          if d - m = i then p * homogeneousComponent i a else 0 := by
      intro i _
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      rw [homogeneousComponent_eq_zero (d - m) a (by omega), mul_zero]
  · exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

