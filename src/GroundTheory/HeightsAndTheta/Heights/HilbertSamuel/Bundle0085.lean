module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace TwoBlockModuleFinite

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem cone_X (x x' : Ix κ → Ω) (p : Σ k, FinTwoTypeFamily κ k) :
    mConeMap (pair x x') (X p : MRing (FinTwoTypeFamily κ)) = MvPolynomial.C (pair x x' p) * X p.1 :=
  aeval_X _ _

theorem cone_num (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (pair x x') (twoBlockNum l) = MvPolynomial.C (∑ j, (l j : Ω) * x' j) * X 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [twoBlockNum, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨⟨⟩, j⟩ := j
  rw [cone_X]
  simp [mConeMap, pair, mul_assoc]

theorem coneMap_firstBlock_linearForm (x x' : Ix κ → Ω) (n : Ix κ → ℤ) :
    mConeMap (pair x x') (∑ i : Ix κ, MvPolynomial.C (n i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ))) =
      MvPolynomial.C (∑ i, (n i : Ω) * x i) * X 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨⟩, i⟩ := i
  rw [cone_X]
  simp [mConeMap, pair, mul_assoc]

theorem mem_twoBlockIdeal (x x' : Ix κ → Ω) (f : MRing (FinTwoTypeFamily κ)) :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (pair x x') f = 0 :=
  RingHom.mem_ker

theorem le_of_add_one_le' {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h' : ((b + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
    rw [WithBot.coe_le_coe] at h'
    change ((b : ℕ∞) : WithBot ℕ∞) ≤ (((n : ℕ) : ℕ∞) : WithBot ℕ∞)
    rw [WithBot.coe_le_coe]
    induction b using ENat.recTopCoe with
    | top => exact absurd h' (by simp)
    | coe m =>
      have : m + 1 ≤ n + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : m ≤ n)

end TwoBlockModuleFinite


open TwoBlockModuleFinite in
theorem TwoBlockModuleFinite.proof : TwoBlockModuleFinite.Statement := by
  classical
  have hA := CoordArithOfFnField.proof
  have hF := TwoBlockFnField.proof
  intro D Ω _ _ κ _ x B c l hx hli hB hspan hxc
  obtain ⟨hFp, -⟩ := hF Ω κ x B hB
  set x' := matAct B x with hx'def
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx
  have hxc0 : x ⟨(), c⟩ ≠ 0 := hli.ne_zero _
  have hx'0 : ∃ j, x' ⟨(), j⟩ ≠ 0 := by
    by_contra h
    push Not at h
    apply hxc0
    rw [hxc]
    exact Finset.sum_eq_zero fun j _ => by
      obtain ⟨⟨⟩, j⟩ := j
      rw [h j, mul_zero]
  obtain ⟨i₁, hi₁⟩ := hx'0
  have hpA : IsArithVar (twoBlockIdeal x x') (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x x') (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨c, by simpa [pair] using hxc0⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  obtain ⟨S, hS, hPS⟩ := hpA.2.1.2.1

  have hL : ∀ i : κ, ∃ L : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (L j : Ω) * x' j := by
    intro i
    have hmem : x ⟨(), i⟩ ∈ Submodule.span ℤ (Set.range x') := hspan (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨L, hL⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
    exact ⟨L, by rw [← hL]; simp [zsmul_eq_mul]⟩
  choose L hL using hL

  set N : ℕ := ∏ p : Ix κ × Ix κ, (B p.1 p.2).den with hN
  have hN0 : 0 < N := Finset.prod_pos fun p _ => (B p.1 p.2).den_pos
  have hn : ∀ j i, ∃ z : ℤ, (z : ℚ) = N * B j i := by
    intro j i
    obtain ⟨M, hM⟩ : (B j i).den ∣ N :=
      Finset.dvd_prod_of_mem (fun p : Ix κ × Ix κ => (B p.1 p.2).den) (Finset.mem_univ (j, i))
    refine ⟨M * (B j i).num, ?_⟩
    rw [hM]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose n hn using hn
  have hNx' : ∀ j : κ, (N : Ω) * x' ⟨(), j⟩ = ∑ i, (n ⟨(), j⟩ i : Ω) * x i := by
    intro j
    simp only [hx'def, matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    congr 1
    have h := congrArg (fun q : ℚ => (q : Ω)) (hn ⟨(), j⟩ i)
    push_cast at h
    rw [h]
  have hPO : twoBlockIdeal x x' ≤ twoBlockMOuter x x' c := le_sup_left
  have hPI : twoBlockIdeal x x' ≤ twoBlockMInner x x' l := le_sup_left
  have hgO : ∀ j : κ, twoBlockDen c * X ⟨1, j⟩ ∈ twoBlockMOuter x x' c := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  have hgI : ∀ i : κ, twoBlockNum l * X ⟨0, i⟩ ∈ twoBlockMInner x x' l := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hlx : ∑ j, (l j : Ω) * x' j = x ⟨(), c⟩ := hxc.symm
  refine ⟨?_, ?_, ?_, ⟨N, hN0, ?_⟩, ?_⟩
  ·
    refine ⟨S ∪ Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩, ?_, ?_⟩
    · rintro f (hf | ⟨j, rfl⟩)
      · exact hS f hf
      · exact ⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockDen c)
          (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩
    · rw [twoBlockMOuter, hPS, Ideal.span_union]
  ·
    refine ⟨S ∪ Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩, ?_, ?_⟩
    · rintro f (hf | ⟨i, rfl⟩)
      · exact hS f hf
      · exact ⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockNum l)
          (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩
    · rw [twoBlockMInner, hPS, Ideal.span_union]
  ·
    rw [twoBlockMInner, sup_le_iff]
    refine ⟨hPO, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨i, rfl⟩
    have hd : twoBlockNum l * X ⟨0, i⟩ - twoBlockDen c * twoBlockNum (L i) ∈ twoBlockIdeal x x' := by
      rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, cone_num, cone_num, twoBlockDen, cone_X, cone_X, hlx,
        ← hL i]
      simp [pair]
      ring
    have hs : twoBlockDen c * twoBlockNum (L i) ∈ twoBlockMOuter x x' c := by
      rw [twoBlockNum, Finset.mul_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [mul_left_comm]
        exact Ideal.mul_mem_left _ _ (hgO j.2)
    have h := Ideal.add_mem _ (hPO hd) hs
    rwa [sub_add_cancel] at h
  ·
    intro f hf
    rw [twoBlockMOuter, Submodule.mem_sup] at hf
    obtain ⟨p, hp, s, hs, rfl⟩ := hf
    rw [mul_add]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hPI hp)) ?_
    induction hs using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      have hd : (N : MRing (FinTwoTypeFamily κ)) * (twoBlockDen c * X ⟨1, j⟩) -
          twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈
            twoBlockIdeal x x' := by
        rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, map_mul, map_natCast, cone_num, coneMap_firstBlock_linearForm, twoBlockDen, cone_X,
          cone_X, hlx, ← hNx' j]
        simp [pair]
        ring
      have hs : twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈
          twoBlockMInner x x' l := by
        rw [Finset.mul_sum]
        exact Ideal.sum_mem _ fun i _ => by
          rw [mul_left_comm]
          exact Ideal.mul_mem_left _ _ (hgI i.2)
      have h := Ideal.add_mem _ (hPI hd) hs
      rwa [sub_add_cancel] at h
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul r a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ ha
  ·
    intro W hW hIW _
    have : (twoBlockIdeal x x').IsPrime := hpA.2.1.1
    have := hW
    have hlt : twoBlockIdeal x x' < W := by
      refine lt_of_le_of_ne (hPI.trans hIW) fun h => ?_
      have hm : twoBlockNum l * X ⟨0, c⟩ ∈ twoBlockIdeal x x' := by
        rw [h]
        exact hIW (hgI c)
      rw [mem_twoBlockIdeal, map_mul, cone_num, cone_X, hlx] at hm
      simp [pair, hxc0] at hm
    have h := krullDim_quotient_add_one_le hlt
    rw [hpA.2.2.2, Fintype.card_fin, show D + 1 + 2 = D + 2 + 1 by omega] at h
    rw [Fintype.card_fin]
    exact le_of_add_one_le' h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace VeroneseGraphDeg

theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

def xc {D : ℕ} (i : Fin (D + 1)) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k := ⟨Sum.inl (), i⟩

def yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k :=
  ⟨Sum.inr (), ⟨(i, j), h⟩⟩

abbrev Γ (D : ℕ) : Ideal (MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) :=
  graphIdeal ⊥ (Veronese.forms D)

theorem graphMap_xc {D : ℕ} (i : Fin (D + 1)) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (xc i)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩)) :=
  eval₂Hom_X' _ _ _

theorem graphMap_yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (yc i j h)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩ * X ⟨(), j⟩)) * X () :=
  eval₂Hom_X' _ _ _

theorem rel_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∈ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_xc, graphMap_xc, graphMap_yc,
    graphMap_yc]
  simp only [map_mul]
  ring

theorem veroneseFirstCoordinate_not_mem_graph (D : ℕ) :
    (X (yc 0 0 le_rfl) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_yc]
  refine mul_ne_zero ?_ (X_ne_zero _)
  rw [Ne, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

theorem x_not_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc i) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_xc, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero _

theorem x'_ne_zero {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (p : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k) (hp : (X p : MRing _) ∉ Γ D) :
    G.x' p ≠ 0 := by
  intro h
  apply hp
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
  exact h

theorem ratio_mem {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (i : Fin (D + 1)) : G.x' (xc i) / G.x' (xc 0) ∈ (⊥ : IntermediateField G.Φ G.Φ') := by
  have h0 := x'_ne_zero G _ (x_not_mem D 0)
  have h00 := x'_ne_zero G _ (veroneseFirstCoordinate_not_mem_graph D)
  have hr : aeval G.x' (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) = 0 := by
    rw [← RingHom.mem_ker, G.genericFibre_ker_target]
    exact rel_mem D i
  simp only [map_sub, map_mul, aeval_X, sub_eq_zero] at hr
  have c1 : G.x' (yc 0 i (Fin.zero_le i)) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩) :=
    G.compat ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩
  have c2 : G.x' (yc 0 0 le_rfl) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩) :=
    G.compat ⟨(), ⟨(0, 0), le_rfl⟩⟩
  rw [IntermediateField.mem_bot]
  refine ⟨G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩ / G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩, ?_⟩
  rw [map_div₀, ← c1, ← c2, div_eq_div_iff h00 h0]
  rw [mul_comm] at hr
  rw [hr, mul_comm]

end VeroneseGraphDeg


open VeroneseGraphDeg in
theorem VeroneseGraphDeg.proof (hGr : GraphStatement) (hImg : VeroneseGraphImage.Statement)
    (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    VeroneseGraphDeg.Statement := by
  intro D hD
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have hnv : ∀ u : Unit, ∃ j, Veronese.forms D ⟨u, j⟩ ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) := by
    intro u
    refine ⟨⟨(0, 0), le_rfl⟩, ?_⟩
    rw [Ideal.mem_bot]
    exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have hΓ : IsArithVar (Γ D) (D + 1) :=
    (hGr Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D) (fun _ _ => 2) hP
      (isMultiHomog_forms D) hnv).1
  have hIm : IsArithVar (imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D)) (D + 1) := by
    rw [Γ, hImg D]
    exact VeroneseArith.proof D hD
  have : (Γ D).IsPrime := hΓ.2.1.1
  let G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D) := Inter.genFibreOf _ _
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory (Veronese.Idx D)) (Unit ⊕ Unit) (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr
      inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  let ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) →
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k := fun
    | ⟨Sum.inl _, _⟩ => (0 : Fin (D + 1))
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(u | u), h⟩
    · cases u
      exact x'_ne_zero G _ (x_not_mem D 0)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(u | u), h⟩, i⟩, rfl⟩
    · cases u
      exact ratio_mem G i
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtFibreLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtFibreLift.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → IsClosedMultiPt P →
    Subsingleton (KH.cechHc ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) d 1) →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtGenUniform
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtGenUniform.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ (e : K → ℤ) (P : Ideal (MRingOver S ι)), IsClosedMultiPt P →
        ∃ (f : MRingOver S ι) (δ : K → ℕ) (c₀ : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ ∧ f ∉ P ∧
          ∀ c : ℕ, c₀ ≤ c → GenNear S ι 𝓜 (e + c • N) f δ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtSkyscraper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtSkyscraper.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓝 → IsClosedMultiPt P → (∀ p ∈ P, ∀ n : N, p • n = 0) →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ y ∈ KH.locPart ι 𝓝 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓝 d 0, z I = y

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

