module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterPrecisionLeLengthAndRank
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntRCloudSub
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

section Rec

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)

theorem six_le_r (R : Ranks) : 6 ≤ R.r := by
  have := R.two_le_m; have := R.m_add_three_le_k; unfold Ranks.r; omega

theorem one_le_Dp : 1 ≤ T.Dp := by
  rw [T.Dp_eq]
  have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord from D.R.ord_pos); omega
  exact Nat.mul_pos h2 (Nat.choose_pos (by have := six_le_r D.R; omega))

theorem forty_le_PP : 40 ≤ T.PP := le_trans (by exact_mod_cast T.nW_40) T.nW_le

theorem len_ge : 4 * T.Dp + 4 ≤ ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ := by
  have h1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast one_le_Dp T
  have h2 := forty_le_PP T
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h3 : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]; exact mul_le_mul_of_nonneg_left hmk (by positivity)
  have h4 : (8 : ℝ) * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have h5 : ((4 * T.Dp + 4 : ℕ) : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast h5.trans (Nat.le_ceil _)

theorem cZeroN_le_TO (j : ℕ) : cZeroN D j ≤ 12 * T.TO := by
  have h1 := cZeroN_le D j
  have h2 := T.TO_11D2
  have h6 := six_le_r D.R
  have h3 : D.R.r ^ 4 ≤ 6 * (D.R.r.choose 2) ^ 2 := by
    obtain ⟨s, hs⟩ : ∃ s, D.R.r = s + 1 := ⟨D.R.r - 1, by omega⟩
    have e : 2 * (D.R.r.choose 2) = D.R.r * s := by
      rw [hs, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' (by
        rw [mul_comm]; exact (Nat.even_mul_succ_self s).two_dvd)]
    have e2 : 4 * (D.R.r.choose 2) ^ 2 = D.R.r ^ 2 * s ^ 2 := by
      rw [← mul_pow, ← e]; ring
    have e3 : 4 * D.R.r ^ 2 ≤ 6 * s ^ 2 := by
      have : 5 ≤ s := by omega
      rw [hs]; nlinarith
    have e4 : D.R.r ^ 2 * (4 * D.R.r ^ 2) ≤ D.R.r ^ 2 * (6 * s ^ 2) := Nat.mul_le_mul_left _ e3
    nlinarith
  have h4 : D.R.f ^ 2 * D.R.r ^ 4 ≤ D.R.f ^ 2 * (6 * (D.R.r.choose 2) ^ 2) := Nat.mul_le_mul_left _ h3
  rw [T.Dp_eq, mul_pow] at h2
  nlinarith

theorem spacing_ge (j n : ℕ) (hn : n ≤ T.TO) :
    4 * ((cZeroN D j : ℝ) + 2 * D.R.r + n + T.Dp + 1) ≤ LevelStarExponents.h0 L ∧ 24 * (D.R.r : ℝ) * n ≤ LevelStarExponents.h0 L ∧
      4 * (n : ℝ) ^ 2 ≤ LevelStarExponents.h0 L := by
  have a1 : (cZeroN D j : ℝ) ≤ 12 * T.TO := by exact_mod_cast cZeroN_le_TO T j
  have a2 : 6 * (D.R.r : ℝ) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have : 6 * D.R.r ≤ T.TO := by nlinarith [Nat.zero_le (D.R.r * T.Dp)]
    exact_mod_cast this
  have a3 : 40 * ((T.Dp : ℝ) + 2) ≤ T.TO := by exact_mod_cast T.TO_40
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have a5 := T.heightBound_ge_order_sq
  have b0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have b1 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have b2 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have b3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  have : 6 * (D.R.r : ℝ) * n ≤ T.TO * T.TO := mul_le_mul a2 a4 b2 (by linarith)
  nlinarith

theorem prod_bounds (n : ℕ) (hn : n ≤ T.TO) :
    T.PP * n * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp ≤ LevelStarExponents.h0 L ∧
    T.PP ^ 2 * D.R.r * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ L.sc.b ∧
    T.PP * n * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b := by
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have hP := forty_le_PP T
  have hP0 : 0 ≤ T.PP := by linarith
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ T.heightBound_ge_order_product
    have e1 : T.PP * n * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) := by
      gcongr
    have e2 : T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.ChT * (T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k *
          (T.Dp : ℝ)) := le_mul_of_one_le_left (by positivity) T.ChT_ge
    calc _ ≤ _ := e1.trans e2
      _ = _ := by ring
  · refine le_trans ?_ T.b_ge
    have e2 : T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤
        T.CbN * (T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3) :=
      le_mul_of_one_le_left (by positivity) T.CbN_ge
    calc _ ≤ _ := e2
      _ = _ := by ring
  · have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
    have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
    have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have c1 := T.TD2'
    have c2 := T.TO_PP'
    rw [hlb] at c1
    have c3 : (1 : ℝ) ≤ T.TO := by
      have := T.TO_40
      exact_mod_cast (by omega : 1 ≤ T.TO)
    have c4 : T.PP ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_left hP0 c3) c2
    have c5 : (n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (by gcongr) c1
    have c6 : L.sc.b ^ (1 / 2 : ℝ) * L.sc.b ^ (1 / 2 : ℝ) = L.sc.b := by
      rw [← Real.rpow_add hb0]; norm_num
    calc _ = T.PP * ((n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul c4 c5 (by positivity) (by positivity)
      _ = _ := c6

theorem abs_logOm_le (hS : SizesAt L) (hL : 3 ≤ L.sc.L) : |L.logOm| ≤ 3 * L.sc.L := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -⟩ := hS
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have h1 := log_rdE_le_L D L hCond hQD
  have hrd : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have h0 := Real.log_nonneg hrd
  have h2 : |L.logDerivativeAtOne| ≤ L.sc.L := hQD.2.2.2.2.2.1
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  have h4 := Real.eulerMascheroniConstant_lt_two_thirds
  have h5 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h6 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos; linarith [Real.pi_le_four]
  have h7 := Real.log_two_lt_d9
  have h8 := Real.log_two_gt_d9
  unfold SizeData₂.logOm Host.v
  rw [Real.log_div Real.pi_pos.ne' (by positivity), Real.log_div (by positivity) (by norm_num)]
  obtain ⟨h9, h10⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

def entR (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℝ :=
  sgR D t n + DV.wSz D ((i : ℕ) + 1) t + n - ((D.R.k : ℝ) + i) + ((D.R.r : ℝ) + 1) / 2 -
    if n < D.R.k + i then 0 else (D.R.r : ℝ)

theorem ent_cast (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ((ent D i t n : ℚ) : ℝ) = entR D i t n := by
  unfold ent entR sgR
  rw [← DV.eQ_cast, eQ_succ]
  split_ifs <;> push_cast <;> ring

theorem entR_cloud (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k - 1) :
    DV.wSz D ((i : ℕ) + 1) t - D.R.r ≤ entR D i t n ∧ entR D i t n ≤ DV.wSz D ((i : ℕ) + 1) t + L.Sc + D.R.r := by
  unfold entR
  rw [if_pos (by omega), sgR_cloud D t n hn]
  obtain ⟨v0, v1⟩ := L.cloud_v t ⟨n, hn⟩
  have c1 : (n : ℝ) + 2 ≤ D.R.k := by exact_mod_cast (by omega : n + 2 ≤ D.R.k)
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c4 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
  have := r_cast D.R
  constructor <;> linarith

theorem entR_node (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : D.R.k - 1 ≤ n) (hr : n < D.R.r) :
    |entR D i t n| ≤ L.etaSz + D.R.r := by
  obtain ⟨a1, a2⟩ := abs_le.1 (sgR_be D L ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t n hn hr)
  have c1 : (D.R.k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : D.R.k ≤ n + 1)
  have c2 : (n : ℝ) + 1 ≤ D.R.r := by exact_mod_cast hr
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c7 : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have := r_cast D.R
  unfold entR
  split_ifs with h
  · have c8 : (n : ℝ) + 1 ≤ (D.R.k : ℝ) + (i : ℕ) := by exact_mod_cast h
    rw [abs_le]; constructor <;> linarith
  · have c8 : (D.R.k : ℝ) + (i : ℕ) ≤ n := by exact_mod_cast not_lt.1 h
    rw [abs_le]; constructor <;> linarith

theorem entR_step (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) :
    entR D i t n - entR D i t (n + 1) =
      sgR D t n - sgR D t (n + 1) - 1 + if n + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
  unfold entR
  split_ifs <;> first | omega | (push_cast; ring)

theorem entR_cloud_sub (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau)
    (hs : ∀ a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1)) (n : ℕ) (hn : n < D.R.k - 1) :
    0 ≤ entR D i t n - entR D i t (D.R.k - 1 - 1) ∧ entR D i t n - entR D i t (D.R.k - 1 - 1) ≤ L.Sc := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 := steps_sum (sgR D t) 0 D.R.r 1 (fun a _ ha => hs a ha) n (Nat.zero_le _) (D.R.k - 1 - 1) (by omega) (by omega)
  have h2 : (n : ℝ) ≤ ((D.R.k - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ D.R.k - 1 - 1)
  have h3 := (L.cloud_v t ⟨n, hn⟩).2
  have h4 := (L.cloud_v t ⟨D.R.k - 1 - 1, by omega⟩).1
  rw [← sgR_cloud] at h3 h4
  unfold entR
  rw [if_pos (by omega), if_pos (by omega)]
  constructor <;> linarith

end Rec

end GlobalTheory.CovTop.WtShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitMulZpowRegularLocalModelDimTwo
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUnit

variable {k L : Type} [Field k] [Field L] {c : k →+* L}

theorem isNoetherianRing {Q : Subring L} (hQ : IsLocModel c Q) : IsNoetherianRing Q := by
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
  exact Algebra.EssFiniteType.isNoetherianRing k Q

theorem isFractionRing {Q : Subring L} (hQ : IsLocModel c Q) : IsFractionRing Q L := by
  refine IsFractionRing.of_field Q L fun z => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩

theorem exists_place_of_height_eq_one {Q : Subring L} (hQ : IsLocModel c Q) [IsIntegrallyClosed Q]
    (p : Ideal Q) [p.IsPrime] (hp1 : p.height = 1) :
    ∃ P : Place c, P.IsPrimeOf Q ∧ ∀ a ∈ P.ring, ∃ s : Q, s ∉ p ∧ (s : L) * a ∈ Q := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  haveI : IsFractionRing Q L := isFractionRing hQ
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q L := Localization.subalgebra.ofField L p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hp
  haveI : IsLocalization.AtPrime A p := hA
  haveI : IsDiscreteValuationRing A := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 A
  haveI : IsFractionRing A L := Localization.subalgebra.isFractionRing_ofField L _ hp
  let V : ValuationSubring L :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, fun f hf => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    have e' : f * (b.1 : L) = a := congrArg Subtype.val e
    exact ⟨b.1, b.2, by rw [mul_comm, e']; exact a.2⟩

theorem mem_of_forall_isPrimeOf {Q : Subring L} (hQ : IsLocModel c Q) [IsIntegrallyClosed Q]
    (a : L) (h : ∀ P : Place c, P.IsPrimeOf Q → a ∈ P.ring) : a ∈ Q := by
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  haveI : IsFractionRing Q L := isFractionRing hQ
  obtain ⟨y, hy⟩ := (GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := Q) (K := L) a).2
    fun p _ hp1 => by
      obtain ⟨P, hP, hs⟩ := exists_place_of_height_eq_one hQ p hp1
      obtain ⟨s, hsp, hsa⟩ := hs a (h P hP)
      exact (GlobalTheory.mem_primeLocalSubalgebra_iff p a).2 ⟨s, hsp, ⟨⟨_, hsa⟩, rfl⟩⟩
  rw [← hy]
  exact y.2

end GlobalTheory.FieldPair.AdjUnit

namespace GlobalTheory.FieldPair.AdjUnit

theorem eq_unit_mul_zpow : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
    ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  intro L _ cL Q hQ t u hm hd E hE hu G hG hP
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  have hsp : (Ideal.span {t, u} : Ideal Q).spanFinrank ≤ 2 :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  haveI : IsRegularLocalRing Q := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q (by
    rw [← hm, hd]; exact_mod_cast hsp)
  have huL : (u : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hu
    exact zero_ne_one hu
  have hu0 : u ≠ 0 := fun h => huL (by rw [h]; rfl)
  have hum : u ∈ IsLocalRing.maximalIdeal Q := hm ▸ Ideal.subset_span (by simp)
  have htm : t ∈ IsLocalRing.maximalIdeal Q := hm ▸ Ideal.subset_span (by simp)
  have hu2 : u ∉ IsLocalRing.maximalIdeal Q ^ 2 := by
    intro h2
    have hle : IsLocalRing.maximalIdeal Q ≤ Ideal.span {t} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Q)
        (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
      rw [← hm, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Submodule.mem_sup_left (Ideal.subset_span rfl), Submodule.mem_sup_right ?_⟩
      rw [hm, smul_eq_mul, ← pow_two]
      exact h2
    have heq : IsLocalRing.maximalIdeal Q = Ideal.span {t} :=
      le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).2 htm)
    have h1 : (IsLocalRing.maximalIdeal Q).spanFinrank ≤ 1 := by
      rw [heq]
      exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
        (by rw [Set.ncard_singleton])
    have h3 := ringKrullDim_le_spanFinrank_maximalIdeal Q
    rw [hd] at h3
    have h4 : ((IsLocalRing.maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
    have := h3.trans h4
    norm_num at this
  haveI : IsRegularLocalRing (Q ⧸ Ideal.span ({u} : Set Q)) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hum hu2
  have hdom : IsDomain (Q ⧸ Ideal.span ({u} : Set Q)) := inferInstance
  have hpr : Prime u :=
    (Ideal.span_singleton_prime hu0).1 ((Ideal.Quotient.isDomain_iff_prime _).1 hdom)
  obtain ⟨S, -, -, hSo⟩ := GlobalTheory.FieldPair.AdjModel.exists_place hQ hpr
  have hES : E.ring = S.ring := by
    by_contra h
    have := hSo E hE h
    omega
  haveI : IsIntegrallyClosed Q := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing Q).2
  set b := E.ord G with hb
  set G' : L := G * (u : L) ^ (-b) with hG'
  have hG'0 : G' ≠ 0 := mul_ne_zero hG (zpow_ne_zero _ huL)
  have hord : ∀ P : Place cL, P.IsPrimeOf Q → P.ord G' = 0 := by
    intro P hPQ
    rw [hG', P.ord_mul hG (zpow_ne_zero _ huL), P.ord_zpow]
    by_cases hPE : P.ring = E.ring
    · obtain rfl : P = E := Place.ext hPE
      rw [hu, ← hb]; ring
    · rw [hP P hPQ hPE, hSo P hPQ (hES ▸ hPE)]; ring
  have h1 : G' ∈ Q := mem_of_forall_isPrimeOf hQ G' fun P hPQ =>
    (P.ord_nonneg_iff hG'0).1 (by rw [hord P hPQ])
  have h2 : G'⁻¹ ∈ Q := mem_of_forall_isPrimeOf hQ G'⁻¹ fun P hPQ =>
    (P.ord_nonneg_iff (inv_ne_zero hG'0)).1 (by rw [P.ord_inv, hord P hPQ]; rfl)
  refine ⟨⟨G', h1⟩, IsUnit.of_mul_eq_one (a := (⟨G', h1⟩ : Q)) (⟨G'⁻¹, h2⟩ : Q)
    (Subtype.ext (mul_inv_cancel₀ hG'0)), ?_⟩
  change G = G * (u : L) ^ (-b) * (u : L) ^ b
  rw [mul_assoc, ← zpow_add₀ huL, neg_add_cancel, zpow_zero, mul_one]

end GlobalTheory.FieldPair.AdjUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantNormalProjectiveCompactificationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_normal_projective_compactification : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).asIso.hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  intro F _ _ X V _ sX j _ Γ _ _ ρ hX hne hN hρ
  classical
  let A : Over (Sp F) := Over.mk sX
  let P : Over (Sp F) := ∏ᶜ fun _ : Γ => A
  let B : Over (Sp F) := Over.mk (j ≫ sX)
  let c : B ⟶ P := Pi.lift fun γ => Over.homMk ((ρ γ).asIso.hom ≫ j) (by simpa [A, B] using hρ γ)
  have hcπ (γ : Γ) : c.left ≫ (Pi.π (fun _ : Γ => A) γ).left = (ρ γ).asIso.hom ≫ j := by
    rw [← Over.comp_left, Pi.lift_comp_π]; rfl

  let σ₀ (g : Γ) : P ⟶ P := Pi.lift fun γ => Pi.π (fun _ : Γ => A) (γ * g)
  have hσπ (g γ : Γ) : σ₀ g ≫ Pi.π (fun _ : Γ => A) γ = Pi.π (fun _ : Γ => A) (γ * g) :=
    Pi.lift_comp_π _ _
  have hσ (g h : Γ) : σ₀ g ≫ σ₀ h = σ₀ (h * g) :=
    Pi.hom_ext _ _ fun γ => by rw [Category.assoc, hσπ, hσπ, hσπ, mul_assoc]
  have hσ1 : σ₀ 1 = 𝟙 P := Pi.hom_ext _ _ fun γ => by rw [hσπ, mul_one, Category.id_comp]
  let σI (g : Γ) : P.left ≅ P.left :=
    { hom := (σ₀ g).left, inv := (σ₀ g⁻¹).left,
      hom_inv_id := by rw [← Over.comp_left, hσ, inv_mul_cancel, hσ1]; rfl,
      inv_hom_id := by rw [← Over.comp_left, hσ, mul_inv_cancel, hσ1]; rfl }
  let σ : Γ →* Aut P.left := MonoidHom.mk' (fun g => Aut.of (σI g)) fun g h => by
    apply Aut.ext
    apply Iso.ext
    change (σ₀ (g * h)).left = (σ₀ h).left ≫ (σ₀ g).left
    rw [← Over.comp_left, hσ]
  have hσP (g : Γ) : (σ g).asIso.hom ≫ P.hom = P.hom := Over.w (σ₀ g)
  have hρmul (g γ : Γ) : (ρ (γ * g)).asIso.hom = (ρ g).asIso.hom ≫ (ρ γ).asIso.hom := by rw [map_mul]; rfl
  have H (g : Γ) : (ρ g).asIso.hom ≫ c.left = c.left ≫ (σ g).asIso.hom := by
    have e : (Over.homMk (ρ g).asIso.hom (by simpa [B] using hρ g) : B ⟶ B) ≫ c = c ≫ σ₀ g :=
      Pi.hom_ext _ _ fun γ => by
        rw [Category.assoc, Category.assoc, hσπ]
        ext1
        simp only [Over.comp_left, hcπ, Over.homMk_left, hρmul, Category.assoc]
    exact congrArg CommaMorphism.left e

  have : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX).1
  have hP : IsProjOver P.hom := GlobalTheory.EqModel.isProjOver_pi_const Γ A hX
  have : IsProper P.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hP).1
  have hcP : c.left ≫ P.hom = j ≫ sX := Over.w c
  have hc1 : c.left ≫ (Pi.π (fun _ : Γ => A) 1).left = j := by rw [hcπ, map_one]; rfl
  have : IsSeparated (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : QuasiSeparated c.left := .of_comp c.left P.hom
  have : IsSeparated (Pi.π (fun _ : Γ => A) 1).left := by
    have : IsSeparated ((Pi.π (fun _ : Γ => A) 1).left ≫ sX) := Over.w (Pi.π (fun _ : Γ => A) 1) ▸ inferInstance
    exact .of_comp _ sX
  have : IsIntegral V := isIntegral_of_isOpenImmersion j
  have : IsIntegral B.left := ‹IsIntegral V›
  have : GlobalTheory.IsNormalScheme B.left := hN
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sX)
  have : CompactSpace V := ⟨by
    rw [j.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ]
    exact NoetherianSpace.isCompact _⟩
  have : IsNoetherian V := {}
  have : QuasiCompact (c.left ≫ (Pi.π (fun _ : Γ => A) 1).left) := by
    rw [hc1]
    exact quasiCompact_of_noetherianSpace_source j
  have : QuasiCompact c.left := .of_comp c.left (Pi.π (fun _ : Γ => A) 1).left
  have : LocallyOfFiniteType (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : LocallyOfFiniteType c.left := locallyOfFiniteType_of_comp c.left P.hom

  have hfin : IsFinite c.left.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType c.left P.hom fun x _ =>
      charZero_of_injective_ringHom
        ((Scheme.ΓSpecIso (.of F)).inv ≫ (j ≫ sX).appTop ≫ V.Γevaluation x).hom.injective
  let φ : c.left.normalization ⟶ X := c.left.fromNormalization ≫ (Pi.π (fun _ : Γ => A) 1).left
  have hφ : φ ≫ sX = c.left.fromNormalization ≫ P.hom := by
    simp only [φ, Category.assoc]
    congr 1
    exact Over.w (Pi.π (fun _ : Γ => A) 1)
  have hproj : IsProjOver (φ ≫ sX) := hφ ▸ isProjOver_comp_of_isFinite _ hP
  have hnorm : GlobalTheory.IsNormalScheme c.left.normalization :=
    IsNormalScheme.normalization_of_isIntegral c.left
  let ρ' := normalizationAction c.left ρ σ H
  have hρ' (g : Γ) : (ρ' g).asIso.hom ≫ φ ≫ sX = φ ≫ sX := by
    rw [hφ, normalizationAction_fromNormalization_assoc, hσP]
  obtain ⟨W, q, sW, hq, hqs, hW, hqf, hqs'⟩ := GlobalTheory.EqModel.exists_projective_quotient (φ ≫ sX) ρ' hproj hρ'
  refine ⟨c.left.normalization, W, φ, c.left.toNormalization, ρ', q, sW, inferInstance, hnorm, hproj,
    GlobalTheory.EqModel.isOpenImmersion_toNormalization c.left (Pi.π (fun _ : Γ => A) 1).left j hc1, ?_,
    fun g => (toNormalization_normalizationAction c.left ρ σ H g).symm, hq, hqs, hW, hq.isIntegral,
    hqf, hqs'⟩
  simp only [φ, Scheme.Hom.toNormalization_fromNormalization_assoc, hc1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamilyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  first | exact @GlobalTheory.DenomIdeal.exists_idealSheaf | exact GlobalTheory.DenomIdeal.exists_idealSheaf | (intros; apply GlobalTheory.DenomIdeal.exists_idealSheaf <;> assumption)
end

