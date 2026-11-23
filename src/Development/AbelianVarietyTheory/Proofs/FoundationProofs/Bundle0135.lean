module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_mem_of_isIntegral {K : Type} [Field K] (W : ValuationSubring K) {x : K} (h : IsIntegral W x) : x ∈ W := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

theorem hs_coeff_algebraMap {Ω : Type} [Field Ω] (c : Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  have : algebraMap Ω (PowerSeries Ω) c = PowerSeries.C c := rfl
  rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  simp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, hs_coeff_algebraMap, hs_coeff_algebraMap]
  split_ifs <;> simp

theorem Tower.gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s X.jK)).coeff r = (X.exp X.jK).coeff r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem Tower.adjoin_le_of_overY (X : Tower Ω ε) (W : ValuationSubring X.K) (hW : X.OverY W) :
    ∀ x ∈ Algebra.adjoin Ω {X.jK}, x ∈ W := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]; exact hW.2
  | algebraMap c => exact hW.1 c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem Tower.overY_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ W : ValuationSubring X.K, X.OverY W →
      (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧
        ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  intro Ω _ _ _ ε X hε hj W hW
  refine ⟨fun g => ⟨fun c => ?_, ?_⟩, fun s => ⟨fun c => ?_, ?_⟩⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl g (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl g X.jK ∈ W
    have hint := _root_.GlobalTheory.KZ.JInt.jK_sl_isIntegral ε X hε hj g
    let A := Algebra.adjoin Ω {X.jK}
    have hle : A.toSubring ≤ W.toSubring := fun x hx => X.adjoin_le_of_overY W hW x hx
    let ι : A →+* W := Subring.inclusion hle
    let _ : Algebra A W := ι.toAlgebra
    have : IsScalarTower A W X.K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact vs_mem_of_isIntegral W (hint.tower_top)
  · rw [ValuationSubring.mem_comap]
    change X.gal s (algebraMap Ω X.K c) ∈ W
    rw [X.gal_algebraMap]; exact hW.1 (s c)
  · rw [ValuationSubring.mem_comap]
    change X.gal s X.jK ∈ W
    rw [X.gal_jK]; exact hW.2

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesNotZeroDivisorModPrimePow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem primCan_mul_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (c : Ω) (a b : HahnSeries ℚ Ω)
    (ha : ∀ r, a.coeff r ∈ A) (hb : ∀ r, ∃ z ∈ A, b.coeff r = c * z) :
    ∀ r, ∃ z ∈ A, (a * b).coeff r = c * z := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = c * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, A.add_mem _ _ hz hw, by ring⟩
  · exact ⟨0, A.zero_mem, by simp⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hb ij.2
    exact ⟨a.coeff ij.1 * z, A.mul_mem _ _ (ha _) hz, by rw [e]; ring⟩

theorem primCan : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) →
    (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  intro Ω _ _ _ l _ A hl n L P φ hL hP hden hφ hφP
  obtain ⟨Q, hQ, -, hQP⟩ := _root_.GlobalTheory.prim_inv_mod_pow l A hl n L P hL hP hden
  have h1 : ∀ r, ∃ z ∈ A, (Q * P - 1).coeff r = (l : Ω) ^ n * z := by
    intro r
    obtain ⟨z, hz, e⟩ := hQP r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub]; exact e⟩
  have h2 := primCan_mul_dvd A _ φ _ hφ h1
  have h3 : ∀ r, ∃ z ∈ A, (Q * (φ * P)).coeff r = (l : Ω) ^ n * z := by
    refine primCan_mul_dvd A _ Q _ hQ ?_
    intro r
    obtain ⟨z, hz, e⟩ := hφP r
    exact ⟨z, hz, by rw [← e, sub_zero]⟩
  intro r
  obtain ⟨z, hz, ez⟩ := h3 r
  obtain ⟨w, hw, ew⟩ := h2 r
  have hid : φ = Q * (φ * P) - φ * (Q * P - 1) := by ring
  refine ⟨z - w, sub_mem hz hw, ?_⟩
  rw [sub_zero, hid, HahnSeries.coeff_sub, ez, ew]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGenerated
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def clearCoeff (n M w : ℕ) (c : Fin n → Polynomial ℂ) (i : ℕ) (τ : ℍ) : ℂ :=
  if h : i < n then
    DD τ ^ (w * (n - i)) * ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k))
  else DD τ ^ M

theorem dd_pow_mul_eval_jT (p : Polynomial ℂ) (M : ℕ) (hp : p.natDegree ≤ M) (τ : ℍ) :
    DD τ ^ M * p.eval (jT τ) =
      ∑ k ∈ Finset.range (M + 1), p.coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hD := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have hsplit : DD τ ^ M = DD τ ^ (M - k) * DD τ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hsplit]
  simp only [ReciprocityTheory.ChartRestriction.L1.jT, ReciprocityTheory.ChartRestriction.L1.AA]
  rw [div_pow, pow_mul]
  field_simp

theorem sum_clearCoeff_eq_zero (n M w : ℕ) (c : Fin n → Polynomial ℂ) (hM : ∀ i, (c i).natDegree ≤ M)
    (f : ℍ → ℂ) (h : ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0) (τ : ℍ) :
    ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i = 0 := by
  have key : ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i =
      DD τ ^ (w * n + M) * (f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range (fun i => clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i),
      mul_add, Finset.mul_sum, add_comm]
    congr 1
    · simp only [clearCoeff, lt_irrefl, dite_false]
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [clearCoeff, Fin.is_lt, dite_true, Fin.eta]
      rw [← dd_pow_mul_eval_jT _ M (hM i), mul_pow, ← pow_mul]
      have e : w * (n - i) + M + w * i = w * n + M := by
        rw [add_right_comm, ← mul_add, Nat.sub_add_cancel i.isLt.le]
      rw [← e, pow_add, pow_add]
      ring
  rw [key, h τ, mul_zero]

theorem qall_clearCoeff (R : Subring ℂ) (N : ℕ) (hN : 0 < N) (n M w : ℕ) (c : Fin n → Polynomial ℂ)
    (hc : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R) (i : ℕ) :
    QAll (· ∈ R) N (clearCoeff n M w c i) := by
  obtain ⟨hcst, -, -, hmul, hpow, hsum⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hDD : QAll (· ∈ R) N DD := ((_root_.GlobalTheory.QFam.eis_q N hN DD (Or.inr (Or.inr rfl))).2.1) R
  have hE : QAll (· ∈ R) N ⇑E₄ := ((_root_.GlobalTheory.QFam.eis_q N hN ⇑E₄ (Or.inl rfl)).2.1) R
  by_cases h : i < n
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ (w * (n - i)) *
        ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
      funext τ; simp [clearCoeff, h]
    rw [hf]
    refine hmul _ _ (hpow _ _ hDD) ?_
    refine (hsum ℕ (Finset.range (M + 1)) _ fun k hk => ?_).1
    exact hmul _ _ (hcst _ (hc _ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
      (hmul _ _ (hpow _ _ hE) (hpow _ _ hDD))
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff, h]
    rw [hf]
    exact hpow _ _ hDD

theorem powerSeries_map_mk {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (g : ℕ → Ω) :
    PowerSeries.map ε (PowerSeries.mk g) = PowerSeries.mk fun k => ε (g k) := by
  ext k; simp [PowerSeries.coeff_map]

theorem qcoeff_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω),
    0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) →
      ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε N w f a hN hLv hF
  classical
  haveI : CharZero Ω := ε.charZero
  obtain ⟨n, c, hc, hrel⟩ := _root_.GlobalTheory.FN.integral_over_jT ε.range f ⟨N, w, hN, hLv⟩
  set M := ∑ i, (c i).natDegree with hMdef
  have hM : ∀ i, (c i).natDegree ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => (c i).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpre : ∀ (i : Fin n) (k : ℕ), ∃ x : Ω, ε x = (c i).coeff k := fun i k => RingHom.mem_range.1 (hc i k)
  choose e he using hpre
  set S₀ : Finset Ω := Finset.univ.image (fun p : Fin n × Fin (M + 1) => e p.1 p.2) with hS₀
  set A : Subring Ω := Subring.closure (S₀ : Set Ω) with hA
  set R : Subring ℂ := A.map ε with hR
  have hcR : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R := fun i k hk =>
    Subring.mem_map.2 ⟨e i k, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(i, ⟨k, Nat.lt_succ_of_le hk⟩), Finset.mem_univ _, rfl⟩)), he i k⟩
  have hP : ∀ i, QAll (· ∈ R) N (clearCoeff n M w c i) := qall_clearCoeff R N hN n M w c hcR
  choose c' hc'Q hc'R using hP
  have hser := _root_.GlobalTheory.QFam.polyRel_qSeries N n (fun τ => DD τ ^ w * f τ) (fun k => ε (a k)) (clearCoeff n M w c) c' hN hF hc'Q
    (sum_clearCoeff_eq_zero n M w c hM f hrel)
  have hpre2 : ∀ i k, ∃ x ∈ A, ε x = c' i k := fun i k => Subring.mem_map.1 (hc'R i k)
  choose d hdA hd using hpre2
  set Q : Polynomial (PowerSeries Ω) :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (d i)) with hQdef
  have hmap : PowerSeries.map ε (Q.eval (PowerSeries.mk a)) =
      (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c' i))).eval
        (PowerSeries.mk fun k => ε (a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hQdef, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum, map_mul, map_pow,
      powerSeries_map_mk, hd]
  rw [hser] at hmap
  have hQ : Q.eval (PowerSeries.mk a) = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff k) hmap
    simpa [PowerSeries.coeff_map] using this
  have hcoef : ∀ i, Q.coeff i = if i ∈ Finset.range (n + 1) then PowerSeries.mk (d i) else 0 := fun i => by
    simp only [hQdef, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    simp [Finsupp.single_apply]
  have hQne : Q ≠ 0 := by
    intro h0
    have hn := hcoef n
    rw [h0, Polynomial.coeff_zero, if_pos (Finset.self_mem_range_succ n)] at hn
    have hc0 : c' n = 0 := funext fun k => by
      have h1 := congrArg (PowerSeries.coeff k) hn
      rw [PowerSeries.coeff_mk, map_zero] at h1
      rw [← hd n k, ← h1, map_zero]; rfl
    have hq := hc'Q n
    have hPn : clearCoeff n M w c n = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff]
    rw [hPn, hc0] at hq
    have hz : HasQ N (fun _ : ℍ => (0 : ℂ)) (0 : ℕ → ℂ) := fun τ => by simpa using hasSum_zero
    have := (_root_.GlobalTheory.QFam.hasQ_unique_both).2 N _ _ 0 hq hz
    exact pow_ne_zero M (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero UpperHalfPlane.I) (congrFun this UpperHalfPlane.I)
  have hcA : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A := fun i k => by
    rw [hcoef i]
    split_ifs
    · rw [PowerSeries.coeff_mk]; exact hdA i k
    · simp
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.AlgPowerSeries.exists_finset_coeff_mem_closure Ω A (PowerSeries.mk a) Q hQne hcA hQ
  refine ⟨S₀ ∪ S₁, fun k => ?_⟩
  have hk := hS₁ k
  rw [PowerSeries.coeff_mk] at hk
  refine (Subring.closure_le.2 ?_) hk
  rintro x (hx | hx)
  · exact Subring.closure_mono (by simp [Finset.coe_union]) hx
  · exact Subring.subset_closure (by simp [hx])

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassTwoFactorsLe
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.TwoFactors

variable {g : ℕ} [Fact g.Prime]

def PairAt (d e : ℕ) (x y : AlgebraicClosure (ZMod g)) (f : (ZMod g)[X]) : Prop :=
  (minpoly (ZMod g) x).natDegree = d ∧ (minpoly (ZMod g) y).natDegree = e ∧ minpoly (ZMod g) x ≠ minpoly (ZMod g) y ∧
    minpoly (ZMod g) x ∣ f ∧ minpoly (ZMod g) y ∣ f

def PairFor (d e l : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∃ x y : AlgebraicClosure (ZMod g), x ^ (g ^ d - 1) = 1 ∧ y ^ (g ^ e - 1) = 1 ∧ SamePart l x y ∧ PairAt d e x y f

end GlobalTheory.BadShare.TwoFactors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylRowActMemOfIsUnitDet
section
namespace GlobalTheory.TestLat

theorem weyl_rowAct_mem_of_isUnit_det :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
      ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g.det →
        ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν,
          Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν := by
  intro R _ _ n ν _ g hg f hf
  exact Formalism.UG.P.wlocal_main (le_refl n) ν n 0 (by omega) g g⁻¹ (Matrix.nonsing_inv_mul g hg)
    (fun _ _ hj => absurd hj (Nat.not_lt_zero _)) f hf

end GlobalTheory.TestLat
end

