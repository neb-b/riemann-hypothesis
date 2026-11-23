module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosedLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace GraphClosedAlt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem chartRing_subset_ampleChart (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 h I := by
  refine ⟨0, ?_⟩
  rw [pow_zero, mul_one, mul_zero]
  change a ∈ twistMod S x 0 I
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero]
  have : a = (⟨a, ha⟩ : chartRing S x I) • (1 : Ω) := by rw [chartRing_smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem ampleChart_mul (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a b : Ω}
    (ha : a ∈ ampleChart H 1 h I) (hb : b ∈ ampleChart H 1 h I) : a * b ∈ ampleChart H 1 h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  rw [SubSystem.pow_sub] at hn hm ⊢
  rw [pow_add, pow_add]
  have : a * b * (h ^ n * h ^ m) = (a * h ^ n) * (b * h ^ m) := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn hm

theorem ampleChart_pow (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H 1 h I) (e : ℕ) : a ^ e ∈ ampleChart H 1 h I := by
  induction e with
  | zero => rw [pow_zero]; exact chartRing_subset_ampleChart H h I (one_mem _)
  | succ e ih => rw [pow_succ]; exact ampleChart_mul H h I ih ha

def chartUnion (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem div_mem_chartRing (I : Chart x) (j : Fin (N + 1)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    x j / x i ∈ chartRing S x I :=
  ⟨X j, X i, 1, X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

theorem exists_pow_mul_ratio_mem (I J : Chart x) {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I.1)
    {i : Fin (N + 1)} (hi : i ∈ I.1 ∪ J.1) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * (x i₀ / x i) ∈ chartRing S x I := by
  by_cases hiI : i ∈ I.1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_chartRing I i₀ hiI⟩
  have hiJ : i ∈ J.1 := (Finset.mem_union.mp hi).resolve_left hiI
  refine ⟨1, ?_⟩
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
  have hQ : xProd I ≠ 0 := xProd_ne_zero I
  obtain ⟨m, hm⟩ : ∃ m, I.1.card = m + 1 := ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨c, hc⟩ : ∃ c, J.1.card = c + 1 := ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hce : (J.1.erase i).card = c := by rw [Finset.card_erase_of_mem hiJ, hc]; rfl
  set P := ∏ j ∈ J.1.erase i, x j with hP
  have hJP : xProd J = x i * P := (Finset.mul_prod_erase J.1 x hiJ).symm
  have hprodI : ∏ i' ∈ I.1, (x i₀ / x i') = x i₀ ^ (m + 1) / xProd I := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hm]; rfl
  have hprodJ : ∏ j ∈ J.1.erase i, (x j / x i₀) = P / x i₀ ^ c := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hce]
  have key : (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ 1 * (x i₀ / x i) =
      (x i / x i₀) ^ m * (∏ j ∈ J.1.erase i, (x j / x i₀)) ^ (m + 1) *
        (∏ i' ∈ I.1, (x i₀ / x i')) ^ (c + 1) := by
    rw [hprodI, hprodJ, hJP, hm, hc, pow_one]
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [key]
  refine mul_mem (mul_mem (pow_mem (div_mem_chartRing I i hi₀) m)
    (pow_mem (prod_mem fun j _ => div_mem_chartRing I j hi₀) _))
    (pow_mem (prod_mem fun i' hi' => div_mem_chartRing I i₀ hi') _)

theorem exists_pow_mul_mem_chartRing (I J : Chart x) {z : Ω}
    (hz : z ∈ chartRing S x (chartUnion I J)) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * z ∈ chartRing S x I := by
  set σ := xProd J ^ I.1.card / xProd I ^ J.1.card
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hmon : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ (e d : ℕ), s.IsHomogeneous d ∧
      σ ^ e * (x i₀ ^ d / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨e, he⟩ := exists_pow_mul_ratio_mem (S := S) I J hi₀ (i := i) (by exact_mod_cast hi)
      exact ⟨e, 1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact he⟩
    | one => exact ⟨0, 0, isHomogeneous_one _ _, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e₁, d₁, had, hae⟩ := ha
      obtain ⟨e₂, d₂, hbd, hbe⟩ := hb
      refine ⟨e₁ + e₂, d₁ + d₂, had.mul hbd, ?_⟩
      have : σ ^ (e₁ + e₂) * (x i₀ ^ (d₁ + d₂) / aeval x (a * b)) =
          (σ ^ e₁ * (x i₀ ^ d₁ / aeval x a)) * (σ ^ e₂ * (x i₀ ^ d₂ / aeval x b)) := by
        rw [map_mul, pow_add, pow_add]; ring
      rw [this]
      exact mul_mem hae hbe
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hz
  obtain ⟨e, d', hsd', hmem⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (chartUnion I J) hs
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hdd : d' = d := hsd'.inj_right hsd hsne
  subst hdd
  have hf' : aeval x f / x i₀ ^ d' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ d', d', pow_mem (X_mem_monos hi₀) d', hf, isHomogeneous_X_pow i₀ d', by simp⟩
  refine ⟨e, ?_⟩
  have : σ ^ e * (aeval x f / aeval x s) = (aeval x f / x i₀ ^ d') * (σ ^ e * (x i₀ ^ d' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf' hmem

theorem exists_pow_mul_mem_ampleRing (H : SubSystem S x Ω) (h b : Ω) (J : Chart x)
    (hb : b ∈ ampleRing H 1 h)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H 1 h I)
    {c : Ω} (hc : c ∈ chartRing S x J) : ∃ e : ℕ, b ^ e * c ∈ ampleRing H 1 h := by
  classical
  have hloc : ∀ I : Chart x, ∃ e : ℕ, b ^ e * c ∈ ampleChart H 1 h I := by
    intro I
    obtain ⟨e₀, he₀⟩ := hbJ I
    have hcU : c ∈ chartRing S x (chartUnion I J) := chartRing_mono Finset.subset_union_right hc
    obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_chartRing I J hcU
    refine ⟨e₀ * e₁, ?_⟩
    have hρσ : (xProd I ^ J.1.card / xProd J ^ I.1.card) *
        (xProd J ^ I.1.card / xProd I ^ J.1.card) = 1 := by
      have := xProd_ne_zero I
      have := xProd_ne_zero J
      field_simp
    have : b ^ (e₀ * e₁) * c = (b ^ e₀ * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ e₁ *
        ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e₁ * c) := by
      calc b ^ (e₀ * e₁) * c = (b ^ e₀) ^ e₁ * ((xProd I ^ J.1.card / xProd J ^ I.1.card) *
          (xProd J ^ I.1.card / xProd I ^ J.1.card)) ^ e₁ * c := by
            rw [hρσ, one_pow, mul_one, pow_mul]
        _ = _ := by ring
    rw [this]
    exact ampleChart_mul H h I (ampleChart_pow H h I he₀ e₁)
      (chartRing_subset_ampleChart H h I he₁)
  choose f hf using hloc
  refine ⟨∑ I, f I, Set.mem_iInter.mpr fun I => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun I _ => Nat.zero_le (f I)) (Finset.mem_univ I))
  have : b ^ (f I + k) * c = (b ^ f I * c) * b ^ k := by ring
  rw [hk, this]
  exact ampleChart_mul H h I (hf I) (ampleChart_pow H h I (Set.mem_iInter.mp hb I) k)

end GraphClosedAlt

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointGenerated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace PointGenerated

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem inv_mem_chartRing (hx : IsSubvar x (primeOf (S := k) x) 0) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing k x I) : a⁻¹ ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set K := (HilbertPoint.affRing k x i).toIntermediateField' (HilbertPoint.isField_affRing hx hxi)

  have h1 : ∀ b ∈ K, b ∈ chartRing k x I := by
    intro b hb
    change b ∈ HilbertPoint.affRing k x i at hb
    rw [HilbertPoint.affRing, ← Algebra.adjoin_range_eq_range_aeval] at hb
    refine Algebra.adjoin_le (S := chartRing k x I) ?_ hb
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X k l, isHomogeneous_X k i, by
      simp [HilbertPoint.aff]⟩

  have h2 : a ∈ K := by
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    have hs0 := eval_ne_zero_of_mem_monos I hs
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have heq : aeval x f / aeval x s =
        aeval (HilbertPoint.aff x i) f / aeval (HilbertPoint.aff x i) s := by
      rw [HilbertPoint.aff_def, aeval_div_of_isHomogeneous hf, aeval_div_of_isHomogeneous hse]
      field_simp
    rw [heq]
    exact div_mem (show _ ∈ HilbertPoint.affRing k x i from ⟨f, rfl⟩)
      (show _ ∈ HilbertPoint.affRing k x i from ⟨s, rfl⟩)
  exact h1 _ (inv_mem h2)

theorem mem_sub_iff_of_subset (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) {I J : Chart x}
    (h : I.1 ⊆ J.1) (y : Ω) : y ∈ Q.sub J ↔ y ∈ Q.sub I := by
  refine ⟨fun hy => ?_, Q.mono I J h y⟩
  obtain ⟨a, ha, hay⟩ := (Q.mem_iff I J h y).mp hy
  have ha0 : (a : Ω) ≠ 0 := by
    intro h0
    apply ha.ne_zero
    exact Subtype.ext h0
  have hy' : y = (⟨(a : Ω)⁻¹, inv_mem_chartRing hx I a.2⟩ : chartRing k x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  rw [hy']
  exact Submodule.smul_mem _ _ hay

theorem mem_sub_iff (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) (I J : Chart x)
    (y : Ω) : y ∈ Q.sub I ↔ y ∈ Q.sub J := by
  let K : Chart x := ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
  rw [← mem_sub_iff_of_subset hx Q (show I.1 ⊆ K.1 from Finset.subset_union_left),
    mem_sub_iff_of_subset hx Q (show J.1 ⊆ K.1 from Finset.subset_union_right)]

end PointGenerated

theorem PointGenerated.proof : PointGenerated.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q hx I
  have hsecs : ∀ y, y ∈ Q.toSubSystem.secs ↔ y ∈ Q.sub I := by
    intro y
    rw [SubSystem.secs, Submodule.mem_iInf]
    exact ⟨fun h => h I, fun h J => (PointGenerated.mem_sub_iff hx Q I J y).mp h⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    exact (hsecs y).mp hy
  · intro y hy
    exact Submodule.subset_span ((hsecs y).mpr hy)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotSectionsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

theorem QuotSectionsFinite.proof (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q J

  let J' : Ideal (Poly k N) := Ideal.span {f | f ∈ J ∧ ∃ e, f.IsHomogeneous e}
  have hJ'hom : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J' := by
    have h : J'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
      Ideal.homogeneous_span _ _ fun f hf =>
        ⟨_, (mem_homogeneousSubmodule _ f).mpr hf.2.choose_spec⟩
    exact fun p hp d => homogeneousComponent_mem_of_mem h hp d
  have hforms : ∀ (f : Poly k N) (e : ℕ), f.IsHomogeneous e → (f ∈ J ↔ f ∈ J') := fun f e hf =>
    ⟨fun h => Ideal.subset_span ⟨h, e, hf⟩, fun h => (show J' ≤ J from Ideal.span_le.mpr (by
      intro g hg
      exact hg.1)) h⟩
  have hsys : idealSys x J = idealSys x J' := SubSystem.ext_sub fun I => by
    change idealMod J I = idealMod J' I
    unfold idealMod
    congr 1
    ext a
    constructor <;> rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mp hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mpr hf, hs, hfe, hse, rfl⟩

  obtain ⟨F, hF, hFfg⟩ := hI k Ω N x Q J' hJ'hom
  obtain ⟨M, -, hM⟩ := hE k Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨M', -, hM'⟩ := hE k Ω N x Ω F hFfg
  have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
  have h1 : M'.tildeSys 0 = Q.toSubSystem.twist (idealSys x J) := by
    rw [hsys, ← hF]
    exact SubSystem.ext_sub hM'

  have hle : ∀ I, (Q.toSubSystem.twist (idealSys x J)).sub I ≤ Q.toSubSystem.sub I := by
    intro I
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.span_induction (p := fun q _ => q • y ∈ Q.sub I) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
      exact (Q.sub I).smul_mem ⟨_, ⟨f, s, e, hs, hf, hse, rfl⟩⟩ hy
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq'; rw [smul_assoc]; exact Submodule.smul_mem _ a hq'
  have hH0 : Module.Finite k (Q.toSubSystem.H 0) := by
    rw [← h0]; exact hT k Ω N x M 0 0
  have hH1 : Module.Finite k ((Q.toSubSystem.twist (idealSys x J)).H 1) := by
    rw [← h1]; exact hT k Ω N x M' 1 0
  exact hQ k Ω N x Ω Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) hle hH0 hH1

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem SectionCount.proof (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨C₁, h₁⟩ := hT k Ω N x d Nb hZ hN
  obtain ⟨C₂, h₂⟩ := hD k Ω N x d Nb b hZ hN hb
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  set f : ℕ → ℝ := fun i =>
    (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) with hf
  set Y : ℝ := (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) with hY
  set X : ℝ := (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω)
    (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) : ℝ) with hX
  have h0 : f 0 = (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) :=
    congrArg (fun m : ℤ => (Module.finrank k (twistMul Nb.toSubSystem n m).secs : ℝ)) (by simp)
  have htel : f 0 - f n = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [Finset.sum_range_sub']
  have hsum : ∑ i ∈ Finset.range n, (f i - f (i + 1)) ≤
      ∑ _i ∈ Finset.range n, (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) :=
    Finset.sum_le_sum fun i hi => hn₂ i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have key : (n : ℝ) * (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) =
      ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) + C₂ * (n : ℝ) ^ d := by
    rw [hfac]; field_simp; ring
  rw [key] at hsum
  rw [← h0] at hn₁
  have hgoal : f n = (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ) := rfl
  rw [← hgoal]
  push_cast
  have e1 : (Y - ((d : ℝ) + 1) * X) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      Y * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
        ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by ring
  rw [e1]
  linarith

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem SubvarDrop.proof : SubvarDrop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf
  have := hpp
  obtain ⟨f, hfp, hfq⟩ := hf
  obtain ⟨j, hj⟩ := hrel

  have hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hx.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hfp

  have hnf : ¬ IsField (Poly k N ⧸ pp) := by
    intro hF
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j))
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq] at hv
    have h0 := hhom _ hv 0
    rw [homogeneousComponent_zero] at h0
    have h1 : (1 : Poly k N) ∈ pp := by
      have hc : AddMonoidAlgebra.coeff (X j * g - 1 : Poly k N) 0 = -1 := by
        change constantCoeff (X j * g - 1 : Poly k N) = -1; simp
      rw [hc, map_neg, map_one] at h0
      simpa using pp.neg_mem h0
    exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ pp) := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_nonneg_of_nontrivial

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe n =>
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hne0 rfl
        omega⟩
      refine ⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have : ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have := Nat.cast_le.mp this
      omega

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (e : ℕ), IsSubvar y pp e →
    ∀ (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∀ᶠ c : ℕ in atTop, restrLen pp (Q'.toSubSystem.twist (twistSys k y (c : ℤ))) =
        restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

