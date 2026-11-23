module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ChartIdeal

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev idealChart (J : Ideal (Poly k N)) (I : Chart x) : Ideal (chartRing k x I) :=
  (idealMod (x := x) J I).comap (Algebra.linearMap (chartRing k x I) Ω)

theorem idealMod_le_range (J : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I ≤ LinearMap.range (Algebra.linearMap (chartRing k x I) Ω) := by
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_mono {J J' : Ideal (Poly k N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  exact ⟨f, s, e, h hf, hs, hfe, hse, rfl⟩

theorem idealMod_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I * idealMod (x := x) J' I ≤ idealMod (x := x) (J * J') I := by
  rw [idealMod, idealMod, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, s, e, hf, hs, hfe, hse, rfl⟩, _, ⟨f', s', e', hf', hs', hfe', hse', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨f * f', s * s', e + e', Ideal.mul_mem_mul hf hf', mul_mem hs hs',
    hfe.mul hfe', hse.mul hse', ?_⟩
  simp only [map_mul, div_mul_div_comm]

theorem idealChart_mul_le (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealChart J I * idealChart J' I ≤ idealChart (x := x) (J * J') I :=
  Ideal.mul_le.mpr fun a ha b hb => by
    have := idealMod_mul_le (x := x) J J' I (Submodule.mul_mem_mul ha hb)
    simpa using this

theorem idealChart_top (I : Chart x) : idealChart (x := x) (⊤ : Ideal (Poly k N)) I = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  refine Submodule.subset_span ⟨1, 1, 0, Submodule.mem_top, one_mem _, isHomogeneous_one _ _,
    isHomogeneous_one _ _, ?_⟩
  simp

theorem idealChart_prod_le {ι : Type*} (s : Finset ι) (P : ι → Ideal (Poly k N)) (I : Chart x) :
    ∏ i ∈ s, idealChart (P i) I ≤ idealChart (x := x) (∏ i ∈ s, P i) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, idealChart_top, le_refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (Ideal.mul_mono_right ih).trans (idealChart_mul_le _ _ I)

theorem idealChart_pow_le (P : Ideal (Poly k N)) (I : Chart x) (n : ℕ) :
    idealChart P I ^ n ≤ idealChart (x := x) (P ^ n) I := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top, idealChart_top, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left ih).trans (idealChart_mul_le _ _ I)

theorem twist_idealSys_le (F : SubSystem k x Ω) (pp : Ideal (Poly k N)) (I : Chart x) :
    (F.twist (idealSys x pp)).sub I ≤ idealChart pp I • F.sub I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := idealMod_le_range pp I hq
  exact Submodule.smul_mem_smul (show a ∈ idealChart pp I from hq) hy

end ChartIdeal

section Algebra

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem le_sup_mul_smul {G F : Submodule A M} {P Q : Ideal A} (hP : F ≤ G ⊔ P • F)
    (hQ : F ≤ G ⊔ Q • F) : F ≤ G ⊔ (P * Q) • F := by
  calc F ≤ G ⊔ P • F := hP
    _ ≤ G ⊔ P • (G ⊔ Q • F) := sup_le_sup_left (Submodule.smul_mono le_rfl hQ) _
    _ ≤ G ⊔ (P * Q) • F := by
      rw [Submodule.smul_sup, Submodule.mul_smul, ← sup_assoc]
      exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _

theorem le_sup_prod_smul {ι : Type*} {G F : Submodule A M} (s : Finset ι) (P : ι → Ideal A)
    (h : ∀ i ∈ s, F ≤ G ⊔ P i • F) : F ≤ G ⊔ (∏ i ∈ s, P i) • F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact le_sup_mul_smul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem le_sup_pow_smul {G F : Submodule A M} {P : Ideal A} (h : F ≤ G ⊔ P • F) (n : ℕ) :
    F ≤ G ⊔ (P ^ n) • F := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
  | succ n ih => rw [pow_succ]; exact le_sup_mul_smul ih h

end Algebra

theorem StepThree.proof (hAway : StepThree.Away.Statement.{u, w})
    (hOnW : StepThree.OnW.Statement.{u, w}) : StepThree.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly k N) T.J
  choose! c₀ hc₀ using hOnW k Ω N x T hK
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg T.J (IsNoetherian.noetherian _)
  set s := hfin.toFinset
  refine ⟨∑ p ∈ s, |c₀ p|, fun b hb I => ?_⟩
  have hc : 0 ≤ ∑ p ∈ s, |c₀ p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  set F := (T.L.pow b).twist (twistSys k x (∑ p ∈ s, |c₀ p|))
  set G := Submodule.span (chartRing k x I) (F.secs : Set Ω)
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) ?_
  · exact (Submodule.mem_iInf _).mp hz I
  have h1 : ∀ p ∈ s, F.sub I ≤ G ⊔ idealChart p I • F.sub I := fun p hp => by
    have hp' := hfin.mem_toFinset.mp hp
    refine (hc₀ p hp' b _ hb ?_ I).trans (sup_le_sup_left (twist_idealSys_le F p I) _)
    exact (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (c₀ q)) hp)
  have h2 := le_sup_pow_smul (le_sup_prod_smul s _ h1) (n * b)
  have hrad : ∏ p ∈ s, p ≤ T.J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact le_sInf fun q hq => Ideal.prod_le_inf.trans (Finset.inf_le (hfin.mem_toFinset.mpr hq))
  have h3 : (∏ p ∈ s, idealChart p I) ^ (n * b) ≤ idealChart T.J I ^ b := by
    rw [pow_mul]
    refine Ideal.pow_right_mono ?_ b
    refine (Ideal.pow_right_mono (idealChart_prod_le s (fun p => p) I) n).trans
      ((idealChart_pow_le _ I n).trans ?_)
    exact Submodule.comap_mono (idealMod_mono ((Ideal.pow_right_mono hrad n).trans hn) I)
  have h4 := hAway k Ω N x T b _ hc I
  exact h2.trans (sup_le le_rfl ((Submodule.smul_mono_left h3).trans h4))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThree.Away

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem homogeneousComponent_homog_mul {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

theorem span_singleton_pow_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (a : A)
    (n : ℕ) : Submodule.span R {a} ^ n = Submodule.span R {a ^ n} := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih => rw [pow_succ, ih, Submodule.span_mul_span, Set.singleton_mul_singleton, pow_succ]

theorem twistSys_sub (c : ℤ) (I : Chart x) : (twistSys S x c).sub I = twistMod S x c I := rfl

theorem twist_sub (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩

theorem twistMod_zero (I : Chart x) : twistMod S x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem twistMod_mul (a a' : ℤ) (I : Chart x) :
    twistMod S x a I * twistMod S x a' I = twistMod S x (a + a') I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twistMod_eq_span a I hi, twistMod_eq_span a' I hi, twistMod_eq_span (a + a') I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, zpow_add₀ hxi]

theorem twistMod_pow (a : ℤ) (I : Chart x) (n : ℕ) :
    twistMod S x a I ^ n = twistMod S x (n * a) I := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero]
  | succ n ih =>
    rw [pow_succ, ih, twistMod_mul]
    congr 1
    push_cast
    ring

theorem pow_sub (Q : SubSystem S x Ω) (I : Chart x) (n : ℕ) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => exact (twistMod_zero I).trans (pow_zero _).symm
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub, ih, pow_succ']

theorem div_pow_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) {h : Poly S N} {d : ℕ}
    (hh : h.IsHomogeneous d) : aeval x h / x i ^ d ∈ chartRing S x I :=
  ⟨h, X i ^ d, d, pow_mem (X_mem_monos hi) d, hh, isHomogeneous_X_pow i d, by rw [map_pow, aeval_X]⟩

theorem homogeneousComponent_mul_mem (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) {f : Poly S N} (hf : f ∈ zeroIdeal D σ) (e : ℕ) :
    ∀ δ ∈ D.sub I, aeval x (homogeneousComponent e f) * δ ∈
      Submodule.span (chartRing S x I) {σ * x i ^ e} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [zeroIdeal, Ideal.span] at hf
  induction hf using Submodule.span_induction generalizing e with
  | mem g hg =>
    obtain ⟨c, hgc, hg⟩ := hg
    intro δ hδ
    rw [homogeneousComponent_of_mem hgc]
    split_ifs with hce
    · subst hce
      obtain ⟨o, ho, heq⟩ := hg I δ hδ
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
      obtain ⟨t, rfl⟩ := ho
      rw [heq, Submodule.mem_span_singleton]
      exact ⟨t, by rw [chartRing_smul_def, chartRing_smul_def, zpow_natCast]; ring⟩
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | zero => intro δ _; rw [map_zero, map_zero, zero_mul]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    intro δ hδ
    rw [map_add (f := _), map_add (f := _), add_mul]
    exact Submodule.add_mem _ (hf e δ hδ) (hg e δ hδ)
  | smul r f _ hf =>
    intro δ hδ
    have hsum : r * f = ∑ d ∈ Finset.range (r.totalDegree + 1), homogeneousComponent d r * f := by
      rw [← Finset.sum_mul, sum_homogeneousComponent]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, hsum, map_sum, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [homogeneousComponent_homog_mul (homogeneousComponent_isHomogeneous d r) f e]
    split_ifs with hde
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hf (e - d) δ hδ)
      rw [map_mul, mul_assoc, ← ht, Submodule.mem_span_singleton]
      refine ⟨⟨_, div_pow_mem_chartRing I hi (homogeneousComponent_isHomogeneous d r)⟩ * t, ?_⟩
      have hpow : x i ^ e = x i ^ d * x i ^ (e - d) := by rw [← pow_add, Nat.add_sub_cancel' hde]
      have hxd : x i ^ d ≠ 0 := pow_ne_zero _ hxi
      rw [chartRing_smul_def, chartRing_smul_def, Subalgebra.coe_mul, hpow]
      field_simp
      try ring
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _

theorem idealMod_zeroIdeal_mul_le (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) :
    idealMod (x := x) (zeroIdeal D σ) I * D.sub I ≤ Submodule.span (chartRing S x I) {σ} := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [Submodule.mul_le]
  intro a ha δ hδ
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, s, e, hf, hs, hfe, hse, rfl⟩ := ha
    have h := homogeneousComponent_mul_mem D σ I hi hf e δ hδ
    rw [homogeneousComponent_of_mem hfe, if_pos rfl] at h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse,
      by rw [map_pow, aeval_X]⟩ * t, ?_⟩
    rw [chartRing_smul_def, Subalgebra.coe_mul,
      show aeval x f / aeval x s * δ = aeval x f * δ / aeval x s by ring, ← ht, chartRing_smul_def]
    field_simp
    try ring
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

end Lemmas

theorem proof : StepThree.Away.Statement.{u, w} := by
  intro k _ Ω _ _ N x T b c hc I
  obtain ⟨i, hi⟩ := I.2.1
  have hL : ∀ I' : Chart x, T.L.sub I' = twistMod k x T.c₁ I' * T.D.sub I' := by
    intro I'
    change ((T.M.toSubSystem.pow T.p).twist (twistSys k x T.m)).sub I' =
      _ * ((T.M.toSubSystem.pow T.p).twist (twistSys k x (T.m - T.c₁))).sub I'
    rw [twist_sub, twist_sub, twistSys_sub, twistSys_sub, ← mul_assoc, twistMod_mul,
      add_sub_cancel]
  have hF : ∀ I' : Chart x, ((T.L.pow b).twist (twistSys k x c)).sub I' =
      twistMod k x (c + b * T.c₁) I' * T.D.sub I' ^ b := by
    intro I'
    rw [twist_sub, twistSys_sub, pow_sub, hL, mul_pow, twistMod_pow, ← mul_assoc, twistMod_mul]
  have hn : 0 ≤ c + b * T.c₁ :=
    add_nonneg hc (mul_nonneg (Nat.cast_nonneg b) (by linarith [T.c₁_pos]))
  obtain ⟨n, hnn⟩ := Int.eq_ofNat_of_zero_le hn

  have hy : x i ^ n * T.si ^ b ∈ ((T.L.pow b).twist (twistSys k x c)).secs := by
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    change _ ∈ ((T.L.pow b).twist (twistSys k x c)).sub I'
    rw [hF I', hnn]
    refine Submodule.mul_mem_mul (Submodule.subset_span ⟨X i ^ n, 1, 0, n, one_mem _,
      isHomogeneous_X_pow i n, isHomogeneous_one _ _, by simp, by simp⟩)
      (Submodule.pow_mem_pow _ ?_ b)
    exact (Submodule.mem_iInf _).mp T.si_mem I'

  have hbound : idealMod (x := x) T.J I ^ b * ((T.L.pow b).twist (twistSys k x c)).sub I ≤
      Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
    rw [hF I, mul_left_comm, ← mul_pow]
    calc twistMod k x (c + b * T.c₁) I * (idealMod (x := x) T.J I * T.D.sub I) ^ b
        ≤ twistMod k x (c + b * T.c₁) I * Submodule.span (chartRing k x I) {T.si} ^ b := by
          gcongr
          exact idealMod_zeroIdeal_mul_le T.D T.si I
      _ = Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
          rw [twistMod_eq_span _ I hi, span_singleton_pow_eq, Submodule.span_mul_span,
            Set.singleton_mul_singleton, hnn, zpow_natCast]
  rw [Submodule.smul_le]
  intro r hr z hz
  have hr' : (r : Ω) ∈ idealMod (x := x) T.J I ^ b := by
    have hm := Submodule.mem_map_of_mem (f := (Algebra.ofId (chartRing k x I) Ω).toLinearMap) hr
    rw [Submodule.map_pow] at hm
    have hle : Submodule.map (Algebra.ofId (chartRing k x I) Ω).toLinearMap
        ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ≤
          idealMod (x := x) T.J I := by
      rintro y ⟨a, ha, rfl⟩
      exact ha
    exact pow_le_pow_left' hle b hm
  have hrz := hbound (Submodule.mul_mem_mul hr' hz)
  rw [chartRing_smul_def]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr hy) hrz

end StepThree.Away

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerCharQuot k
            ((F₁.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
            ((F₂.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotIsoSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v'

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

structure QuotIso {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    {E' : Type v'} [AddCommGroup E'] [Module Ω E'] [Module S E'] [IsScalarTower S Ω E']
    (F₁ F₂ : SubSystem S x E) (G₁ G₂ : SubSystem S x E') where

  equiv : ∀ I : Chart x,
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[S] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I)

  comm : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I),
    equiv J (SubSystem.quotRes F₁ F₂ I J h y) = SubSystem.quotRes G₁ G₂ I J h (equiv I y)

end Defs

def SnapperQuotIso.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (E' : Type v') [AddCommGroup E'] [Module Ω E'] [Module k E'] [IsScalarTower k Ω E']
    (F₁ F₂ : SubSystem k x E) (G₁ G₂ : SubSystem k x E'), QuotIso F₁ F₂ G₁ G₂ →
    eulerCharQuot k F₁ F₂ = eulerCharQuot k G₁ G₂

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperSection.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → (∃ i, (X i : Poly k N) ∉ pp) →
    ∀ (t : ℕ) (L : Fin t → LineBundle k x) (j : Fin t) (a : ℤ),
    ∃ (μ : ℤ) (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp < qq m) ∧
      ∀ (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ) - pieceChar k pp a L n c =
          ∑ m, pieceChar k (qq m) (b m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

