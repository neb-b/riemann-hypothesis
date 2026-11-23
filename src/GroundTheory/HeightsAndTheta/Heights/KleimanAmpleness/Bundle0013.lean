module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmplePow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise

noncomputable section

universe u w

namespace VeryAmplePow

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def mono {r j : ℕ} (h : Fin (r + 1) → Ω) (w : Fin j → Fin (r + 1)) : Ω := ∏ t, h (w t)

theorem range_mono {r j : ℕ} (h : Fin (r + 1) → Ω) :
    Set.range (mono (j := j) h) = Set.range h ^ j := by
  ext a
  rw [Set.mem_pow_iff_prod]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨fun t => h (w t), fun t => ⟨w t, rfl⟩, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    choose w hw using hf
    exact ⟨w, by simp only [mono, hw]⟩

theorem mono_mem {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hH : ∀ l I, h l ∈ H.sub I) (w : Fin j → Fin (r + 1)) (I : Chart x) :
    mono h w ∈ H.sub I ^ j := by
  rw [Submodule.pow_eq_span_pow_set]
  exact Submodule.subset_span (Set.mem_pow_iff_prod.mpr ⟨fun t => h (w t), fun t => hH _ I, rfl⟩)

theorem mono_succ {r j : ℕ} (h : Fin (r + 1) → Ω) (w : Fin (j + 1) → Fin (r + 1)) :
    mono h w = h (w 0) * mono h (Fin.tail w) := by
  simp only [mono, Fin.prod_univ_succ, Fin.tail]

theorem mono_cons {r j : ℕ} (h : Fin (r + 1) → Ω) (v : Fin (r + 1)) (t : Fin j → Fin (r + 1)) :
    mono h (Fin.cons v t : Fin (j + 1) → Fin (r + 1)) = h v * mono h t := by
  simp only [mono, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem ampleChart_le {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hH : ∀ l I, h l ∈ H.sub I) (w : Fin (j + 1) → Fin (r + 1)) (I : Chart x) :
    ampleChart H 1 (h (w 0)) I ⊆ ampleChart (H.pow (j + 1)) 1 (mono h w) I := by
  rintro a ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [SubSystem.pow_sub, one_mul] at hn
  rw [SubSystem.pow_sub, SubSystem.pow_sub, one_mul, ← pow_mul, mono_succ, mul_pow, ← mul_assoc,
    show (j + 1) * n = n + j * n by ring, pow_add, pow_mul]
  exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ (mono_mem hH _ I) n)

theorem isVeryAmpleBy_mono {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy H h) {m : ℕ} (E : (Fin (j + 1) → Fin (r + 1)) ≃ Fin (m + 1)) :
    IsVeryAmpleBy (H.pow (j + 1)) (fun k => mono h (E.symm k)) := by
  have hH : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  have hgen : ∀ k w', mono h w' / mono h (E.symm k) ∈
      ampleBase (S := S) (fun k => mono h (E.symm k)) k :=
    fun k w' => Algebra.subset_adjoin ⟨E w', by simp⟩
  refine ⟨fun k => ?_, fun I => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · exact (Submodule.mem_iInf _).mpr fun I => by
      rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
      exact mono_mem hH _ I
  · change Submodule.span _ (Set.range (mono h ∘ E.symm)) = _
    rw [EquivLike.range_comp, range_mono, ← Submodule.span_pow, hv.generates I, SubSystem.pow_sub]
  · have hk' : mono h (E.symm k) ≠ 0 := hk
    rw [mono_succ] at hk'
    have hl : h (E.symm k 0) ≠ 0 := left_ne_zero_of_mul hk'
    have hq : mono h (Fin.tail (E.symm k)) ≠ 0 := right_ne_zero_of_mul hk'
    intro a ha
    have hI : ∀ I, ∃ n, a * mono h (E.symm k) ^ n ∈ H.sub I ^ ((j + 1) * n) := fun I => by
      obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
      refine ⟨n, ?_⟩
      rwa [SubSystem.pow_sub, SubSystem.pow_sub, one_mul, ← pow_mul] at hn
    choose nI hnI using hI
    classical
    have hn0 : ∀ I, a * mono h (E.symm k) ^ (∑ I', nI I') ∈ H.sub I ^ ((j + 1) * ∑ I', nI I') :=
      fun I => by
        obtain ⟨d, hd⟩ : ∃ d, ∑ I', nI I' = nI I + d :=
          ⟨_, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ I))).symm⟩
        rw [hd, pow_add, ← mul_assoc, mul_add, pow_add]
        exact Submodule.mul_mem_mul (hnI I)
          (by rw [pow_mul]; exact Submodule.pow_mem_pow _ (mono_mem hH _ I) d)
    have hb : a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') ∈
        ampleRing H 1 (h (E.symm k 0)) := Set.mem_iInter.mpr fun I => ⟨(j + 1) * ∑ I', nI I', by
      rw [SubSystem.pow_sub, one_mul]
      have : a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') *
          h (E.symm k 0) ^ ((j + 1) * ∑ I', nI I') = a * mono h (E.symm k) ^ (∑ I', nI I') := by
        rw [pow_mul, div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hl))]
      rw [this]
      exact hn0 I⟩
    have hbase : ampleBase (S := S) h (E.symm k 0) ≤
        ampleBase (S := S) (fun k => mono h (E.symm k)) k := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨v, rfl⟩
      have : h v / h (E.symm k 0) =
          mono h (Fin.cons v (Fin.tail (E.symm k)) : Fin (j + 1) → Fin (r + 1)) / mono h (E.symm k) := by
        rw [mono_cons, mono_succ h (E.symm k), mul_div_mul_right _ _ hq]
      change h v / h (E.symm k 0) ∈ _
      rw [this]
      exact hgen k _
    have hinv : h (E.symm k 0) ^ (j + 1) / mono h (E.symm k) ∈
        ampleBase (S := S) (fun k => mono h (E.symm k)) k := by
      have : h (E.symm k 0) ^ (j + 1) = mono h (fun _ => E.symm k 0 : Fin (j + 1) → Fin (r + 1)) := by
        simp [mono, Finset.prod_const]
      rw [this]
      exact hgen k _
    have ha' : a = a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') *
        (h (E.symm k 0) ^ (j + 1) / mono h (E.symm k)) ^ (∑ I', nI I') := by
      rw [mul_assoc, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hl),
        div_self (by rw [mono_succ]; exact hk'), one_pow, mul_one]
    rw [ha']
    exact Subalgebra.mul_mem _ (hbase (hv.closed _ hl hb)) (Subalgebra.pow_mem _ hinv _)
  · have hk' : mono h (E.symm k) ≠ 0 := hk
    rw [mono_succ] at hk'
    have hl : h (E.symm k 0) ≠ 0 := left_ne_zero_of_mul hk'
    obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hv.affine (E.symm k 0) hl
    have hR : ampleRing H 1 (h (E.symm k 0)) ⊆ ampleRing (H.pow (j + 1)) 1 (mono h (E.symm k)) :=
      fun c hc => Set.mem_iInter.mpr fun I => ampleChart_le hH _ I (Set.mem_iInter.mp hc I)
    refine ⟨n, a, b, J, fun i => hR (ha i), fun i => hR (hb i), hsum, fun i I => ?_⟩
    obtain ⟨e, he⟩ := hJ i I
    exact ⟨e, ampleChart_le hH _ I he⟩

end VeryAmplePow

theorem VeryAmplePow.proof : VeryAmplePow.Statement.{u, w} := by
  intro S _ Ω _ _ N x H j hH hj
  obtain ⟨r, h, hv⟩ := hH
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have hc : (r + 1) ^ (j + 1) - 1 + 1 = (r + 1) ^ (j + 1) :=
    Nat.sub_add_cancel (Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.succ_ne_zero r)))
  exact ⟨_, _, VeryAmplePow.isVeryAmpleBy_mono hv (finFunctionFinEquiv.trans (finCongr hc.symm))⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleSecs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace VeryAmpleSecs

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]

theorem mem_secs_pow_twistSys_one_iff {r : ℕ} (h : Fin (r + 1) → Ω) (n : ℕ) (s : Ω) :
    s ∈ ((twistSys k h 1).pow n).secs ↔ ∀ j, h j ≠ 0 → s / h j ^ n ∈ ampleBase (S := k) h j := by
  constructor
  · intro hs j hj
    have hsj := (Submodule.mem_iInf _).mp hs (singleChart hj)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hsj)
    rw [chartRing_smul_def] at hb
    rw [← hb, mul_div_cancel_right₀ _ (pow_ne_zero n hj)]
    exact mem_ampleBase_of_mem_chartRing hj b.2
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hhi : h i ≠ 0 := (mem_support h).mp (I.2.2 hi)
    have hbase : ampleBase (S := k) h i ≤ chartRing k h (singleChart hhi) := by
      rw [ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      exact (ratio (S := k) hhi l).2
    have hmem : s / h i ^ n ∈ chartRing k h I :=
      chartRing_mono (Finset.singleton_subset_iff.mpr hi) (hbase (H i hhi))
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    have hs : s = (⟨s / h i ^ n, hmem⟩ : chartRing k h I) • h i ^ n := by
      rw [chartRing_smul_def, div_mul_cancel₀ _ (pow_ne_zero n hhi)]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (mem_twistMod_one I i) n)

theorem mem_pow_of_pow_mul_mem {A : Type*} [CommRing A] [Algebra A Ω] {L Q : Submodule A Ω}
    (hLQ : L * Q = 1) {r : ℕ} {h : Fin (r + 1) → Ω} (hL : Submodule.span A (Set.range h) = L)
    {s : Ω} {n : ℕ} (hs : ∀ j, ∃ e, h j ^ e * s ∈ L ^ (n + e)) : s ∈ L ^ n := by
  set C : Ideal A := (L ^ n).colon {s}
  have key : ∀ j, ∀ q ∈ Q, ∀ a : A, algebraMap A Ω a = h j * q → a ∈ C.radical := by
    intro j q hq a ha
    obtain ⟨e, he⟩ := hs j
    refine ⟨e, ?_⟩
    rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha]
    have hm := Submodule.mul_mem_mul (Submodule.pow_mem_pow Q hq e) he
    have hQL : Q ^ e * L ^ (n + e) = L ^ n := by
      calc Q ^ e * L ^ (n + e) = L ^ n * (L * Q) ^ e := by ring
        _ = L ^ n := by rw [hLQ, one_pow, mul_one]
    rw [hQL] at hm
    convert hm using 1
    ring
  have h1 : (1 : Submodule A Ω) ≤ Submodule.map (Algebra.linearMap A Ω) (C.radical : Submodule A A) := by
    rw [← hLQ, ← hL, ← Submodule.span_eq Q, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, q, hq, rfl⟩
    have hjq : h j * q ∈ L * Q := Submodule.mul_mem_mul (hL ▸ Submodule.subset_span ⟨j, rfl⟩) hq
    rw [hLQ, Submodule.mem_one] at hjq
    obtain ⟨a, ha⟩ := hjq
    exact ⟨a, key j q hq a ha, ha⟩
  obtain ⟨a, ⟨m, hm⟩, ha1⟩ := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have ha1' : algebraMap A Ω a = 1 := ha1
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha1', one_pow, one_mul] at hm
  exact hm

theorem exists_pow_mul_mem_pow {A : Subalgebra k Ω} {L : Submodule A Ω} {r : ℕ}
    {h : Fin (r + 1) → Ω} (hL : ∀ l, h l ∈ L) {j : Fin (r + 1)} (hj : h j ≠ 0) {t : Ω}
    (ht : t ∈ ampleBase (S := k) h j) : ∃ e, h j ^ e * t ∈ L ^ e := by
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨l, rfl⟩ := ht
    exact ⟨1, by rw [pow_one, pow_one, mul_div_cancel₀ _ hj]; exact hL l⟩
  | algebraMap c =>
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_zero, one_mul, Submodule.mem_one]
    exact ⟨⟨_, Subalgebra.algebraMap_mem A c⟩, rfl⟩
  | add t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ + t₂) = h j ^ e₂ * (h j ^ e₁ * t₁) + h j ^ e₁ * (h j ^ e₂ * t₂) := by
      ring
    rw [hs, pow_add]
    exact Submodule.add_mem _
      (by rw [mul_comm (L ^ e₁)]; exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₁)
      (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₂)
  | mul t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ * t₂) = (h j ^ e₁ * t₁) * (h j ^ e₂ * t₂) := by ring
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul he₁ he₂

end VeryAmpleSecs


open VeryAmpleSecs in
theorem VeryAmpleSecs.proof : VeryAmpleSecs.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hv n
  ext s
  rw [mem_secs_pow_twistSys_one_iff]
  have hL : ∀ I l, h l ∈ Nb.sub I := fun I l => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  constructor
  · intro hs j hj
    refine hv.closed j hj (Set.mem_iInter.mpr fun I => ⟨n, ?_⟩)
    rw [div_mul_cancel₀ _ (pow_ne_zero n hj), one_mul]
    exact (Submodule.mem_iInf _).mp hs I
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    obtain ⟨Q, hQ⟩ := Nb.invertible I
    refine mem_pow_of_pow_mul_mem hQ (hv.generates I) fun j => ?_
    by_cases hj : h j = 0
    · exact ⟨1, by rw [hj, pow_one, zero_mul]; exact Submodule.zero_mem _⟩
    obtain ⟨e, he⟩ := exists_pow_mul_mem_pow (hL I) hj (H j hj)
    refine ⟨e, ?_⟩
    have hs : h j ^ e * s = h j ^ n * (h j ^ e * (s / h j ^ n)) := by
      field_simp
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL I j) n) he

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ResidOfMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

section RestrictGenAux

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')


open Classical in
def RestrictGen.resid (a : Ω) : K' := if h : a ∈ R then σ ⟨a, h⟩ else 0

theorem RestrictGen.resid_of_mem {a : Ω} (h : a ∈ R) : RestrictGen.resid R σ a = σ ⟨a, h⟩ := dif_pos h

theorem RestrictGen.resid_zero : RestrictGen.resid R σ 0 = 0 := by
  rw [RestrictGen.resid_of_mem R σ (zero_mem R)]
  exact map_zero σ

theorem RestrictGen.resid_add {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a + b) = RestrictGen.resid R σ a + RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (add_mem ha hb), ← map_add]
  rfl

theorem RestrictGen.resid_mul {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a * b) = RestrictGen.resid R σ a * RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (mul_mem ha hb), ← map_mul]
  rfl

end RestrictGenAux


open RestrictGen in
theorem RestrictGen.proof : RestrictGen.Statement := by
  intro F _ N Ω _ _ x K' _ _ x' hxy R σ hσ Q Q' c H ρ w w' hw' hQ hQ' hH
  classical
  have hσ' : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      aeval x f / aeval x g ∈ R ∧ resid R σ (aeval x f / aeval x g) = aeval x' f / aeval x' g := by
    intro f g m hf hg hg'
    obtain ⟨h, e⟩ := hσ f g m hf hg hg'
    exact ⟨h, by rw [resid_of_mem R σ h, e]⟩
  by_cases hx' : ∃ j, x' j ≠ 0
  swap
  · simp only [not_exists, not_not] at hx'
    have hI : IsEmpty (Kleiman.Chart x') := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      exact (Kleiman.mem_support x').mp (I.2.2 hi) (hx' i)⟩
    exact ⟨0, ⟨fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I⟩⟩
  obtain ⟨j, hj⟩ := hx'
  have hxj : x j ≠ 0 := hxy j hj
  set r : Ω → K' := fun q => resid R σ (q * x j ^ c * w) / (x' j ^ c * w') with hr

  have hrat : ∀ i, x' i ≠ 0 → (x j / x i) ^ c ∈ R ∧ resid R σ ((x j / x i) ^ c) = (x' j / x' i) ^ c := by
    intro i hi
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := hσ' (X j ^ n) (X i ^ n) n (isHomogeneous_X_pow (R := F) j n) (isHomogeneous_X_pow (R := F) i n)
        (by simpa using pow_ne_zero n hi)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_natCast, div_pow] using this
    · have := hσ' (X i ^ n) (X j ^ n) n (isHomogeneous_X_pow (R := F) i n) (isHomogeneous_X_pow (R := F) j n)
        (by simpa using pow_ne_zero n hj)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_neg, zpow_natCast, div_pow, inv_div] using this

  have hchart : ∀ (I : Kleiman.Chart x') (a : Ω), a ∈ Kleiman.chartRing F x (Kleiman.liftChart hxy I) →
      a ∈ R ∧ resid R σ a ∈ Kleiman.chartRing F x' I := by
    rintro I a ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨h1, h2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    exact ⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩

  have hspan : ∀ (I : Kleiman.Chart x') (z : Ω),
      z ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H →
      z * w ∈ R ∧ resid R σ (z * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I z hz
    induction hz using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨hm, e⟩ := hH h hh
      refine ⟨hm, ?_⟩
      rw [resid_of_mem R σ hm, e, mul_div_cancel_right₀ _ hw']
      exact Submodule.subset_span ⟨h, hh, rfl⟩
    | zero =>
      rw [zero_mul, resid_zero, zero_div]
      exact ⟨zero_mem R, zero_mem _⟩
    | add a b _ _ ha hb =>
      refine ⟨by rw [add_mul]; exact add_mem ha.1 hb.1, ?_⟩
      rw [add_mul, resid_add R σ ha.1 hb.1, add_div]
      exact add_mem ha.2 hb.2
    | smul a z _ hz =>
      obtain ⟨ha1, ha2⟩ := hchart I a a.2
      rw [Kleiman.chartRing_smul_def, mul_assoc]
      refine ⟨mul_mem ha1 hz.1, ?_⟩
      rw [resid_mul R σ ha1 hz.1, mul_div_assoc]
      exact Submodule.smul_mem _ (⟨_, ha2⟩ : Kleiman.chartRing F x' I) hz.2

  have hkey : ∀ (I : Kleiman.Chart x') (i : Fin (N + 1)), i ∈ I.1 → ∀ q ∈ Q.sub (Kleiman.liftChart hxy I),
      q * x j ^ c * w ∈ R ∧ r q * x' i ^ c = resid R σ (x i ^ c * q * w) / w' ∧
      resid R σ (x i ^ c * q * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    have hxi : x i ≠ 0 := hxy i hx'i
    have hz : x i ^ c * q ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H := by
      rw [← hQ (Kleiman.liftChart hxy I)]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mpr ⟨q, hq, rfl⟩
    obtain ⟨hz1, hz2⟩ := hspan I _ hz
    obtain ⟨hr1, hr2⟩ := hrat i hx'i
    have heq : q * x j ^ c * w = (x j / x i) ^ c * (x i ^ c * q * w) := by
      rw [div_zpow]
      field_simp
    refine ⟨heq ▸ mul_mem hr1 hz1, ?_, hz2⟩
    rw [hr]
    dsimp only
    rw [heq, resid_mul R σ hr1 hz1, hr2, div_zpow]
    field_simp
  have hmem : ∀ (I : Kleiman.Chart x'), ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), r q ∈ Q'.sub I := by
    intro I q hq
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨-, e, hm⟩ := hkey I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    rw [← hQ' I] at hm
    obtain ⟨y, hy, hy'⟩ := (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mp hm
    have h' : r q * x' i ^ c = y * x' i ^ c := by
      rw [e, hy', smul_eq_mul, mul_comm]
    rw [mul_right_cancel₀ (zpow_ne_zero c hx'i) h']
    exact hy
  refine ⟨r, ⟨hmem, ?_, ?_, ?_⟩⟩
  · intro I q hq q' hq'
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    have h2 := (hkey I i hi q' hq').1
    rw [hr]
    dsimp only
    rw [add_mul, add_mul, resid_add R σ h1 h2, add_div]
  · intro I q hq f s e hs hf hse
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    obtain ⟨ha1, ha2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    have hm : aeval x f / aeval x s * q * x j ^ c * w = aeval x f / aeval x s * (q * x j ^ c * w) := by ring
    rw [hr]
    dsimp only
    rw [hm, resid_mul R σ ha1 h1, ha2, mul_div_assoc]
  · intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hmem I q hq
    · intro t ht
      have ht' : x' i ^ c * t ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
        rw [← hQ' I]
        exact (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mpr ⟨t, ht, rfl⟩
      have hall : ∀ u ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H),
          x' i ^ (-c) * u ∈ Submodule.span (Kleiman.chartRing F x' I) (r '' Q.sub (Kleiman.liftChart hxy I)) := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨h, hh, rfl⟩ := hu
          have hh' : h ∈ (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub (Kleiman.liftChart hxy I) := by
            rw [hQ]
            exact Submodule.subset_span hh
          obtain ⟨y, hy, rfl⟩ :=
            (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mp hh'
          obtain ⟨hm, e⟩ := hH _ hh
          obtain ⟨-, e', -⟩ := hkey I i hi y hy
          have e'' : resid R σ (x i ^ c * y * w) = ρ (x i ^ c • y) * w' := (resid_of_mem R σ hm).trans e
          rw [e'', mul_div_cancel_right₀ _ hw'] at e'
          have : x' i ^ (-c) * ρ (x i ^ c • y) = r y := by
            rw [← e', zpow_neg]
            field_simp
          rw [this]
          exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => rw [mul_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
        | smul a u _ hu =>
          rw [Kleiman.chartRing_smul_def, mul_left_comm]
          exact Submodule.smul_mem _ a hu
      have := hall _ ht'
      rwa [← mul_assoc, ← zpow_add₀ hx'i, neg_add_cancel, zpow_zero, one_mul] at this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

