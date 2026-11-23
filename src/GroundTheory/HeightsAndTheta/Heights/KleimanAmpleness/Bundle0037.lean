module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionBundle

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PProjDegreePositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

universe u

namespace ProjDegreePositive

variable {F : Type u} [Field F] {ι₀ : Type} [Fintype ι₀]

theorem ringKrullDim_of_mem_minimalPrimes (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hmin.1.1
  have hIW : q ≤ W := le_sup_left.trans hmin.1.2
  have hxW : x ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MRing (fun _ : Unit => ι₀) F ⧸ q
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)
  set W' : Ideal B := W.map (Ideal.Quotient.mk q)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk q x ∈ W' := Ideal.mem_map_of_mem _ hxW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by
    cases h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl


omit [Fintype ι₀] in
theorem isRelevant_of_ringKrullDim (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by
  intro k
  by_contra h
  simp only [not_exists, not_not] at h
  have hX : ∀ v : (Σ _ : Unit, ι₀), (X v : MRing (fun _ : Unit => ι₀) F) ∈ W := by
    rintro ⟨⟨⟩, i⟩
    cases k
    exact h i
  have hsurj : Function.Surjective (algebraMap F (MRing (fun _ : Unit => ι₀) F ⧸ W)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨a, by rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]⟩
    | add p r hp hr =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hr
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
    | mul_X p v _ =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hX v), mul_zero]
  have hle := ringKrullDim_le_of_surjective _ hsurj
  rw [hW, ringKrullDim_eq_zero_of_field] at hle
  have : e + 1 ≤ 0 := by exact_mod_cast hle
  omega


set_option synthInstance.maxHeartbeats 400000 in
theorem hilbFn_pos (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by
  obtain ⟨i, hi⟩ := hq.relevant ()
  have hqp := hq.isPrime
  obtain ⟨hfin, heq⟩ :=
    GroundTheory.Heights₂.Heights.FieldNumbers.GradedFinite.full F Unit (fun _ => ι₀) q (fun _ => n)
  have heq' : hilbFn q (fun _ => (n : ℤ)) =
      (Module.finrank F (gradedPiece q (fun _ : Unit => n)) : ℤ) := heq
  rw [heq']
  have hmem : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ∈
      gradedPiece q (fun _ : Unit => n) := by
    refine ⟨(X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n, ?_, rfl⟩
    change _ ∈ weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ι₀)) (fun _ : Unit => n)
    rw [mem_weightedHomogeneousSubmodule]
    have hp := (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ι₀)) ⟨(), i⟩).pow n
    convert hp using 1
    funext k
    cases k
    simp [blockWeight]
  have hne : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hi (hqp.mem_of_pow_mem n h)
  have := hfin
  have : Nontrivial (gradedPiece q (fun _ : Unit => n)) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank F (gradedPiece q (fun _ : Unit => n)) := Module.finrank_pos
  exact_mod_cast hpos


omit [Fintype ι₀] in
theorem le_ker_constantCoeff (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
  intro p hp
  rw [RingHom.mem_ker]
  by_contra h
  have h0 := hq.multiHomog p hp 0
  rw [weightedHomogeneousComponent_zero p (fun v => by
    obtain ⟨⟨⟩, _⟩ := v
    intro h'
    have := congrFun h' ()
    simp [blockWeight] at this)] at h0
  have hu : IsUnit (C (AddMonoidAlgebra.coeff p 0) : MRing (fun _ : Unit => ι₀) F) :=
    (isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C
  exact hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)

theorem pos (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨a₀, ha⟩ := HilbertSamuel.HilbertDimZero.proof F Unit (fun _ => ι₀) q hq
      (by rw [Fintype.card_unit]; exact hd)
    have h := ha (fun _ => a₀) (fun _ => le_rfl)
    have e : (fun _ : Fin 0 => fun _ : Unit => (1 : ℤ)) = (![] : Fin 0 → Unit → ℤ) :=
      funext fun j => j.elim0
    rw [e, ← h]
    exact hilbFn_pos q hq a₀
  | succ D ih =>
    intro q hq hd
    have hqp : q.IsPrime := hq.isPrime
    obtain ⟨i, hX⟩ := hq.relevant ()
    set x : MRing (fun _ : Unit => ι₀) F := X ⟨(), i⟩ with hxdef
    have hx : IsMultiHomog x (blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩) :=
      isWeightedHomogeneous_X F _ _
    have hlt : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) <
        ((D + 2 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
      rw [hd, Fintype.card_unit]
      exact_mod_cast (by omega : D + 1 + 1 < D + 2 + 1)
    have hcut := CutByForm.full F Unit (fun _ => ι₀) D q hqp hq.multiHomog hlt x _ hx hX
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ))
    have e1 : Matrix.vecCons (fun k => ((blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩ k : ℕ) : ℤ))
        (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = fun _ : Fin (D + 1) => fun _ : Unit => (1 : ℤ) := by
      funext j k
      cases k
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockWeight]
    rw [e1] at hcut
    rw [hcut, cycEval]
    set J := q ⊔ Ideal.span {x} with hJdef
    have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

    have hterm : ∀ W, divCycle q x W ≠ 0 →
        0 < divCycle q x W ∧ 0 < intNum F W (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
      intro W hW
      unfold divCycle at hW ⊢
      by_cases hc : W ∈ J.minimalPrimes ∧ IsRelevant W
      · rw [dite_eq_left hc] at hW ⊢
        have hWp : W.IsPrime := hc.1.1.1
        have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hc.1
        have hWq : IsMultiProjPrime W :=
          ⟨hWp, MinimalPrimeMultiHomog.full F Unit (fun _ => ι₀) J W hJh hc.1, hc.2⟩
        exact ⟨lt_of_le_of_ne (by positivity) (Ne.symm hW), ih W hWq hWd⟩
      · rw [dite_eq_right hc] at hW
        exact absurd rfl hW
    have hfin := DivCycleFiniteSupport.full F Unit (fun _ => ι₀) q x
    rw [finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hfin.coe_toFinset.symm.subset)]
    refine Finset.sum_pos' (fun W _ => ?_) ?_
    · by_cases hW : divCycle q x W = 0
      · rw [hW, zero_mul]
      · exact (mul_pos (hterm W hW).1 (hterm W hW).2).le

    have hJm : J ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
      refine sup_le (le_ker_constantCoeff q hq) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change constantCoeff x = 0
      rw [hxdef, constantCoeff_X]
    have hmax : (RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩).isPrime
    obtain ⟨W, hmin, -⟩ := Ideal.exists_minimalPrimes_le hJm
    have hWp : W.IsPrime := hmin.1.1
    have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hmin
    have hrel := isRelevant_of_ringKrullDim W D hWd
    have hne : divCycle q x W ≠ 0 := by
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hrel⟩]
      have htop := length_localizedQuot_ne_top J W hmin
      have hzero : multAt J W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr1⟩ := hs (1 : MRing (fun _ : Unit => ι₀) F ⧸ J)
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr1
        exact hr (hmin.1.2 hr1)
      have : (multAt J W).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]
        exact not_or.mpr ⟨hzero, htop⟩
      exact_mod_cast this
    refine ⟨W, hfin.mem_toFinset.mpr hne, mul_pos (hterm W hne).1 (hterm W hne).2⟩

end ProjDegreePositive

theorem ProjDegreePositive.proof : ProjDegreePositive.Statement.{u} := by
  intro F _ ι₀ _ q D hq hd
  exact ProjDegreePositive.pos D q hq hd

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem zero_mem_ampleChart {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {σ : E} {I : Chart z} :
    (0 : E) ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [zero_mul]; exact Submodule.zero_mem _⟩

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem exists_restrictData_isVeryAmpleBy (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I₀ : Chart y) (Nb : LineBundle k x) {r : ℕ}
    (h : Fin (r + 1) → Ω) (hV : IsVeryAmpleBy Nb.toSubSystem h) :
    ∃ (Q' : LineBundle k y) (ρ : Ω → K'), RestrictData Nb.toSubSystem hxy Q'.toSubSystem ρ ∧
      IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) ∧ dimCl k y = dimCl k (ρ ∘ h) := by
  classical
  obtain ⟨l₀, hg0, hgl, hg⟩ := exists_redGood hsp hxy hV I₀
  obtain ⟨Q', hQ⟩ := exists_lineBundle_redSys hsp hxy hV hg0 hg (mem_sub_of_isVeryAmpleBy hV l₀)
  set g := h l₀ with hgdef
  set ρ : Ω → K' := fun q => redAt k x y (q / g) with hρ
  have hloc : ∀ {j : Fin (r + 1)} (_ : redAt k x y (h j / g) ≠ 0) {c : Ω},
      c ∈ ampleRing Nb.toSubSystem 1 (h j) →
        c ∈ locAt k x y ∧ redAt k x y c ∈ ampleBase (S := k) (ρ ∘ h) j := fun {j} hr {c} hc =>
    redAt_mem_ampleBase hsp hg0 hgl hr (hV.closed j (ne_zero_of_redAt_div hsp (hgl j) hr) hc)
  have hvery : IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) := by
    refine ⟨fun l => ?_, fun I => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun I => ?_
      rw [Submodule.restrictScalars_mem, hQ]
      exact Submodule.subset_span ⟨h l, mem_sub_of_isVeryAmpleBy hV l _, rfl⟩
    · rw [hQ, redSys_sub_eq hsp hxy hV hg]; rfl
    ·
      have hσ := hgl j
      have hσr : redAt k x y (h j / g) ≠ 0 := hj
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ :=
        hV.affine j (ne_zero_of_redAt_div hsp hσ hσr)
      intro a ha
      have hE : ∀ kk, ∃ E : ℕ, redAt k x y (b' kk) ^ (E + 1) * a ∈ ampleBase (S := k) (ρ ∘ h) j := by
        intro kk
        by_cases hbr : redAt k x y (b' kk) = 0
        · refine ⟨0, ?_⟩
          rw [hbr, zero_pow (Nat.succ_ne_zero 0), zero_mul]; exact zero_mem _
        · have hbl := (hloc hσr (hb' kk)).1
          have hJ := subset_support_of_redAt_ne_zero hsp hxy hg hσ hσr I₀ hbl hbr (hbJ kk)
          let Jy : Chart y := ⟨(J kk).1, (J kk).2.1, hJ⟩
          obtain ⟨e, he, hea⟩ :=
            exists_lift_ampleChart hsp hxy hg Q' hQ hσ hσr Jy (Set.mem_iInter.mp ha Jy)
          have hel := (redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr Jy he).1
          obtain ⟨E, hEm⟩ := res_exists_pow_mul_mem_ampleRing Nb (hb' kk) (hbJ kk) (J := J kk) he
          have hm := hloc hσr hEm
          rw [(locAt_mul hsp (locAt_pow hsp hbl E).1 hel).2, (locAt_pow hsp hbl E).2, hea] at hm
          refine ⟨E, ?_⟩
          have : redAt k x y (b' kk) ^ (E + 1) * a =
              redAt k x y (b' kk) * (redAt k x y (b' kk) ^ E * a) := by ring
          rw [this]
          exact mul_mem (hloc hσr (hb' kk)).2 hm.2
      choose E hE using hE
      let T := Finset.univ.sup E + 1
      let β : Fin n → ampleBase (S := k) (ρ ∘ h) j :=
        fun kk => ⟨redAt k x y (b' kk), (hloc hσr (hb' kk)).2⟩
      let α : Fin n → ampleBase (S := k) (ρ ∘ h) j :=
        fun kk => ⟨redAt k x y (a' kk), (hloc hσr (ha' kk)).2⟩
      have hsum' : ∑ kk, α kk * β kk = 1 := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
        have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).1).2
        rw [hsum, (locAt_one hsp).2] at h2
        refine Eq.trans (Finset.sum_congr rfl fun kk _ => ?_) h2.symm
        rw [(locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).2]
        rfl
      have hspan : Ideal.span (Set.range β) = ⊤ := by
        rw [Ideal.eq_top_iff_one, ← hsum']
        exact Ideal.sum_mem _ fun kk _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨kk, rfl⟩)
      have hT := Ideal.span_pow_eq_top (Set.range β) hspan T
      let 𝔞 : Ideal (ampleBase (S := k) (ρ ∘ h) j) :=
        { carrier := {c | (c : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j}
          add_mem' := fun {u v} hu hv => by
            simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_mul] at hu hv ⊢
            exact add_mem hu hv
          zero_mem' := by
            simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact zero_mem _
          smul_mem' := fun c u hu => by
            simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_assoc] at hu ⊢
            exact mul_mem c.2 hu }
      have hle : Ideal.span ((fun c => c ^ T) '' Set.range β) ≤ 𝔞 := by
        rw [Ideal.span_le]
        rintro _ ⟨_, ⟨kk, rfl⟩, rfl⟩
        show ((β kk ^ T : ampleBase (S := k) (ρ ∘ h) j) : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j
        have hk : E kk + 1 ≤ T := Nat.succ_le_succ (Finset.le_sup (Finset.mem_univ kk))
        rw [SubmonoidClass.coe_pow, ← Nat.sub_add_cancel hk, pow_add, mul_assoc]
        exact mul_mem (pow_mem (β kk).2 _) (hE kk)
      have h1 : (1 : ampleBase (S := k) (ρ ∘ h) j) ∈ 𝔞 := hle (by rw [hT]; exact Submodule.mem_top)
      have h1' : ((1 : ampleBase (S := k) (ρ ∘ h) j) : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j := h1
      rwa [OneMemClass.coe_one, one_mul] at h1'
    ·
      have hσ := hgl j
      have hσr : redAt k x y (h j / g) ≠ 0 := hj
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ :=
        hV.affine j (ne_zero_of_redAt_div hsp hσ hσr)
      have hred : ∀ {c : Ω}, c ∈ ampleRing Nb.toSubSystem 1 (h j) →
          redAt k x y c ∈ ampleRing Q'.toSubSystem 1 ((ρ ∘ h) j) := fun hc =>
        Set.mem_iInter.mpr fun I => (redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr I
          (Set.mem_iInter.mp hc (liftChart hxy I))).2
      have hsupp : ∀ kk, redAt k x y (b' kk) ≠ 0 → (J kk).1 ⊆ support y := fun kk hbr =>
        subset_support_of_redAt_ne_zero hsp hxy hg hσ hσr I₀ (hloc hσr (hb' kk)).1 hbr (hbJ kk)
      refine ⟨n, fun kk => redAt k x y (a' kk),
        fun kk => if redAt k x y (b' kk) = 0 then 0 else redAt k x y (b' kk),
        fun kk => if hb : redAt k x y (b' kk) = 0 then I₀ else ⟨(J kk).1, (J kk).2.1, hsupp kk hb⟩,
        fun kk => hred (ha' kk), fun kk => ?_, ?_, fun kk I => ?_⟩
      · dsimp only
        split_ifs with hb
        · exact Set.mem_iInter.mpr fun I => zero_mem_ampleChart
        · exact hred (hb' kk)
      · have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).1).2
        rw [hsum, (locAt_one hsp).2] at h2
        refine Eq.trans (Finset.sum_congr rfl fun kk _ => ?_) h2.symm
        rw [(locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).2]
        dsimp only
        split_ifs with hb
        · rw [hb, mul_zero]
        · rfl
      · dsimp only
        by_cases hb : redAt k x y (b' kk) = 0
        · rw [if_pos hb, dite_eq_left hb]
          exact ⟨1, by rw [pow_one, zero_mul]; exact zero_mem_ampleChart⟩
        · rw [if_neg hb, dite_eq_right hb]
          obtain ⟨e, he⟩ := hbJ kk (liftChart hxy I)
          have hbl := (hloc hσr (hb' kk)).1
          have hJ := hsupp kk hb
          have hf := (res_isHomogeneous_prod_X (S := k) I.1).pow (J kk).1.card
          have hs : ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card).IsHomogeneous
              (I.1.card * (J kk).1.card) := by
            rw [mul_comm]; exact (res_isHomogeneous_prod_X (S := k) (J kk).1).pow I.1.card
          have hsy : aeval y ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card) ≠ 0 := by
            rw [map_pow, res_aeval_prod_X]
            exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i hi => (mem_support y).mp (hJ hi))
          have ht : xProd (liftChart hxy I) ^ (J kk).1.card / xProd (J kk) ^ (liftChart hxy I).1.card =
              aeval x ((∏ l ∈ I.1, (X l : Poly k N)) ^ (J kk).1.card) /
                aeval x ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card) := by
            rw [map_pow, map_pow, res_aeval_prod_X, res_aeval_prod_X]; rfl
          obtain ⟨-, h2⟩ := redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr I he
          rw [ht, (locAt_mul hsp (locAt_pow hsp hbl e).1 (mem_locAt hf hs hsy)).2,
            (locAt_pow hsp hbl e).2, redAt_eq hsp hf hs hsy, map_pow, map_pow, res_aeval_prod_X,
            res_aeval_prod_X] at h2
          exact ⟨e, h2⟩

  have hdim : funField (k := k) y = funField (k := k) (ρ ∘ h) := by
    obtain ⟨i₀, hi₀⟩ := I₀.2.1
    have hy₀ : y i₀ ≠ 0 := (mem_support y).mp (I₀.2.2 hi₀)
    have haeval : ∀ p : Poly k N, aeval (fun l => y l / y i₀) p ∈ funField (k := k) y := fun p =>
      MvPolynomial.induction_on (motive := fun p => aeval (fun l => y l / y i₀) p ∈ funField (k := k) y) p
        (fun c => by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ c)
        (fun p q hp hq => by rw [map_add]; exact add_mem hp hq)
        (fun p l hp => by
          rw [map_mul, aeval_X]
          exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i₀, l, hy₀, rfl⟩))
    have hredF : ∀ {c : Ω}, c ∈ locAt k x y → redAt k x y c ∈ funField (k := k) y := by
      rintro _ ⟨f, s, e, hf, hs, hsy, rfl⟩
      rw [redAt_eq hsp hf hs hsy, ← div_div_div_cancel_right₀ (pow_ne_zero e hy₀),
        ← aeval_div_of_isHomogeneous hf i₀, ← aeval_div_of_isHomogeneous hs i₀]
      exact div_mem (haeval f) (haeval s)
    apply le_antisymm
    · have hg1' : redAt k x y (g / g) ≠ 0 := by
        rw [div_self hg0, (locAt_one hsp).2]; exact one_ne_zero
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ := hV.affine l₀ hg0
      have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hg1' (ha' kk)).1 (hloc hg1' (hb' kk)).1).1).2
      rw [hsum, (locAt_one hsp).2] at h2
      have hne : ∑ kk, redAt k x y (a' kk * b' kk) ≠ 0 := by rw [← h2]; exact one_ne_zero
      obtain ⟨kk, -, hkk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      rw [(locAt_mul hsp (hloc hg1' (ha' kk)).1 (hloc hg1' (hb' kk)).1).2] at hkk
      have hbr : redAt k x y (b' kk) ≠ 0 := right_ne_zero_of_mul hkk
      have hbl := (hloc hg1' (hb' kk)).1
      have hJ := subset_support_of_redAt_ne_zero hsp hxy hg (hgl l₀) hg1' I₀ hbl hbr (hbJ kk)
      obtain ⟨c, hc⟩ := (J kk).2.1
      have hyc : y c ≠ 0 := (mem_support y).mp (hJ hc)
      have hBF : ampleBase (S := k) (ρ ∘ h) l₀ ≤ (funField (k := k) (ρ ∘ h)).toSubalgebra := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨l, rfl⟩
        exact IntermediateField.subset_adjoin _ _ ⟨l₀, l, hg1', rfl⟩
      have hbF : redAt k x y (b' kk) ∈ funField (k := k) (ρ ∘ h) := hBF (hloc hg1' (hb' kk)).2
      have hratio : ∀ m, y m / y c ∈ funField (k := k) (ρ ∘ h) := by
        intro m
        have hmc : x m / x c ∈ chartRing k x (J kk) :=
          ⟨X m, X c, 1, X_mem_monos hc, isHomogeneous_X k m, isHomogeneous_X k c, by simp⟩
        obtain ⟨E, hE⟩ := res_exists_pow_mul_mem_ampleRing Nb (hb' kk) (hbJ kk)
          (res_chartRing_sub_ampleChart hmc)
        have hm := hloc hg1' hE
        have hsy : aeval y (X c : Poly k N) ≠ 0 := by rw [aeval_X]; exact hyc
        have hmcl : x m / x c ∈ locAt k x y := by
          have := mem_locAt (x := x) (isHomogeneous_X k m) (isHomogeneous_X k c) hsy
          simpa only [aeval_X] using this
        have hmcr : redAt k x y (x m / x c) = y m / y c := by
          have := redAt_eq hsp (isHomogeneous_X k m) (isHomogeneous_X k c) hsy
          simpa only [aeval_X] using this
        rw [(locAt_mul hsp (locAt_pow hsp hbl E).1 hmcl).2, (locAt_pow hsp hbl E).2, hmcr] at hm
        have hF := hBF hm.2
        have hbE : redAt k x y (b' kk) ^ E ≠ 0 := pow_ne_zero _ hbr
        have : y m / y c = (redAt k x y (b' kk) ^ E * (y m / y c)) / redAt k x y (b' kk) ^ E := by
          field_simp
        rw [this]
        exact div_mem hF (pow_mem hbF E)
      rw [funField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, i', hi, rfl⟩
      rw [← div_div_div_cancel_right₀ hyc (y i') (y i)]
      exact div_mem (hratio i') (hratio i)
    · rw [funField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, i', -, rfl⟩
      exact div_mem (hredF (hgl i')) (hredF (hgl i))
  refine ⟨Q', ρ, restrictData_redSys hsp hxy hg Q' hQ, hvery, ?_⟩
  rw [dimCl, dimCl, hdim]

theorem Restriction.proof : Restriction.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hV pp _ _ _ j hj _ K' _ _ ψ _ hxy
  have hsp := primeOf_le_primeOf_of_algHom hj ψ
  have hyj : (fun i => ψ (ratio hj i)) j ≠ 0 := by
    show ψ (ratio hj j) ≠ 0
    rw [algHom_ratio_self]; exact one_ne_zero
  exact exists_restrictData_isVeryAmpleBy hsp hxy (singleChart hyj) Nb h hV

end

end GroundTheory.Heights₂.Heights.Kleiman
end

