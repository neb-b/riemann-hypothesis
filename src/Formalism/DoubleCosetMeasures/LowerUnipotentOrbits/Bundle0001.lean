module

public import Formalism.DoubleCosetMeasures.Statement

@[expose] public section

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
section
set_option maxHeartbeats 400000

noncomputable section

open Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := by
  intro K _ n x y
  exact ⟨fun hx hy => isLowUni_mul K hx hy, fun hx hy => isUpUni_mul K hx hy,
    fun hx => ⟨isLowUni_inv K hx, isLowUni_det K hx⟩,
    fun hx => ⟨isUpUni_inv K hx, isUpUni_det K hx⟩⟩

section Simple

variable {K : Type} [CommRing K] {n : ℕ}

theorem low_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) (hy : IsLowUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) ⟨j.val + 1, h⟩ j = x ⟨j.val + 1, h⟩ j + y ⟨j.val + 1, h⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hy.2 j, hx.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : y k j = 0 := hy.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : x ⟨j.val + 1, h⟩ k = 0 := hx.1 (by simpa using hlt)
      simp [this]

theorem up_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) (hy : IsUpUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) j ⟨j.val + 1, h⟩ = x j ⟨j.val + 1, h⟩ + y j ⟨j.val + 1, h⟩ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hx.2 j, hy.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : x j k = 0 := hx.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : y k ⟨j.val + 1, h⟩ = 0 := hy.1 (by simpa using hlt)
      simp [this]

end Simple

theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := by
  intro K _ n x y
  constructor
  · intro hx hy
    unfold sLow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact low_simple_entry hx hy j h
    · simp [dif_neg h]
  · intro hx hy
    unfold sUp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact up_simple_entry hx hy j h
    · simp [dif_neg h]

section Int

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem isInt_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hB : IsInt R B) :
    IsInt R (A * B) := by
  intro a b
  rw [Matrix.mul_apply]
  exact R.sum_mem fun k _ => R.mul_mem (hA a k) (hB k b)

theorem isInt_adjugate {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) :
    IsInt R A.adjugate := by
  let A' : Matrix (Fin n) (Fin n) R := fun a b => ⟨A a b, hA a b⟩
  have hmap : R.subtype.mapMatrix A' = A := by ext a b; rfl
  intro a b
  rw [← hmap, ← RingHom.map_adjugate]
  exact (A'.adjugate a b).2

theorem isInt_inv {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hd : A.det = 1) :
    IsInt R A⁻¹ := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  exact isInt_adjugate R hA

end Int

theorem intInv : Formalism.DoubleCosetMeasures.IntInv := by
  intro K _ R n a b Z ha hb haR hbR
  have hda : IsUnit a.det := by simp [isLowUni_det K ha]
  have hdb : IsUnit b.det := by simp [isUpUni_det K hb]
  constructor
  · intro h
    have hZ : Z = a⁻¹ * (a * Z * b) * b⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv b hdb, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]
    rw [hZ]
    exact isInt_mul R (isInt_mul R (isInt_inv R haR (isLowUni_det K ha)) h)
      (isInt_inv R hbR (isUpUni_det K hb))
  · intro h
    exact isInt_mul R (isInt_mul R haR h) hbR

section Lat

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

end Lat

end Formalism.DoubleCosetMeasures.P
end
end

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
section
noncomputable section

open MeasureTheory Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

section SlopeTestRemainingChoices

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem isOpen_isInt_set (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} := by
  have hset : {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} =
      (⋂ a, ⋂ b, {g : GL (Fin n) K | (g : Matrix (Fin n) (Fin n) K) a b ∈ R}) ∩
      (⋂ a, ⋂ b, {g : GL (Fin n) K | ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R}) := by
    ext g
    simp [IsInt, Set.mem_iInter]
  rw [hset]
  apply IsOpen.inter
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_val.matrix_elem a b)
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_coe_inv.matrix_elem a b)

theorem isOpen_intSub (R : Subring K) (hR : IsOpen (R : Set K)) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) : IsOpen (intSub R H : Set H) := by
  exact (isOpen_isInt_set R hR n).preimage continuous_subtype_val

end SlopeTestRemainingChoices

theorem sLow_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sLow x ∈ R := by
  unfold sLow
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem

theorem sUp_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sUp x ∈ R := by
  unfold sUp
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem

theorem phi_inv (hIntInv : IntInv) (hIsoInv : IsoInv) (hSA : SimpleAdd)
    {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    ∀ a ∈ intSub R (lowW K s t), ∀ b ∈ intSub R (upUniG K s.sum), ∀ x : lowW K s t,
      ∀ y : upUniG K s.sum, phi R s t ψ C e lam (a * x, y * b) = phi R s t ψ C e lam (x, y) := by
  intro a ha b hb x y
  have haI : IsInt R (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := ha.1
  have hbI : IsInt R (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := hb.1
  have haL : IsLowUni (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := a.2.1
  have hxL : IsLowUni (((x : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := x.2.1
  have hbU : IsUpUni (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := b.2
  have hyU : IsUpUni (((y : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := y.2
  unfold phi
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hi := hIntInv K R s.sum _ _
    (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) haL hbU haI hbI
  have hc := hIsoInv K R s.sum _ _
    (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) haL hbU haI hbI C e lam
  have hi' : IsInt R (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
       ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) ↔
      IsInt R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
       ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    simpa only [mul_assoc] using hi
  have heq : (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
       ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) =
      ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
       ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) *
      ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by simp only [mul_assoc]
  have hc' := (congrArg (fun z => Nat.card (isoSet R z C e lam)) heq).trans hc
  simp only [hi', hc', (hSA K s.sum _ _).1 haL hxL, (hSA K s.sum _ _).2 hyU hbU]
  have hpa : ψ (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) = 1 := hψ _ (sLow_mem R _ haI)
  have hpb : ψ (sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) = 1 := hψ _ (sUp_mem R _ hbI)
  rw [show sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + (sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
      (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) + (sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) by abel]
  simp only [AddChar.map_add_eq_mul, hpa, hpb, one_mul]
  split_ifs with h h <;> simp_all

theorem bbFinite_of : IntTwoSided → IntInv → IsoInv → SimpleAdd → BBFinite := by
  intro hTS hII hIso hSA K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ C _ _ e lam hcs
  have h := hTS (lowW K s t) (upUniG K s.sum) μ₁ μ₂ (intSub R (lowW K s t))
    (intSub R (upUniG K s.sum)) (isOpen_intSub R hR _) (isOpen_intSub R hR _) ℂ
    (phi R s t ψ C e lam) (phi_inv hII hIso hSA R s t ψ hψ C e lam) hcs
  refine ⟨h.1, ?_⟩
  rw [BB, h.2]
  congr 1

theorem bbNorm_of : BBFinite → BBNorm := by
  intro hBB K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ h1 h2 C _ _ e lam hcs
  rw [(hBB K R hR s t ψ hψ μ₁ μ₂ C e lam hcs).2, h1, h2]
  simp

end Formalism.DoubleCosetMeasures.P
end
end

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided
section
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

theorem mem_preimage_rightRel_mk {G : Type} [Group G] (K : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel K)) (x : G) :
    Quotient.mk (QuotientGroup.rightRel K) x = q ↔ x * q.out⁻¹ ∈ K := by
  conv_lhs => rw [← Quotient.out_eq q]
  rw [Quotient.eq, QuotientGroup.rightRel_apply, ← K.inv_mem_iff, mul_inv_rev, inv_inv]

theorem mem_preimage_leftQuot_mk {G : Type} [Group G] (K : Subgroup G) (q : G ⧸ K) (y : G) :
    (y : G ⧸ K) = q ↔ q.out⁻¹ * y ∈ K := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev, inv_inv]

def box {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) : Set (G₁ × G₂) :=
  ((fun x => x * p.1.out⁻¹) ⁻¹' (K₁ : Set G₁)) ×ˢ ((fun y => p.2.out⁻¹ * y) ⁻¹' (K₂ : Set G₂))

def clsTS {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (z : G₁ × G₂) : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) :=
  (Quotient.mk _ z.1, (z.2 : G₂ ⧸ K₂))

theorem mem_box_iff {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) (z : G₁ × G₂) :
    z ∈ box K₁ K₂ p ↔ clsTS K₁ K₂ z = p := by
  simp only [box, clsTS, Prod.ext_iff, Set.mem_prod, Set.mem_preimage, SetLike.mem_coe,
    mem_preimage_rightRel_mk, mem_preimage_leftQuot_mk]

theorem cls_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) :
    clsTS K₁ K₂ (p.1.out, p.2.out) = p := by
  simp only [clsTS, Quotient.out_eq, QuotientGroup.out_eq']

theorem inv_eq_cls {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    {E : Type} (f : G₁ × G₂ → E)
    (hf : ∀ a ∈ K₁, ∀ b ∈ K₂, ∀ x : G₁, ∀ y : G₂, f (a * x, y * b) = f (x, y)) (z : G₁ × G₂) :
    f z = f ((clsTS K₁ K₂ z).1.out, (clsTS K₁ K₂ z).2.out) := by
  have h1 := (mem_preimage_rightRel_mk K₁ (Quotient.mk (QuotientGroup.rightRel K₁) z.1) z.1).1 rfl
  have h2 := (mem_preimage_leftQuot_mk K₂ (z.2 : G₂ ⧸ K₂) z.2).1 rfl
  have h := hf _ h1 _ h2 (Quotient.mk (QuotientGroup.rightRel K₁) z.1).out (z.2 : G₂ ⧸ K₂).out
  simp only [inv_mul_cancel_right, mul_inv_cancel_left] at h
  simpa [clsTS] using h

theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := by
  classical
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ μ₁ μ₂ _ _ _ _ K₁ K₂ hK₁ hK₂ E _ _ _ f hf hcs
  set g : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) → E := fun p => f (p.1.out, p.2.out) with hg
  have hopen : ∀ p, IsOpen (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_const _)).prod (hK₂.preimage (continuous_const_mul _))
  have hmeas : ∀ p, MeasurableSet (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_const _)).measurableSet.prod
      (hK₂.preimage (continuous_const_mul _)).measurableSet
  have hfg : ∀ z, f z = g (clsTS K₁ K₂ z) := fun z => inv_eq_cls K₁ K₂ f hf z
  have hfin : (Function.support g).Finite := by
    obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun p => box K₁ K₂ p) hopen
      (fun z _ => Set.mem_iUnion.2 ⟨clsTS K₁ K₂ z, (mem_box_iff K₁ K₂ _ z).2 rfl⟩)
    refine t.finite_toSet.subset fun p hp => ?_
    have hz : ((p.1.out, p.2.out) : G₁ × G₂) ∈ tsupport f := subset_tsupport f hp
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hpi := (mem_box_iff K₁ K₂ i _).1 hzi
    rw [cls_out] at hpi
    rw [hpi]
    exact hi
  refine ⟨hfin, ?_⟩
  change ∫ p, f p ∂(μ₁.prod μ₂) = ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
    ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p
  set S := hfin.toFinset with hS
  have hsum : ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p =
      ∑ p ∈ S, ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    rw [hS, Set.Finite.coe_toFinset]
    intro h
    apply hp
    simp [h]
  rw [hsum]
  have hdecomp : f = fun z => ∑ p ∈ S, (box K₁ K₂ p).indicator (fun _ => g p) z := by
    funext z
    have hind : ∀ p, (box K₁ K₂ p).indicator (fun _ => g p) z =
        if clsTS K₁ K₂ z = p then g p else 0 := by
      intro p
      simp only [Set.indicator, mem_box_iff]
    simp only [hind, Finset.sum_ite_eq]
    rw [hfg z]
    split_ifs with h
    · rfl
    · rw [hS, Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h
  have hbox : ∀ p, (μ₁.prod μ₂) (box K₁ K₂ p) = μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) := by
    intro p
    rw [box, Measure.prod_prod, measure_preimage_mul_right, measure_preimage_mul]
  have hpiece : ∀ p, ∫ z, (box K₁ K₂ p).indicator (fun _ => g p) z ∂(μ₁.prod μ₂) =
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    intro p
    rw [integral_indicator_const _ (hmeas p), Measure.real, hbox p, ENNReal.toReal_mul]
  by_cases hint : Integrable f (μ₁.prod μ₂)
  · have hI : ∀ p ∈ S, Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      intro p _
      refine (hint.indicator (hmeas p)).congr (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ box K₁ K₂ p
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hfg z, (mem_box_iff K₁ K₂ p z).1 hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    conv_lhs => rw [hdecomp]
    rw [MeasureTheory.integral_finsetSum S hI]
    exact Finset.sum_congr rfl fun p _ => hpiece p
  · rw [integral_undef hint]
    have hex : ∃ p ∈ S, ¬ Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      by_contra hne
      push_neg at hne
      apply hint
      rw [hdecomp]
      exact MeasureTheory.integrable_finsetSum S hne
    obtain ⟨p, -, hnp⟩ := hex
    have htop : μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) = ⊤ := by
      by_contra hne
      apply hnp
      rw [integrable_indicator_iff (hmeas p)]
      exact integrableOn_const (by rw [hbox p]; exact hne)
    have h0 : (μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal = 0 := by
      rw [← ENNReal.toReal_mul, htop, ENNReal.toReal_top]
    simp [h0]

end Formalism.DoubleCosetMeasures.P
end
end

