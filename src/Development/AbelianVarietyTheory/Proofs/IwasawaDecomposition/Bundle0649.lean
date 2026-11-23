module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotInternalOfRead
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitive
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eq_one_of_smul_eq_of_orbFun_evalZ_eq_one :
    ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀]
      (v : LinearMap.BilinForm ℤ X₀) (hv : v ∈ balForms bar X₀), IsPrim bar (⟨v, hv⟩ : balForms bar X₀) →
      ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X),
        (OrbMark.orbFun O w0 v).evalZ β = 1 →
        ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar w0 X₀ _ _ v hv hp X _ _ _ β hβ k β' hk
  obtain ⟨τ, f, -, hf, -, H⟩ := _root_.GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one w0 v β hβ
  have hval : ∀ (x₀ y₀ : X₀), ∃ x y, v x₀ y₀ = β x y := by
    intro x₀ y₀
    obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
    obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
    exact ⟨x, y, (H x y x₀ y₀ hx.symm hy.symm).symm⟩
  have hβ' : ∀ x y, (k : ℤ) * β' x y = β x y := fun x y => by rw [← hk]; simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have hv0 : v = 0 := LinearMap.ext₂ fun x₀ y₀ => by
      obtain ⟨x, y, e⟩ := hval x₀ y₀
      rw [e, ← hβ']
      simp
    exact zero_ne_one (hp 0 0 (Subtype.ext (by simp [hv0])))
  · have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hcan : ∀ {a b : ℤ}, (k : ℤ) * a = k * b → a = b := fun h => mul_left_cancel₀ hkz h
    have hl : ∀ x, f x = 0 → ∀ y, β' x y = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H x y 0 y₀ (by rw [hx]; rfl) hy₀
      apply hcan
      rw [hβ', e]
      simp
    have hr : ∀ x, f x = 0 → ∀ y, β' y x = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H y x y₀ 0 hy₀ (by rw [hx]; rfl)
      apply hcan
      rw [hβ', e]
      simp
    obtain ⟨ζ₁, hζ₁⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β' hl hr
    let m : X₀ →ₗ[ℤ] X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
      (CarDim.orad v : Submodule O X₀).mkQ.toAddMonoidHom.toIntLinearMap
    let ζ : LinearMap.BilinForm ℤ X₀ := ζ₁.compl₁₂ m m
    have hζ : ∀ x₀ y₀, (k : ℤ) * ζ x₀ y₀ = v x₀ y₀ := by
      intro x₀ y₀
      obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
      obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
      have e1 : ζ x₀ y₀ = β' x y := by
        show ζ₁ (Submodule.Quotient.mk x₀) (Submodule.Quotient.mk y₀) = _
        rw [← hx, ← hy, hζ₁]
      rw [e1, hβ', H x y x₀ y₀ hx.symm hy.symm]
    have hmem : ζ ∈ balForms bar X₀ := by
      refine ⟨fun y z => hcan ?_, fun a y z => hcan ?_⟩
      · rw [hζ, hζ, hv.1]
      · rw [hζ, hζ, hv.2]
    refine hp k ⟨ζ, hmem⟩ (Subtype.ext (LinearMap.ext₂ fun x₀ y₀ => ?_))
    change v x₀ y₀ = ((k • ζ : LinearMap.BilinForm ℤ X₀)) x₀ y₀
    rw [LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul, hζ]

end OrbMark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

lemma rel_mem_J {p q k : ℕ} (hk : 1 ≤ k) : rel k ∈ J p q :=
  Ideal.subset_span (Or.inl ⟨k, hk, rfl⟩)

lemma X_zero_sub_one_mem_J {p q : ℕ} (b : Bool) :
    (X (b, 0) - 1 : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inl ⟨b, rfl⟩))

lemma X_true_mem_J {p q k : ℕ} (hk : p < k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))

lemma X_false_mem_J {p q k : ℕ} (hk : q < k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q :=
  Ideal.subset_span (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))

lemma mem_of_neg_one_pow_mul {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} {x : MvPolynomial (Bool × ℕ) ℝ}
    (n : ℕ) (h : C ((-1 : ℝ) ^ n) * x ∈ I) : x ∈ I := by
  have := I.mul_mem_left (C ((-1 : ℝ) ^ n)) h
  rwa [← mul_assoc, ← C_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1, one_mul] at this

lemma X_mul_X_mem_J {p q : ℕ} (hpq : 1 ≤ p + q) :
    (X (true, p) * X (false, q) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p q := by
  have hrel := rel_mem_J (p := p) (q := q) hpq
  have hp : p ∈ Finset.range (p + q + 1) := Finset.mem_range.2 (by omega)
  rw [rel, ← Finset.add_sum_erase _ _ hp] at hrel
  have hrest : (∑ a ∈ (Finset.range (p + q + 1)).erase p,
      C ((-1 : ℝ) ^ (p + q - a)) * X (true, a) * X (false, p + q - a)) ∈ J p q := by
    refine Ideal.sum_mem _ fun a ha => ?_
    have hap := Finset.ne_of_mem_erase ha
    rcases lt_or_gt_of_ne hap with h | h
    · exact (J p q).mul_mem_left _ (X_false_mem_J (by omega))
    · exact (J p q).mul_mem_right _ ((J p q).mul_mem_left _ (X_true_mem_J h))
  have := (J p q).sub_mem hrel hrest
  rw [add_sub_cancel_right, Nat.add_sub_cancel_left, mul_assoc] at this
  exact mem_of_neg_one_pow_mul q this

lemma sub_C_eval_mem {I : Ideal (MvPolynomial (Bool × ℕ) ℝ)} (v : Bool × ℕ → ℝ)
    (hv : ∀ y, X y - C (v y) ∈ I) (P : MvPolynomial (Bool × ℕ) ℝ) : P - C (eval v P) ∈ I := by
  refine MvPolynomial.induction_on (motive := fun P => P - C (eval v P) ∈ I) P (fun a => ?_) (fun P Q hP hQ => ?_) (fun P y hP => ?_)
  · simp
  · have := I.add_mem hP hQ
    convert this using 1
    simp only [map_add (f := _)]; ring
  · have := I.add_mem (I.mul_mem_right (X y) hP) (I.mul_mem_left (C (eval v P)) (hv y))
    convert this using 1
    simp only [map_mul, eval_X]; ring

lemma X_false_mem_J_zero {q k : ℕ} (hk : 1 ≤ k) : (X (false, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J 0 q := by
  have hrel := rel_mem_J (p := 0) (q := q) hk
  rw [rel, Finset.sum_range_succ'] at hrel
  have hrest : (∑ i ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - (i + 1))) * X (true, i + 1) * X (false, k - (i + 1))) ∈ J 0 q :=
    Ideal.sum_mem _ fun i _ => (J 0 q).mul_mem_right _ ((J 0 q).mul_mem_left _ (X_true_mem_J (by omega)))
  have h0 := (J 0 q).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_zero] at h0
  have h1 := (J 0 q).sub_mem h0
    ((J 0 q).mul_mem_right (C ((-1 : ℝ) ^ k) * X (false, k)) (X_zero_sub_one_mem_J true))
  refine mem_of_neg_one_pow_mul k ?_
  convert h1 using 1
  ring

lemma X_true_mem_J_zero {p k : ℕ} (hk : 1 ≤ k) : (X (true, k) : MvPolynomial (Bool × ℕ) ℝ) ∈ J p 0 := by
  have hrel := rel_mem_J (p := p) (q := 0) hk
  rw [rel, Finset.sum_range_succ] at hrel
  have hrest : (∑ a ∈ Finset.range k,
      C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)) ∈ J p 0 :=
    Ideal.sum_mem _ fun a ha => (J p 0).mul_mem_left _ (X_false_mem_J (by simp at ha; omega))
  have h0 := (J p 0).sub_mem hrel hrest
  rw [add_sub_cancel_left, Nat.sub_self, pow_zero, C_1, one_mul] at h0
  have h1 := (J p 0).sub_mem h0 ((J p 0).mul_mem_left (X (true, k)) (X_zero_sub_one_mem_J false))
  convert h1 using 1
  ring

lemma hv_zero_left (q : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J 0 q := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := 0) (q := q) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J_zero hk
    · exact X_true_mem_J hk

lemma hv_zero_right (p : ℕ) (y : Bool × ℕ) :
    X y - C (if y.2 = 0 then (1 : ℝ) else 0) ∈ J p 0 := by
  obtain ⟨b, k⟩ := y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using X_zero_sub_one_mem_J (p := p) (q := 0) b
  · simp only [show k ≠ 0 by omega, if_false, C_0, sub_zero]
    cases b
    · exact X_false_mem_J hk
    · exact X_true_mem_J_zero hk

lemma base_left (q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J 0 q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis 0 q) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_left q) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hpow : (1 : MvPolynomial (Bool × ℕ) ℝ) - X (true, 0) ^ q ∈ J 0 q := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (X (true, 0) : MvPolynomial (Bool × ℕ) ℝ) 1 q
    rw [one_pow] at hd
    have := (J 0 q).mul_mem_right d (X_zero_sub_one_mem_J true)
    rw [← hd] at this
    simpa using (J 0 q).neg_mem this
  have hdecomp : h = (h - C c + C c * (1 - X (true, 0) ^ q)) + c • X (true, 0) ^ q := by
    rw [smul_eq_C_mul]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [Submodule.restrictScalars_mem]
    exact (J 0 q).add_mem h1 ((J 0 q).mul_mem_left _ hpow)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma base_right (p : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ) :
    h ∈ (J p 0).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p 0) := by
  have h1 := sub_C_eval_mem (fun y => if y.2 = 0 then (1 : ℝ) else 0) (hv_zero_right p) h
  set c := eval (fun y : Bool × ℕ => if y.2 = 0 then (1 : ℝ) else 0) h
  have hdecomp : h = (h - C c) + c • X (true, p) ^ 0 := by
    rw [pow_zero, smul_eq_C_mul, mul_one]; ring
  rw [hdecomp]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rwa [Submodule.restrictScalars_mem]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))

lemma J_le_succ_left (p q : ℕ) :
    J p q ≤ J (p + 1) q ⊔ Ideal.span {(X (true, p + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · rcases Nat.lt_or_ge (p + 1) k with h | h
    · exact Ideal.mem_sup_left (X_true_mem_J h)
    · obtain rfl : k = p + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_left (X_false_mem_J hk)

lemma J_le_succ_right (p q : ℕ) :
    J p q ≤ J p (q + 1) ⊔ Ideal.span {(X (false, q + 1) : MvPolynomial (Bool × ℕ) ℝ)} := by
  refine Ideal.span_le.2 ?_
  rintro f (⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact Ideal.mem_sup_left (rel_mem_J hk)
  · exact Ideal.mem_sup_left (X_zero_sub_one_mem_J b)
  · exact Ideal.mem_sup_left (X_true_mem_J hk)
  · rcases Nat.lt_or_ge (q + 1) k with h | h
    · exact Ideal.mem_sup_left (X_false_mem_J h)
    · obtain rfl : k = q + 1 := by omega
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

lemma wt_add_single (d : Bool × ℕ →₀ ℕ) (y : Bool × ℕ) :
    wt (d + Finsupp.single y 1) = wt d + y.2 := by
  unfold wt
  rw [Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _),
    Finsupp.sum_single_index (mul_zero _), mul_one]

lemma wt_single (y : Bool × ℕ) (n : ℕ) : wt (Finsupp.single y n) = y.2 * n := by
  unfold wt
  rw [Finsupp.sum_single_index (mul_zero _)]

lemma basis_subset_succ_left (p q : ℕ) : basis p (q + 1) ⊆ basis (p + 1) (q + 1) := by
  rintro f (⟨d, hd, rfl⟩ | rfl)
  · exact Or.inl ⟨d, lt_of_lt_of_le hd (Nat.mul_le_mul_right _ (Nat.le_succ p)), rfl⟩
  · refine Or.inl ⟨Finsupp.single (true, p) (q + 1), ?_, X_pow_eq_monomial⟩
    rw [wt_single]
    show p * (q + 1) < (p + 1) * (q + 1)
    nlinarith

lemma X_mul_span_basis (p q : ℕ) {s : MvPolynomial (Bool × ℕ) ℝ}
    (hs : s ∈ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * s ∈ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    rcases hx with ⟨d, hd, rfl⟩ | rfl
    · refine Or.inl ⟨d + Finsupp.single (true, p + 1) 1, ?_, ?_⟩
      · rw [wt_add_single]
        show wt d + (p + 1) < (p + 1) * (q + 1)
        nlinarith
      · rw [add_comm d, monomial_single_add, pow_one]
    · exact Or.inr (by rw [pow_succ'])
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

lemma X_mul_mem (p q : ℕ) (f : MvPolynomial (Bool × ℕ) ℝ)
    (hf : f ∈ (J (p + 1) q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) q)) :
    X (true, p + 1) * f ∈
      (J (p + 1) (q + 1)).restrictScalars ℝ ⊔ Submodule.span ℝ (basis (p + 1) (q + 1)) := by
  obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 hf
  rw [mul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (X_mul_span_basis p q hs))
  rw [Submodule.restrictScalars_mem] at hj ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_right (p + 1) q hj)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hXX := X_mul_X_mem_J (p := p + 1) (q := q + 1) (by omega)
  have : X (true, p + 1) * (a + c * X (false, q + 1)) =
      X (true, p + 1) * a + c * (X (true, p + 1) * X (false, q + 1)) := by ring
  rw [this]
  exact (J _ _).add_mem ((J _ _).mul_mem_left _ ha) ((J _ _).mul_mem_left _ hXX)

theorem mem_rel_sup_span_low_or_top : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ),
    h ∈ (J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis p q) := by
  intro p
  induction p with
  | zero => exact base_left
  | succ p ihp =>
    intro q
    induction q with
    | zero => exact base_right (p + 1)
    | succ q ihq =>
      intro h
      obtain ⟨j, hj, s, hs, rfl⟩ := Submodule.mem_sup.1 (ihp (q + 1) h)
      rw [Submodule.restrictScalars_mem] at hj
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (J_le_succ_left p (q + 1) hj)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ?_) ?_)
        (Submodule.mem_sup_right ?_)
      · rwa [Submodule.restrictScalars_mem]
      · rw [mul_comm]; exact X_mul_mem p q c (ihq c)
      · exact Submodule.span_mono (basis_subset_succ_left p q) hs

end GlobalTheory.GrassTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.BasicNotions.TH

namespace GlobalTheory.HeightCounting.Up.StandardFrameAgreement

theorem stdFrame_iff {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) :
    R3.StdFrame hF P ↔ GlobalTheory.NJoin.StdFrame hF P := by
  have key : ∀ {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2),
      R3.swapCast h = principalLevelFrame.tensCastR h := by
    intro E _ _ F1 F2 h
    subst h
    rfl
  unfold R3.StdFrame GlobalTheory.NJoin.StdFrame principalLevelFrame.StdPsi
  rw [key hF]


end GlobalTheory.HeightCounting.Up.StandardFrameAgreement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengths
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.NRows.L0

theorem parts_positive_scalars_without_congruence_lengths : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → (Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D) ∧ GlobalTheory.NRows.LamUsed D := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost
  exact ⟨GlobalTheory.IsotSum.L0.isotInternal_of_read h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost,
    GlobalTheory.NRows.LamUsedProof.L0.main h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost⟩

end GlobalTheory.NRows.L0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posDef_im_on_ball_of_logExp : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  intro n a J _ _ Δ hΔ hpos z hz
  set U := Metric.ball (0 : Fin n → ℂ) 1 with hU
  have hcont : ∀ i j, ContinuousOn (fun w => Δ w i j) U := fun i j => (hΔ i j).continuousOn
  have hM : ContinuousOn (fun w => (Δ w).map Complex.im) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont i j)
  have hMT : ContinuousOn (fun w => ((Δ w).map Complex.im)ᵀ) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont j i)
  have hsymm : ((Δ z).map Complex.im)ᵀ = (Δ z).map Complex.im := by
    refine eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix J J ℝ)
      (fun w => ((Δ w).map Complex.im)ᵀ) (fun w => (Δ w).map Complex.im) le_rfl hMT hM ?_ z hz
    intro s hs _
    have h1 := (hpos s hs).1
    unfold Matrix.IsHermitian at h1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  intro x hx
  set q : (Fin n → ℂ) → ℂ := fun w => ∑ i, ∑ j, (x i : ℂ) * Δ w i j * (x j : ℂ) with hq
  have hqim : ∀ w, (q w).im = star x ⬝ᵥ ((Δ w).map Complex.im *ᵥ x) := by
    intro w
    simp [q, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc]
  have hqd : DifferentiableOn ℂ q U := by
    rw [hq]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hΔ i j).const_mul (x i : ℂ)).mul_const (x j : ℂ)
  have hqpos : ∀ s ∈ logDom n a, 0 < (q (logExp a s)).im := by
    intro s hs
    rw [hqim]
    exact (hpos s hs).dotProduct_mulVec_pos hx
  have hqc : ContinuousOn (fun w => (q w).im) U :=
    Complex.continuous_im.comp_continuousOn hqd.continuousOn
  have hnn : ∀ w ∈ U, 0 ≤ (q w).im := by
    intro w hw
    have := eq_on_ball_of_eq_on_logExp_image n a 1 ℝ (fun w => min (q w).im 0) (fun _ => 0)
      le_rfl ((continuous_id.min continuous_const).comp_continuousOn hqc) continuousOn_const
      (fun s hs _ => min_eq_right (hqpos s hs).le) w hw
    exact (min_eq_right_iff.1 this)
  rw [← hqim]
  rcases (hnn z hz).lt_or_eq with h | h0
  · exact h
  exfalso
  set F : (Fin n → ℂ) → ℂ := fun w => Complex.exp (Complex.I * q w) with hF
  have hFn : ∀ w, ‖F w‖ = Real.exp (-(q w).im) := by
    intro w
    simp [F, Complex.norm_exp, Complex.I_mul_re]
  have hFd : DifferentiableOn ℂ F U := (hqd.const_mul Complex.I).cexp
  have hmax : IsMaxOn (norm ∘ F) U z := by
    intro w hw
    simp only [Set.mem_setOf_eq, Function.comp, hFn, ← h0, neg_zero]
    exact Real.exp_le_exp.2 (by linarith [hnn w hw])
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : Fin n → ℂ) 1).isPreconnected
    Metric.isOpen_ball hFd hz hmax
  obtain ⟨s, hs⟩ := (GlobalTheory.ShFam.Hor.Mark.nonempty_logDom : (logDom n a).Nonempty)
  have hmem : logExp a s ∈ U := GlobalTheory.ShFam.Hor.Mark.logExp_mem hs
  have h2 := congrArg norm (heq hmem)
  simp only [Function.const_apply, hFn, ← h0, neg_zero] at h2
  have h3 : (q (logExp a s)).im = 0 := by
    have := Real.exp_injective h2
    linarith
  exact (hqpos s hs).ne' h3

end GlobalTheory
end

