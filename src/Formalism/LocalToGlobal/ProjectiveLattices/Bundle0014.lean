module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002
public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]


variable (Xo c) in
def supR (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : Rul Xo c) : ℝ :=
  supAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f


variable (Xo c) in
def SupBdd (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    Prop :=
  ∀ σ, BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f


variable (Xo c) in
def PTNe : Prop := ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), (PT (Ω := Om Z) σ).Nonempty

theorem ptNe_of_fnFG (hfg : FnFG Xo c) : PTNe Xo c := fun Z σ => exists_embedding_over (hfg Z) σ

def ValAtCx (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ‖P (evC h Z f)‖ = cabs (evR Xo c f (yP Z P))

def NZSome (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∃ Z, evC h Z f ≠ 0

section Pf

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem meanK_mono' {K : Type} [Field K] [NumberField K] {F G : (K →+* ℂ) → ℝ} (hFG : ∀ sg, F sg ≤ G sg) :
    meanK F ≤ meanK G := by
  unfold meanK
  gcongr with sg _
  exact hFG sg

theorem exZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (i : Ix Dw) : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
  cases i <;> rfl

theorem nrmC_valC_le (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P ≤ supR Xo c fn (sgOf P) a n f := by
  have hb := hB (sgOf P)
  unfold BddAt at hb
  have hle := le_ciSup hb (yP Z P)
  have hc : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  have heq : nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P =
      ptNorm (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
    unfold nrmC ptNorm
    rw [hc, hcx Z P a n f hS]
    simp only [exZ_wtZ, zpow_neg, zpow_natCast, inv_pow] <;> rfl
  rw [heq]
  exact hle

theorem log_supN_le (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  have hbd : ∀ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2 ≤ supR Xo c fn σ a n f := by
    rintro ⟨Z, P, hP⟩
    have hσ : sgOf P = σ := hP
    have key := nrmC_valC_le (h := h) (yP := yP) hcx hS hB Z P
    rw [hσ] at key
    exact key
  obtain ⟨Z0, hZ0⟩ := hN
  obtain ⟨P0, hP0⟩ := hPT Z0 σ
  have hpos : 0 < nrmC fn (yP Z0) (wtZ a n) (valC h a n f Z0) P0 := by
    have hc : (valC h a n f Z0).coeff (wtZ a n) = evC h Z0 f := by
      unfold valC
      simp
    unfold nrmC
    rw [hc]
    apply mul_pos
    · exact norm_pos_iff.mpr ((map_ne_zero P0).mpr hZ0)
    · apply Finset.prod_pos
      intro i _
      exact zpow_pos (abs_pos.mpr (hfn _ _ i)) _
  have hne : Nonempty (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) := ⟨⟨Z0, P0, hP0⟩⟩
  have hB' : BddAbove (Set.range fun p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := ⟨_, Set.forall_mem_range.mpr hbd⟩
  apply Real.log_le_log
  · exact lt_of_lt_of_le hpos (le_ciSup hB' ⟨Z0, P0, hP0⟩)
  · exact ciSup_le hbd

end Pf

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Fin

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def DivFin : Prop := ∀ (Z : Comp Xo c) (r : Om Z), r ≠ 0 → {v | d.admitted Z v ∧ v r ≠ 0}.Finite

def FrShFin (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ Z : Comp Xo c, {v | d.admitted Z v ∧ δ Z v ≠ 0}.Finite

theorem lawA3'_of (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (hD : DivFin d) (hF : FrShFin d δ) : LawA3' d := by
  intro Z G f hf hf0
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf0 (zero_smul _ _)
  have hcoeff : (a • (AddMonoidAlgebra.single G (1 : Om Z))).coeff G = a := by
    first
      | simp
      | simp [AddMonoidAlgebra.smul_single']
      | (rw [AddMonoidAlgebra.smul_single', mul_one]; rfl)
  refine ((hD Z a ha).union (hF Z)).subset ?_
  rintro v ⟨hadm, hne⟩
  rw [hord] at hne
  unfold ordC at hne
  rw [hcoeff] at hne
  by_cases hv : v a = 0
  · refine Or.inr ⟨hadm, fun hδ => hne ?_⟩
    rw [hv, hδ]
    have hz : frW (0 : Ix Dw → ℤ) G = 0 := by
      unfold frW
      simp
    rw [hz]
    rfl
  · exact Or.inl ⟨hadm, hv⟩

end Fin

section Data

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem lawA3'_dataOf
    (hD : DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hF : FrShFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) δ) :
    LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA3'_of _ δ (fun _ _ => rfl) hD hF

end Data

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def KapFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (kap Z)).FG

def KapTrdeg (d : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = d

theorem fnFG_of (h : KapFG Xo c) : FnFG Xo c := by
  intro Z
  classical
  obtain ⟨s, hs⟩ := h Z
  have hfin : (Set.range fun i : FlagVar Dw =>
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X i)).Finite := Set.finite_range _
  refine ⟨s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset, ?_⟩
  set K := IntermediateField.adjoin c.F
    ((s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset : Finset (Om Z)) : Set (Om Z)) with hK
  have hC : ∀ a : kap Z, algebraMap (kap Z) (Om Z) a ∈ K := by
    intro a
    have ha : a ∈ IntermediateField.adjoin c.F (s : Set (kap Z)) := by
      rw [hs]
      exact IntermediateField.mem_top
    have h1 : IsScalarTower.toAlgHom c.F (kap Z) (Om Z) a ∈
        (IntermediateField.adjoin c.F (s : Set (kap Z))).map (IsScalarTower.toAlgHom c.F (kap Z) (Om Z)) :=
      by
        first
          | exact ⟨a, ha, rfl⟩
          | (rw [← SetLike.mem_coe, IntermediateField.coe_map]; exact Set.mem_image_of_mem _ ha)
    rw [IntermediateField.adjoin_map] at h1
    refine IntermediateField.adjoin.mono _ _ _ ?_ h1
    rintro _ ⟨b, hb, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hP : ∀ q : MvPolynomial (FlagVar Dw) (kap Z),
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) q ∈ K := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC a
    next p₁ p₂ h₁ h₂ =>
      rw [map_add (f := _)]
      exact K.add_mem h₁ h₂
    next p₁ i h₁ =>
      rw [map_mul]
      refine K.mul_mem h₁ (IntermediateField.subset_adjoin c.F _ ?_)
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨i, rfl⟩))
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) x
  dsimp only
  rw [IsFractionRing.mk'_eq_div]
  exact K.div_mem (hP p₁) (hP p₂)

private lemma isAlgebraic_frac_lemma {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (x : K) : IsAlgebraic A x := by
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  dsimp only
  have hq : algebraMap A K (q : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
  refine ⟨Polynomial.C (q : A) * Polynomial.X - Polynomial.C p, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun f : Polynomial A => f.coeff 1) h0
    simp at h1
    try exact nonZeroDivisors.ne_zero q.2 h1
  · rw [IsFractionRing.mk'_eq_div]
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [mul_div_cancel₀ _ hq, sub_self]

theorem fnTrdeg_of (d : ℕ) (h : KapTrdeg Xo c d) : FnTrdeg Xo c (d + Nat.card (FlagVar Dw)) := by
  intro Z
  haveI h1 : FaithfulSMul (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (kap Z) (MvPolynomial (FlagVar Dw) (kap Z))).injective
  haveI h2 : FaithfulSMul (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z))
  haveI h3 : FaithfulSMul c.F (kap Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap c.F (kap Z)).injective
  haveI h4 : FaithfulSMul (kap Z) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (kap Z) (Om Z)).injective
  have e1 : Algebra.trdeg (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) = Cardinal.mk (FlagVar Dw) := by
    first
      | (rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id])
      | (rw [Algebra.trdeg_mvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq, Cardinal.lift_id])
      | (rw [MvPolynomial.lift_trdeg, Cardinal.lift_id])
      | (rw [Algebra.trdeg_MvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq_cardinalMk, Cardinal.lift_id])
  have e2 : Algebra.trdeg (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) = 0 := by
    unfold Algebra.trdeg
    refine le_antisymm (ciSup_le' fun s => ?_) zero_le
    refine (Cardinal.mk_eq_zero_iff.mpr ⟨fun x => ?_⟩).le
    exact s.2.transcendental x (isAlgebraic_frac_lemma _)
  have hcard : Cardinal.mk (FlagVar Dw) = ((Nat.card (FlagVar Dw) : ℕ) : Cardinal) := by
    first
      | exact Nat.cast_card.symm
      | simp [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have T1 := lift_trdeg_add_eq (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z)
  have T2 := lift_trdeg_add_eq c.F (kap Z) (Om Z)
  simp only [Cardinal.lift_id] at T1 T2
  show Algebra.trdeg c.F (Om Z) = ((d + Nat.card (FlagVar Dw) : ℕ) : Cardinal)
  rw [← T2, h Z, ← T1, e1, e2, add_zero, hcard, Nat.cast_add]

end Formalism.L2.Pj

end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LawA13OfContinuous
section
noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Gen

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def A13ContinuousOffNull : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1),
      MeasurableSet S ∧ d.sphMeasure S = 0 ∧
      ContinuousOn (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
        ∑ᶠ P ∈ d.ST Z sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
          Real.log (d.nrm Z G f P)) Sᶜ

theorem lawA13_of_continuous (hc : A13ContinuousOffNull d) : A13Measurable d := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hcont⟩ := hc Z sg hf hf0
  have h1 := hcont.aemeasurable (μ := d.sphMeasure) hSm.compl
  have h2 : d.sphMeasure.restrict Sᶜ = d.sphMeasure :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hS0)
  rw [h2] at h1
  exact h1

end Gen

def NrmContOff (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ContinuousOn (fun t : Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1 =>
        ∑ᶠ P ∈ {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j, (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
            P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0},
          Real.log (nrmC fn (yP Z) G f P)) Sᶜ

theorem lawA13_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hc : NrmContOff h fn yP Dd N uL wR jc) :
    A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA13_of_continuous _ hc

end Formalism.L2.Pj
end
end

