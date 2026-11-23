module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LogExpAdaptedGauge
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowOfFiniteField
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbFrob

open Polynomial

theorem exists_pow_of_finite_field (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Finite F]
    [Field k] [CharP k p] (f g : F →+* k) : ∃ i : ℕ, ∀ a : F, g a = f a ^ p ^ i := by
  haveI : CharP F p := f.charP f.injective p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra F k := f.toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let g' : F →ₐ[ZMod p] k :=
    { g with commutes' := fun z =>
        RingHom.congr_fun (Subsingleton.elim (g.comp (algebraMap (ZMod p) F)) (algebraMap _ k)) z }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2
    (g'.restrictNormal' F)
  refine ⟨n, fun a => ?_⟩
  have h1 : algebraMap F k (g'.restrictNormal' F a) = g' (algebraMap F F a) :=
    AlgHom.restrictNormal_commutes g' F a
  have h2 : g'.restrictNormal' F a = a ^ p ^ (n : ℕ) := by
    rw [← hn]
    simp [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [h2, map_pow] at h1
  exact h1.symm

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

theorem comap_eq {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [IsDedekindDomain OE]
    [CharZero OE] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    (hp : ¬ IsUnit (p : R)) (w : Place p OE) {P : Ideal OE}
    (hP : ∀ Q : Ideal OE, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) (σ : OE →+* R)
    (hσ : extend σ w.e = 1) : (IsLocalRing.maximalIdeal R).comap σ = P := by
  by_contra hne
  have hpQ : (p : OE) ∈ (IsLocalRing.maximalIdeal R).comap σ := by
    rw [Ideal.mem_comap, map_natCast]; exact hp
  have hQ : ((IsLocalRing.maximalIdeal R).comap σ).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h => ?_
    rw [h, Ideal.mem_bot] at hpQ
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpQ
  let φ : w.Ow →+* R := Ideal.Quotient.lift _ (extend σ).toRingHom (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    simp [hσ])
  have hφ : ∀ a, φ (w.toOw a) = σ a := fun a => by
    show extend (p := p) σ (1 ⊗ₜ a) = σ a
    simp [extend]
  have hle : ((IsLocalRing.maximalIdeal R).comap σ).map w.toOw ≤
      (IsLocalRing.maximalIdeal R).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact ha
  rw [hP _ hQ hne, top_le_iff] at hle
  exact Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle

theorem exists_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Finite ℤ OE] (C : Type) [Field C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R],
    v.Integers R → ¬ IsUnit (p : R) → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE)
    (σ τ : OE →+* R), σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    τ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    ∃ i : ℕ, ∀ a : OE, v (algebraMap R C (τ a - σ a ^ (p ^ i))) < 1 := by
  intro p _ OE _ _ _ _ C _ v R _ _ _ hv hp w σ τ hσ hτ
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  let w' : Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨P, hPm, hpP, -, hP⟩ := GlobalTheory.OnePrime.exists_prime_under p OE w'
  have h1 := comap_eq hp w' hP σ hσ
  have h2 := comap_eq hp w' hP τ hτ
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpP
  haveI : Finite (OE ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI : Field (OE ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
    exact hp
  obtain ⟨i, hi⟩ := exists_pow_of_finite_field p (k := IsLocalRing.ResidueField R)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) σ h1.ge)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) τ h2.ge)
  refine ⟨i, fun a => ?_⟩
  have h3 : IsLocalRing.residue R (τ a) = IsLocalRing.residue R (σ a) ^ p ^ i :=
    hi (Ideal.Quotient.mk P a)
  have h4 : τ a - σ a ^ p ^ i ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h3, sub_self]
  exact lt_of_le_of_ne (hv.map_le_one _) fun h => h4 (hv.isUnit_iff_valuation_eq_one.2 h)

end GlobalTheory.EmbFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
section
open TensorProduct

namespace GlobalTheory

theorem exists_primitive_idempotent_map_eq_one {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by
  let S : Set (Ideal A) := {I | ∃ e : A, e * e = e ∧ φ e = 1 ∧ I = Ideal.span {1 - e}}
  have hS : S.Nonempty := ⟨_, 1, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, hφe, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian A A)) S hS
  have key : ∀ f : A, f * f = f → f * e = f → φ f = 1 → f = e := by
    intro f hf hfe hφf
    have hle : Ideal.span {1 - e} ≤ Ideal.span {1 - f} := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨1 - e, by linear_combination hfe⟩
    have heq : Ideal.span {1 - e} = Ideal.span {1 - f} := by
      by_contra hne
      exact hmax _ ⟨f, hf, hφf, rfl⟩ (lt_of_le_of_ne hle hne)
    have hmem : 1 - f ∈ Ideal.span {1 - e} := heq ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    linear_combination e * hc - hfe + c * he
  refine ⟨e, he, ?_, ?_, hφe⟩
  · rintro rfl
    simp at hφe
  · intro f hf hfe
    have hid : IsIdempotentElem (φ f) := by
      change φ f * φ f = φ f
      rw [← map_mul, hf]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h
    · left
      have := key (e - f) (by linear_combination he + hf - 2 * hfe)
        (by linear_combination he - hfe) (by rw [map_sub, h, hφe, sub_zero])
      linear_combination -this
    · exact Or.inr (key f hf hfe h)

theorem exists_placeU_mem_emb (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] OE) :=
    IsNoetherianRing.of_finite ℤ_[p] _
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_primitive_idempotent_map_eq_one
    (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (p := p) σ).toRingHom
  exact ⟨⟨e, h1, h2, h3⟩, h4⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermLinearPartCoordinatePointZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.GermDerivativeLinearMaps

section Calc

variable {k : Type} [CommRing k] {d : ℕ}

theorem dLin_comp (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germComp_matrixLinearMap_apply {n : ℕ} (U : Matrix (Fin d) (Fin d) k) (a : Pt k n d) (ha : GP a) (i : Fin d) :
    comp1 (LogExpAdaptedGauge.linMap U) a i = ∑ j, C (U i j) * a j := by
  have hz : FormalLog.CZ (![a] : Fin 1 → Pt k n d) := fun j l => single_point_zero_constant ha j l
  show ev ![a] (∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)) = _
  rw [FormalLog.ev_sum hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FormalLog.ev_mul hz, FormalLog.ev_C hz, FormalLog.ev_X hz]
  rfl

theorem gp_linMap (U : Matrix (Fin d) (Fin d) k) : GP (LogExpAdaptedGauge.linMap U) := fun i => by
  simp [LogExpAdaptedGauge.linMap]

theorem dLin_linMap (U : Matrix (Fin d) (Fin d) k) : dLin (LogExpAdaptedGauge.linMap U) = U := by
  classical
  ext i j
  simp [dLin, LogExpAdaptedGauge.linMap, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem linMap_one {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (LogExpAdaptedGauge.linMap (1 : Matrix (Fin d) (Fin d) k)) a = a := by
  classical
  funext i
  rw [germComp_matrixLinearMap_apply _ _ ha, Finset.sum_eq_single i] <;> simp +contextual [Matrix.one_apply, eq_comm]

end Calc

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem additive_at {n : ℕ} (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) : comp1 ψ (addOf F a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf F hF _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem germLinearPart_coordinatePoint_zero : dLin (pt k (n := 1) d 0) = 1 := by
  rw [← linMap_one (pt k (n := 1) d 0) (gp_pt 0), gt_comp1_pt_right, dLin_linMap]

theorem additive_eq_lin (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ℓ ε ψ : Pt k 1 d)
    (h1 : dLin ℓ = 1) (hℓ : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)) (hi : IsInvPair ℓ ε) (h0 : GP ψ)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1)) :
    ψ = comp1 (LogExpAdaptedGauge.linMap (dLin ψ)) ℓ := by
  classical
  have hε : GP ε := hi.2.1
  have hℓ0 : GP ℓ := hi.1
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 := gp_comp1 _ _ hε p0
  have q1 := gp_comp1 _ _ hε p1
  have ps : GP (pt k (n := 2) d 0 + pt k (n := 2) d 1) := fun i => by simp [pt]
  have e1 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← gt_comp_inv' hi _ (gp_addOf F hF _ _ q0 q1), additive_at F hF ℓ hℓ _ _ q0 q1,
      gt_comp_inv hi _ p0, gt_comp_inv hi _ p1]
  have e2 : comp1 (comp1 ψ ε) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ψ ε) (pt k (n := 2) d 0) + comp1 (comp1 ψ ε) (pt k (n := 2) d 1) := by
    rw [gt_comp1_comp1 _ _ hε _ ps, gt_comp1_comp1 _ _ hε _ p0, gt_comp1_comp1 _ _ hε _ p1, e1,
      additive_at F hF ψ hψ _ _ q0 q1]
  have hdε : dLin ε = 1 := by
    have := dLin_comp ℓ ε hε
    rwa [hi.2.2.1, germLinearPart_coordinatePoint_zero, h1, one_mul, eq_comm] at this
  have e3 : comp1 ψ ε = LogExpAdaptedGauge.linMap (dLin ψ) := by
    have hd : dLin (comp1 ψ ε) = dLin (LogExpAdaptedGauge.linMap (dLin ψ)) := by
      rw [dLin_comp _ _ hε, hdε, mul_one, dLin_linMap]
    funext i
    ext e
    by_cases he : e.degree = 1
    · obtain ⟨⟨s, j⟩, rfl⟩ : ∃ s, e = Finsupp.single s 1 := by
        exact (Finsupp.sum_eq_one_iff e).1 he
      obtain rfl : s = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun hd i) j
    · rw [addition_linear k d _ (congrFun e2 i) e he]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LogExpAdaptedGauge.linMap, map_sum, coeff_C_mul, coeff_X]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg, mul_zero]
      rintro rfl
      simp at he
  rw [← e3, gt_comp1_comp1 _ _ hε _ hℓ0, hi.2.2.2, gt_comp1_pt_right]

end Log

section Predicates

variable {C : Type} [NormedField C] [IsUltrametricDist C] {d : ℕ}

end Predicates

section Predicates2

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
  {O : Type} [CommRing O] [StarRing O]

end Predicates2

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

section Frame

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Frame

end GlobalTheory.GermDerivativeLinearMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.DerivEndo

open GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_endo (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ : Pt k 1 d) (hφ : GP φ)
    (hom : comp1 φ F = addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u (ev (n := 1) ![φ] g) = ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have key : ev (n := 2) ![F] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![F] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F := hom
    rw [this]
  rw [dof_eq _ hF hu, dof_eq F hF hu, key, ChartTrans.ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ChartTrans.ev_C_mul _ (single_point_zero_constant hφ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dof_smul_dir (F : Fin d → PS k 2 d) (c : k) (u : Fin d → k) (g : PS k 1 d) :
    Dof F (c • u) g = C c * Dof F u g := by
  unfold Dof
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem iterate_dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (n : ℕ) (c : k) (g : PS k 1 d) :
    (Dof F u)^[n] (C c * g) = C c * (Dof F u)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul]

theorem dmonOf_endo (F : Fin d → PS k 2 d) (φ : Pt k 1 d) (hφ : GP φ) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (α : ι → k)
    (h : ∀ l g, Dof F (u l) (ev (n := 1) ![φ] g) = C (α l) * ev (n := 1) ![φ] (Dof F (u l) g))
    (m : ι →₀ ℕ) (g : PS k 1 d) :
    DmonOf F u m (ev (n := 1) ![φ] g) = C (∏ l, α l ^ m l) * ev (n := 1) ![φ] (DmonOf F u m g) := by
  have hit : ∀ (l : ι) (n : ℕ) (g : PS k 1 d), (Dof F (u l))^[n] (ev (n := 1) ![φ] g) =
      C (α l ^ n) * ev (n := 1) ![φ] ((Dof F (u l))^[n] g) := by
    intro l n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul, h, pow_succ,
        map_mul, mul_assoc]
  rw [← Finset.prod_map_toList]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, iterate_dof_C_mul, hit, List.map_cons, List.prod_cons,
      map_mul]
    ring

end GlobalTheory.DerivEndo

namespace GlobalTheory

open DerivEndo QuadDeriv

theorem invariantDeriv_along_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (a : O), (∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) = ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g)) ∧ ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (m : ι →₀ ℕ) (g : PS k 1 d), constantCoeff (DmonOf (B.FK k) u m (ev (n := 1) ![B.actK k a] g)) = (∏ l, α l ^ m l) * constantCoeff (DmonOf (B.FK k) u m g) := by
  intro R _ d O _ _ k _ _ _ B a
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k a) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k a) (pt k (n := 2) d 0))
      (comp1 (B.actK k a) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom a)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const a) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const a) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have h1 : ∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) =
      ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g) :=
    dof_endo (B.FK k) hF (congrFun hU) (B.actK k a) hw hom
  refine ⟨h1, fun ι _ u α hα m g => ?_⟩
  rw [dmonOf_endo (B.FK k) (B.actK k a) hw u α (fun l g => by
    rw [h1, hα, dof_smul_dir, ChartTrans.ev_C_mul _ (single_point_zero_constant hw)]), map_mul, constantCoeff_C,
    constSt k d (B.actK k a) hw]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.FlatComplete

theorem mem_smul_top_iff_repr {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι]
    (b : Module.Basis ι O M) (J : Ideal O) (x : M) :
    x ∈ J • (⊤ : Submodule O M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun y => ∀ i, b.repr y i ∈ J) hx ?_ ?_
    · intro r hr y _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · intro y z hy hz i
      rw [map_add (f := _), Finsupp.add_apply]
      exact J.add_mem (hy i) (hz i)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Module.Basis ι O M) (J : Ideal O) [hO : IsAdicComplete J O] :
    IsAdicComplete J M := by
  have hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n := fun n r => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)] := fun n x y => by
    simp only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]
  rw [isAdicComplete_iff]
  refine ⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩
  · apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_
    have := (key n x 0).1 (hx n) i
    rwa [map_zero, Finsupp.zero_apply] at this
  · have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    rw [← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
    exact hL i n

theorem isAdicComplete_of_finite_flat (O : Type) [CommRing O] [IsLocalRing O] (J : Ideal O)
    (hO : IsAdicComplete J O) (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Flat O A] : IsAdicComplete (J.map (algebraMap O A)) A := by
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  have := hO
  exact (IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2
    (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)

end GlobalTheory.FlatComplete
end

