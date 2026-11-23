module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdQMapDomainResiduePlaceTransport
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTransport

variable {k M : Type} [Field k] [Field M] {c : k →+* M}

theorem ord_prod_zpow {ι : Type} (P : Place c) (s : Finset ι) (f : ι → M) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : P.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s)))
        (Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))),
      P.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ordQ_mapDomain {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) :
    P.ordQ (Finsupp.mapDomain f φ) = ∑ g ∈ φ.support, φ g * P.ord (f g) := by
  rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

theorem ord_prod_eq_mul_ordQ {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) (N : ℕ)
    (m : ι → ℤ) (hm : ∀ g ∈ φ.support, (m g : ℚ) = N * φ g) (hf : ∀ g ∈ φ.support, f g ≠ 0) :
    (P.ord (∏ g ∈ φ.support, f g ^ m g) : ℚ) = N * P.ordQ (Finsupp.mapDomain f φ) := by
  rw [ord_prod_zpow P _ f m hf, ordQ_mapDomain, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hm g hg]
  ring

theorem exists_common_den {ι : Type} (s : Finset ι) (φ : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ s, ∃ m : ℤ, (m : ℚ) = N * φ g := by
  classical
  refine ⟨∏ g ∈ s, (φ g).den, Finset.prod_pos fun g _ => (φ g).den_pos, fun g hg =>
    ⟨(φ g).num * ∏ x ∈ s.erase g, ((φ x).den : ℤ), ?_⟩⟩
  rw [← Finset.mul_prod_erase s _ hg]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

end GlobalTheory.FieldPair.ResidueTransport

namespace GlobalTheory.FieldPair


open ResidueTransport in
theorem ordQ_mapDomain_residue_eq {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (Q : Subring L) (u : Q) (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK)
    (hSQ : S.Contains Q) (hSu : S.ord (u : L) = 0) (hu0 : (u : L) ≠ 0)
    (hψ : Function.Surjective ψ)
    (hF : ∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a)
    (hFu : ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1)
    (hG : ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
      ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G)
    (φ : S.ring →₀ ℚ) (hsupp : ∀ g ∈ φ.support, ψ g ≠ 0)
    (hPφ : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) :
    F.ordQ (Finsupp.mapDomain ψ φ) =
      E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by

  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal S.ring :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
  have hunit : ∀ g ∈ φ.support, IsUnit g := fun g hg =>
    IsLocalRing.notMem_maximalIdeal.1 (by rw [← hker, RingHom.mem_ker]; exact hsupp g hg)
  choose! w hw using hunit
  obtain ⟨N, hN, hm⟩ := exists_common_den φ.support φ
  choose! m hm using hm
  have hg0 : ∀ g ∈ φ.support, ((g : S.ring) : L) ≠ 0 := fun g hg h =>
    hsupp g hg (by rw [show g = 0 from Subtype.ext h, map_zero])
  set G : L := ∏ g ∈ φ.support, ((g : S.ring) : L) ^ m g with hGdef
  set H : K := ∏ g ∈ φ.support, ψ g ^ m g with hHdef
  have hGord := fun P : Place cL => ord_prod_eq_mul_ordQ P φ (fun g : S.ring => (g : L)) N m hm hg0
  have hHord := ord_prod_eq_mul_ordQ F φ ψ N m hm hsupp
  have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.2 fun g hg => zpow_ne_zero _ (hg0 g hg)

  have hPG : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0 := by
    intro P hP hPE
    by_cases hPS : P.ring = S.ring
    · obtain rfl : P = S := Place.ext hPS
      rw [hGdef, ord_prod_zpow P _ _ m hg0]
      refine Finset.sum_eq_zero fun g hg => ?_
      rw [← hw g hg, P.ord_eq_zero (w g).isUnit, mul_zero]
    · have h := hGord P
      rw [hPφ P hP hPS hPE, mul_zero] at h
      exact_mod_cast h
  obtain ⟨q, hqU, hGq⟩ := hG G hG0 hPG
  set b := E.ord G with hb

  let uS : S.ring := ⟨u, hSQ _ u.2⟩
  have huS : IsUnit uS := by
    have h1 : (u : L) ∈ S.ring := hSQ _ u.2
    have h2 : (u : L)⁻¹ ∈ S.ring := by
      rw [← S.ord_nonneg_iff (inv_ne_zero hu0), S.ord_inv, hSu]; simp
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hu0))
  obtain ⟨r, hr⟩ := hqU.exists_right_inv
  let qS : S.ring := ⟨q, hSQ _ q.2⟩
  let rS : S.ring := ⟨r, hSQ _ r.2⟩
  have hqr : qS * rS = 1 := Subtype.ext (by change ((q * r : Q) : L) = 1; rw [hr]; rfl)
  let qU : S.ringˣ := (IsUnit.of_mul_eq_one rS hqr).unit
  let uU : S.ringˣ := huS.unit
  let W : S.ringˣ := ∏ g ∈ φ.support, w g ^ m g
  let e : S.ringˣ →* Lˣ := Units.map (S.ring.subtype : S.ring →* L)
  let f : S.ringˣ →* Kˣ := Units.map (ψ : S.ring →* K)
  have he : ∀ x, ((e x : Lˣ) : L) = ((x : S.ring) : L) := fun _ => rfl
  have hf : ∀ x, ((f x : Kˣ) : K) = ψ x := fun _ => rfl
  have heW : ((e W : Lˣ) : L) = G := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, he]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hfW : ((f W : Kˣ) : K) = H := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hf]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hWeq : W = qU * uU ^ b := by
    have hinj : Function.Injective e := fun x y h =>
      Units.ext (Subtype.ext (by rw [← he, ← he, h]))
    apply hinj
    apply Units.ext
    rw [heW, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, he, he,
      IsUnit.unit_spec, IsUnit.unit_spec]
    exact hGq
  have hH : H = ψ qS * ψ uS ^ b := by
    rw [← hfW, hWeq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hf, hf,
      IsUnit.unit_spec, IsUnit.unit_spec]

  have hq0 : ψ qS * ψ rS = 1 := by rw [← map_mul, hqr, map_one]
  have hψq0 : ψ qS ≠ 0 := left_ne_zero_of_mul_eq_one hq0
  have hψu0 : ψ uS ≠ 0 := (huS.map ψ).ne_zero
  have hFq : F.ord (ψ qS) = 0 := by
    have h1 : 0 ≤ F.ord (ψ qS) := (F.ord_nonneg_iff hψq0).2 ((hF _).2 ⟨qS, q.2, rfl⟩)
    have hinv : (ψ qS)⁻¹ = ψ rS := inv_eq_of_mul_eq_one_right hq0
    have h2 : 0 ≤ F.ord (ψ qS)⁻¹ := (F.ord_nonneg_iff (inv_ne_zero hψq0)).2
      (by rw [hinv]; exact (hF _).2 ⟨rS, r.2, rfl⟩)
    rw [F.ord_inv] at h2
    omega
  have hFH : F.ord H = b := by
    rw [hH, F.ord_mul hψq0 (zpow_ne_zero _ hψu0), F.ord_zpow, hFq, hFu uS rfl]
    ring
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hEG := hGord E
  rw [← hb, ← hFH, hHord] at hEG
  exact mul_left_cancel₀ hNq hEG

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTop
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem ne_zero_of_ord_pos {K : Type} [Field K] [Algebra ℂ K] (E : Place (algebraMap ℂ K)) {e : K}
    (he : 0 < E.ord e) : e ≠ 0 := by
  rintro rfl
  simp [Place.ord] at he

theorem graphIdeal_ne_top_of_hom {K κ κ' F : Type} [Field K] [Field κ] [Field κ'] [Field F]
    [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (h1 : ∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a)
    (h2 : ∀ a, algebraMap ℂ K a ∈ R) (h4 : E.Contains R)
    (α : E.ring →+* F) (β : κ' →+* F) (hα : ∀ r : R, α ⟨r, h4 _ r.2⟩ = β (ρ (π r)))
    (hpos : ∀ x : E.ring, 0 < E.ord (x : K) → α x = 0) :
    graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  letI : Algebra ℂ F := (β.comp (algebraMap ℂ κ')).toAlgebra
  let j : placeAlg E →+* E.ring :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let α' : placeAlg E →ₐ[ℂ] F :=
    { α.comp j with
      commutes' := fun a => by
        have := hα ⟨algebraMap ℂ K a, h2 a⟩
        rw [h1, ρ.commutes] at this
        exact this }
  let β' : κ' →ₐ[ℂ] F := { β with commutes' := fun _ => rfl }
  let Φ := Algebra.TensorProduct.lift α' β' (fun _ _ => Commute.all _ _)
  let Ψ : tens (κ' := κ') (placeAlg E) →+* F :=
    (Φ.comp (tensEquiv (κ' := κ') (placeAlg E)).symm.toAlgHom).toRingHom
  have hΨ : ∀ w, Ψ (tensEquiv (placeAlg E) w) = Φ w := fun w => by
    simp [Ψ]
  intro htop
  have hle : graphIdeal (κ' := κ') E R π ρ ≤ RingHom.ker Ψ := by
    rw [graphIdeal, Ideal.span_le]
    rintro b (⟨e, he, hb⟩ | ⟨a, hb⟩)
    · have hmem : e ∈ E.ring := (E.ord_nonneg_iff (ne_zero_of_ord_pos E he)).1 he.le
      have hb' : b = tensEquiv (κ' := κ') (placeAlg E) (⟨e, hmem⟩ ⊗ₜ 1) :=
        Subtype.ext (by rw [hb]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact hpos ⟨e, hmem⟩ he
    · have hb' : b = tensEquiv (κ' := κ') (placeAlg E)
          (⟨a, h4 _ a.2⟩ ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)) :=
        Subtype.ext (by rw [hb, coe_tensEquiv, map_sub]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, map_sub, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
      rw [sub_eq_zero]
      exact hα a
  have h1mem : (1 : tens (κ' := κ') (placeAlg E)) ∈ graphIdeal (κ' := κ') E R π ρ :=
    htop ▸ Submodule.mem_top
  exact one_ne_zero ((RingHom.mem_ker).1 (hle h1mem) |>.symm.trans (map_one Ψ)).symm

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem graphIdeal_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E h1 h2 h3 h4 h5
  let kE := IsLocalRing.ResidueField E.ring
  let inc : R →+* E.ring := R.subtype.codRestrict E.ring (fun r => h4 _ r.2)
  let g : R →+* kE := (IsLocalRing.residue E.ring).comp inc
  have hnu : ∀ x : E.ring, (x : K) ≠ 0 →
      (0 < E.ord x ↔ x ∈ IsLocalRing.maximalIdeal E.ring) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hpos hu
      have := E.ord_eq_zero hu
      omega
    · intro hnu'
      have h0 : 0 ≤ E.ord x := (E.ord_nonneg_iff hx).2 x.2
      rcases h0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hnu'
        have hinv : (x : K)⁻¹ ∈ E.ring :=
          (E.ord_nonneg_iff (inv_ne_zero hx)).1 (by rw [E.ord_inv, ← h]; simp)
        exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hx))
  have hker : ∀ r : R, π r = 0 ↔ g r = 0 := by
    intro r
    by_cases hr : (r : K) = 0
    · have : r = 0 := Subtype.ext hr
      subst this
      simp
    · rw [h5 r hr, show g r = IsLocalRing.residue E.ring (inc r) from rfl,
        IsLocalRing.residue_eq_zero_iff]
      exact hnu (inc r) hr
  have hsurj : Function.Surjective π.rangeRestrict := π.rangeRestrict_surjective
  let φ₀ : π.range →+* kE := π.rangeRestrict.liftOfSurjective hsurj
    ⟨g, fun r hr => by
      rw [RingHom.mem_ker] at hr ⊢
      exact (hker r).1 (congrArg Subtype.val hr)⟩
  have hφ₀ : ∀ r, φ₀ (π.rangeRestrict r) = g r := fun r =>
    RingHom.liftOfSurjective_comp_apply _ hsurj _ r
  have hinj : Function.Injective φ₀ := (injective_iff_map_eq_zero φ₀).2 fun s hs => by
    obtain ⟨r, rfl⟩ := hsurj s
    rw [hφ₀] at hs
    exact Subtype.ext ((hker r).2 hs)
  haveI : IsFractionRing π.range κ := IsFractionRing.of_field π.range κ fun z => by
    obtain ⟨a, b, hb, e⟩ := h3 z
    refine ⟨π.rangeRestrict a, π.rangeRestrict b, ?_⟩
    show z = π a / π b
    rw [eq_div_iff hb, e]
  let ι : κ →+* kE := IsFractionRing.lift hinj
  have hι : ∀ r, ι (π r) = g r := fun r => by
    rw [← hφ₀]
    exact IsFractionRing.lift_algebraMap hinj (π.rangeRestrict r)
  letI : Algebra κ kE := ι.toAlgebra
  letI : Algebra κ κ' := ρ.toRingHom.toAlgebra
  haveI : Nontrivial (kE ⊗[κ] κ') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ kE κ'
      ι.injective ρ.toRingHom.injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (kE ⊗[κ] κ')
  letI : Field (kE ⊗[κ] κ' ⧸ M) := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  let α : E.ring →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeLeftRingHom.comp (IsLocalRing.residue E.ring))
  let β : κ' →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeRight (R := κ) (A := kE)).toRingHom
  refine graphIdeal_ne_top_of_hom R π ρ E h1 h2 h4 α β (fun r => ?_) (fun x hx => ?_)
  · show q (IsLocalRing.residue E.ring (inc r) ⊗ₜ 1) = q (1 ⊗ₜ ρ (π r))
    congr 1
    rw [show IsLocalRing.residue E.ring (inc r) = g r from rfl, ← hι,
      show ι (π r) = π r • (1 : kE) by rw [Algebra.smul_def, mul_one]; rfl,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  · show q (IsLocalRing.residue E.ring x ⊗ₜ 1) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).2 ((hnu x (ne_zero_of_ord_pos E hx)).1 hx),
      TensorProduct.zero_tmul, map_zero]

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffCurvatureCompHolomorphic
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexConjugate

namespace GlobalTheory.GoodTop

theorem isSesq_eq_sum_coordVec {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {α : V n → V n → M}
    (hα : IsSesq α) (x y : V n) :
    α x y = ∑ c, ∑ d, (x c * conj (y d)) • α (coordVec c) (coordVec d) := by
  have hex : ∀ w : V n, w = ∑ a, w a • coordVec a := by
    intro w
    ext i
    simp [coordVec, Pi.single_apply]
  have hl : ∀ (s : Finset (Fin n)) (c : Fin n → ℂ) (x : Fin n → V n) (y : V n),
      α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i • α (x i) y := by
    intro s c x y
    induction s using Finset.induction_on with
    | empty =>
      have := hα.smul_left 0 0 y
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih]
  have hr : ∀ (s : Finset (Fin n)) (c : Fin n → ℂ) (x : V n) (y : Fin n → V n),
      α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) • α x (y i) := by
    intro s c x y
    induction s using Finset.induction_on with
    | empty =>
      have := hα.smul_right 0 x 0
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih]
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by rw [← hex x, ← hex y]
    _ = _ := by
      rw [hl]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hr, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul]

theorem det_of_apply_coordVec {n : ℕ} (L : V n →L[ℂ] V n) :
    (Matrix.of fun c a => L (coordVec a) c).det = L.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1

theorem mixTop_curvAt_comp_holo : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  intro n r _ _ G φ w hφ hG hu
  set J : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => fderiv ℂ φ w (coordVec a) c with hJ
  have h := _root_.GlobalTheory.GoodTop.mixTop_subst (fun _ : Fin n => curvAt G (φ w)) J (J.map conj)
  have e : (fun _ : Fin n => curvAt (fun x => G (φ x)) w) =
      fun (_ : Fin n) a b => ∑ c, ∑ d, (J c a * (J.map conj) d b) • curvAt G (φ w) c d := by
    funext _ a b
    rw [curvAt, curv_comp_holo hG hu hφ, isSesq_eq_sum_coordVec (isSesq_curv hG hu)]
    rfl
  have hc : (J.map conj).det = conj J.det := by
    rw [RingHom.map_det]; rfl
  rw [e, h, hc, hJ, det_of_apply_coordVec, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfield
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ProjCountableDescent


open GlobalTheory.PolCountableDescent in
theorem projLB_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  intro K _ X p hp L hL
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ X p hp
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ X p₀ p φ L hL sq
  let s : Finset K := s₀ ∪ s₂
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  have sq₁ : IsPullback (pullback.fst p₀ inc) (pullback.snd p₀ inc) p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : X ⟶ pullback p₀ inc := sq₁.lift φ (p ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ pullback.fst p₀ inc = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd p₀ inc = p ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨L₁, hL₁, hI⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) _ _ _ ψ
    sq₁ hψ₁ hψ₂
  refine ⟨K₁, _, pullback.snd p₀ inc, ψ, L₁, countable_closure s,
    ProjSpace.isProjOver_pullback_snd _ hp₀, ?_, hL₁, hI⟩
  refine IsPullback.of_right (t := sq₁) ?_ hψ₂
  have e : spMap (algebraMap K₁ K) ≫ inc = spMap K₀.subtype := spMap_subtype_comp h
  rw [hψ₁, e]
  exact sq

end GlobalTheory.ProjCountableDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGLStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | exact GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | (intros; apply GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QWeilZeroCartier
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PairStep

theorem qWeil_zero_cartier {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem qNum_zero_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ N : LB X, QNum p N 0 0 := by
  intro X _ _ p _ N
  letI := algebraΓOfHom p
  refine ⟨1, 0, one_pos, CartierDiv.eff_zero, (qWeil_zero_cartier 1).symm, fun C _ => ?_⟩
  rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
  simp

end GlobalTheory.PairStep
end
end

