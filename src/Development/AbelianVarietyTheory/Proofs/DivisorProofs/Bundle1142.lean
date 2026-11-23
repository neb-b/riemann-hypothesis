module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardChartsFormalTowerOfVeryAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.ChartsEx

section Level0

variable {X : Scheme.{0}} {H : LB X}

theorem exists_chart_of_mem_nonzeroLocus (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) :
    ∃ k, x ∈ H.U k := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨l, X.basicOpen_le _ hl⟩

theorem mem_nonzeroLocus_iff_basicOpen (s : LB.Sec H) (k : H.ι) {x : X} (hk : x ∈ H.U k) :
    x ∈ nonzeroLocus s ↔ x ∈ X.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg X.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, X.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem isUnit_rs (s : LB.Sec H) (k : H.ι) {O : X.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus s) : IsUnit (rs X hk (s.f k)) := by
  have hb : O ≤ X.basicOpen (s.f k) := fun x hx => (mem_nonzeroLocus_iff_basicOpen s k (hk hx)).1 (h hx)
  have hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  simpa only [rs_rs] using hu.map (rs X hb)

theorem ratio_self (s : LB.Sec H) {V : X.Opens} (h : V ≤ nonzeroLocus s) (r : Γ(X, V))
    (hr : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : V ⊓ H.U k ≤ V) r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k)) :
    r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V (fun k => homOfLE inf_le_left)
    (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus s (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, hl⟩
  · change rs X inf_le_left r = rs X inf_le_left 1
    rw [map_one]
    exact (isUnit_rs s k inf_le_right (inf_le_left.trans h)).mul_right_cancel
      ((hr k).symm.trans (_root_.one_mul _).symm)

variable {n : ℕ} (s : Fin (n + 1) → LB.Sec H) (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
      rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))


include hr in
theorem basicOpen_ratio (i j : Fin (n + 1)) :
    X.basicOpen (r i j) = nonzeroLocus (s i) ⊓ nonzeroLocus (s j) := by
  have key : ∀ k, (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) =
      (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := by
    intro k
    have e := congrArg X.basicOpen (hr i j k)
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (isUnit_rs (s i) k inf_le_right inf_le_left)] at e
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
    rw [e, inf_assoc, inf_comm (X.basicOpen (r i j)), ← inf_assoc, inf_idem]
  ext x
  constructor
  · intro hx
    have hxi : x ∈ nonzeroLocus (s i) := X.basicOpen_le _ hx
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := ⟨⟨hxi, hk⟩, hx⟩
    rw [← key k] at hm
    exact ⟨hxi, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm.2⟩⟩
  · rintro ⟨hxi, hxj⟩
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) :=
      ⟨⟨hxi, hk⟩, (mem_nonzeroLocus_iff_basicOpen (s j) k hk).1 hxj⟩
    rw [key k] at hm
    exact hm.2


include hr in
theorem ratio_cocycle (i j l : Fin (n + 1)) :
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i l) =
      rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i j) *
        rs X (inf_le_right : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s j)) (r j l) := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k)
    (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _
    fun k => ?_
  · obtain ⟨l', hl⟩ := exists_chart_of_mem_nonzeroLocus (s i) hx.1
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l', hx, hl⟩
  · change rs X inf_le_left _ = rs X inf_le_left _
    have hi : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s i) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_left
    have hj : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s j) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_right
    have e1 := congrArg (rs X hi) (hr i l k)
    have e2 := congrArg (rs X hi) (hr i j k)
    have e3 := congrArg (rs X hj) (hr j l k)
    simp only [map_mul, rs_rs] at e1 e2 e3 ⊢
    have hu := isUnit_rs (s i) k (inf_le_right : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ H.U k)
      (inf_le_left.trans inf_le_left)
    refine hu.mul_right_cancel ?_
    rw [← e1, e3, e2]
    ring

end Level0

end GlobalTheory.FormalAlg.ChartsEx

namespace GlobalTheory.FormalAlg.ChartsEx

section Tower

variable {R : Type} [CommRing R] {I : Ideal R}

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [_root_.range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    refine x.2.mem_of_pow_mem 2 ?_
    have : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow ha' 2
    rw [this]
    exact Ideal.zero_mem _
  exact hx

theorem isNilpotent_ker_factor (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hb : b ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy
  rw [← map_mul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) + (e + 1) by omega) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

variable {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}


variable (Y n) in
abbrev Lvl (e : ℕ) : Type :=
  {p : (Σ D : Fin (n + 1) → (Y e).left.Opens, ∀ i, Fin (n + 1) → Γ((Y e).left, D i)) //
    ∀ i, IsAffineOpen (p.1 i)}


variable (β) in
def Lifts (e : ℕ) (q : Lvl Y n e) (q' : Lvl Y n (e + 1)) : Prop :=
  ∃ h : ∀ i, β e ⁻¹ᵁ q'.1.1 i = q.1.1 i,
    ∀ i j, ((β e).appLE (q'.1.1 i) (q.1.1 i) (h i).ge).hom (q'.1.2 i j) = q.1.2 i j

theorem exists_lifts {e : ℕ} (hsq : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q : Lvl Y n e) : ∃ q' : Lvl Y n (e + 1), Lifts β e q q' := by
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  have hD := fun i => GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _
    (Ideal.Quotient.factor hle) hsurj (isNilpotent_ker_factor e hle) _ _ (Y (e + 1)).hom (Y e).hom
    (β e) hsq (q.1.1 i) (q.2 i)
  choose D' hD' hpre using hD
  haveI : IsClosedImmersion (β e) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip
      (IsClosedImmersion.spec_of_surjective _ hsurj)
  have hs : ∀ i, Function.Surjective ((β e).appLE (D' i) (q.1.1 i) (hpre i).ge).hom := by
    intro i y
    obtain ⟨x, hx⟩ := (β e).app_surjective (D' i) (hD' i) (rs _ (hpre i).le y)
    refine ⟨x, ?_⟩
    change rs _ (hpre i).ge (((β e).app (D' i)).hom x) = y
    rw [hx, rs_rs, rs_self]
  choose ρ' hρ' using fun i j => hs i (q.1.2 i j)
  exact ⟨⟨⟨D', ρ'⟩, hD'⟩, hpre, hρ'⟩


variable (β) in
def seq (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lvl Y n e :=
  Nat.rec (motive := Lvl Y n) q₀ (fun e q => Classical.choose (exists_lifts (hsq e) q)) e

theorem seq_lifts (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lifts β e (seq β hsq q₀ e) (seq β hsq q₀ (e + 1)) :=
  Classical.choose_spec (exists_lifts (hsq e) (seq β hsq q₀ e))

end Tower

end GlobalTheory.FormalAlg.ChartsEx


open GlobalTheory.FormalAlg.ChartsEx in
theorem GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  intro R _ I Y β hsq H₀ n s₀ _ hva
  obtain ⟨hcov, hloc⟩ := hva
  choose haff r hrel hsurj using hloc
  let q₀ : Lvl Y n 0 := ⟨⟨fun i => nonzeroLocus (s₀ i), r⟩, haff⟩
  have hsurjβ : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hsq e).flip (surjective_thickTrans e)
  have hcover : ∀ e, ⨆ i, (seq β hsq q₀ e).1.1 i = ⊤ := by
    intro e
    induction e with
    | zero => exact hcov
    | succ e ih =>
      obtain ⟨hpre, -⟩ := seq_lifts hsq q₀ e
      refine top_unique fun y _ => ?_
      obtain ⟨x, rfl⟩ := (hsurjβ e).surj y
      have hx : x ∈ β e ⁻¹ᵁ (⨆ i, (seq β hsq q₀ (e + 1)).1.1 i) := by
        rw [Scheme.Hom.preimage_iSup]
        simp only [hpre]
        rw [ih]
        trivial
      exact hx
  refine ⟨{ D := fun e => (seq β hsq q₀ e).1.1
            aff := fun e => (seq β hsq q₀ e).2
            cover := hcover
            pre := fun e => (seq_lifts hsq q₀ e).1
            ρ := fun e => (seq β hsq q₀ e).1.2
            ρ_pull := fun e => (seq_lifts hsq q₀ e).2
            ρ_self := fun i => ratio_self (s₀ i) le_rfl (r i i) (hrel i i)
            basic := fun i j => basicOpen_ratio s₀ r hrel i j
            cocycle := fun i j l => ratio_cocycle s₀ r hrel i j l
            surj := hsurj }, fun i => rfl, hrel⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_trBasis_lift : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  intro K κ _ _ inst k R π hfrac ⟨z, hz⟩
  have hiff : ∀ u : Fin k → κ, TrBasis (algebraMap ℂ κ) u ↔ IsTranscendenceBasis ℂ u := by
    intro u
    have : (algebraMap ℂ κ).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [this]
  have hz' := (hiff z).1 hz
  have htop : IntermediateField.adjoin ℂ (Set.range π) = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨a, b, hb, e⟩ := hfrac f
    have : f = π a / π b := by rw [← e, mul_div_cancel_right₀ _ hb]
    rw [this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range π)) κ :=
    ⟨fun f => isAlgebraic_algebraMap
      (⟨f, htop ▸ IntermediateField.mem_top⟩ : IntermediateField.adjoin ℂ (Set.range π))⟩
  have halg' : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range π)) κ :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp halg
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range π)
  have hc : Cardinal.mk (Fin k) = Cardinal.mk t := by
    rw [hb.cardinalMk_eq_trdeg, hz'.cardinalMk_eq_trdeg]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  choose J hJ using fun i : Fin k => ht (e i).2
  refine ⟨J, (hiff _).2 ?_⟩
  have := (isTranscendenceBasis_equiv e).2 hb
  convert this using 1
  funext i
  exact hJ i

end GlobalTheory.GraphLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPoint
section
open GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isAlgebraic_of_mul_eq {S K : Type} [CommRing S] [Field K] [Algebra S K] {f : K} (a b : S)
    (hb : b ≠ 0) (e : f * algebraMap S K b = algebraMap S K a) : IsAlgebraic S f := by
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) h0
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ, sub_zero,
      Polynomial.coeff_zero, if_true] using h1
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C, mul_comm, e,
      sub_self]

theorem exists_trBasis_mem_of_isLocModel {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K)
    (n : ℕ) (hR : IsLocModel c R) (hx : ∃ x : Fin n → K, TrBasis c x) :
    ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  letI := c.toAlgebra
  obtain ⟨x, hx⟩ := hx
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (R : Set K)) K := by
    refine ⟨fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac f
    exact isAlgebraic_of_mul_eq (⟨a, Algebra.subset_adjoin ha⟩ : Algebra.adjoin ℂ (R : Set K))
      ⟨b, Algebra.subset_adjoin hb⟩ (fun h => hb0 (congrArg Subtype.val h)) e
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (R : Set K)
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) ht
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.trans h2.symm)
  refine ⟨fun j => ⟨(e j : K), hts (e j).2⟩, ?_⟩
  show IsTranscendenceBasis ℂ fun j => ((e j : t) : K)
  exact (isTranscendenceBasis_equiv e).2 ht

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingPartNonLoweringUnit
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.WeightPart

variable {S ι : Type} [Ring S] [Fintype ι] {ε : ι → S} {w : ι → ℤ}

def dg (ε : ι → S) (w : ι → ℤ) (x : S) : S := ∑ a, ∑ b, if w a = w b then ε a * x * ε b else 0

theorem ext_sand (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : ∀ a b, ε a * x * ε b = ε a * y * ε b) : x = y := by
  have e : ∀ z : S, z = ∑ a, ∑ b, ε a * z * ε b := fun z => by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  rw [e x, e y]
  simp only [h]

theorem sand_mul (he : CompleteOrthogonalIdempotents ε) (x y : S) (a b : ι) :
    ε a * (x * y) * ε b = ∑ c, (ε a * x * ε c) * (ε c * y * ε b) := by
  have e : ∀ c, (ε a * x * ε c) * (ε c * y * ε b) = ε a * x * ε c * (y * ε b) := fun c => by
    rw [mul_assoc (ε c) y, ← mul_assoc _ (ε c) (y * ε b), mul_assoc _ (ε c) (ε c), (he.idem c).eq]
  simp only [e]
  rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete]
  simp only [mul_one, mul_assoc]

theorem sand_dg (he : CompleteOrthogonalIdempotents ε) (x : S) (a b : ι) :
    ε a * dg ε w x * ε b = if w a = w b then ε a * x * ε b else 0 := by
  classical
  rw [dg, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single a, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_eq_single b]
  · split_ifs
    · rw [← mul_assoc, ← mul_assoc, (he.idem a).eq, mul_assoc _ (ε b), (he.idem b).eq]
    · simp
  · intro c _ hc
    split_ifs
    · rw [mul_assoc, mul_assoc _ (ε c), he.ortho hc, mul_zero, mul_zero]
    · simp
  · simp
  · intro c _ hc
    rw [Finset.mul_sum, Finset.sum_eq_zero, zero_mul]
    intro d _
    split_ifs
    · rw [← mul_assoc, ← mul_assoc, he.ortho hc.symm, zero_mul, zero_mul]
    · simp
  · simp

theorem dg_mul_dg (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : x * y = 1)
    (hx : ∀ a b, w a < w b → ε a * x * ε b = 0) (hy : ∀ a b, w a < w b → ε a * y * ε b = 0) :
    dg ε w x * dg ε w y = 1 := by
  refine ext_sand he fun a b => ?_
  by_cases hab : w a = w b
  · rw [← h, sand_mul he, sand_mul he]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    rcases lt_trichotomy (w a) (w c) with h1 | h1 | h1
    · rw [if_neg h1.ne, hx a c h1, zero_mul, zero_mul]
    · rw [if_pos h1, if_pos (h1 ▸ hab)]
    · rw [if_neg h1.ne', hy c b (hab ▸ h1), zero_mul, mul_zero]
  · rw [mul_one, he.ortho (fun e => hab (congrArg w e)), sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    by_cases h1 : w a = w c
    · rw [if_neg (show ¬ w c = w b from h1 ▸ hab), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem exists_weightPart : ∀ {S ι : Type} [Ring S] [Fintype ι] (st : S →+ S) (ε : ι → S) (w : ι → ℤ) (τ : ι → ι), (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → CompleteOrthogonalIdempotents ε → (∀ a, st (ε a) = ε (τ a)) → (∀ a, w (τ a) = -w a) → (∀ a, τ (τ a) = a) → ∀ x y : S, x * y = 1 → y * x = 1 → st x = y → (∀ a b, w a < w b → ε a * x * ε b = 0) → (∀ a b, w a < w b → ε a * y * ε b = 0) → ∃ m m' : S, m * m' = 1 ∧ m' * m = 1 ∧ st m = m' ∧ (∀ a b, w a ≠ w b → ε a * m * ε b = 0) ∧ (∀ a b, w a ≠ w b → ε a * m' * ε b = 0) ∧ x * m' - 1 ∈ raise ε w 0 ∧ ∀ S₀ : Subring S, (∀ a, ε a ∈ S₀) → x ∈ S₀ → y ∈ S₀ → m ∈ S₀ ∧ m' ∈ S₀ := by
  intro S ι _ _ st ε w τ hst hss he hε hw hτ x y hxy hyx hs hx hy
  have hm : ∀ z a b, w a ≠ w b → ε a * dg ε w z * ε b = 0 := fun z a b h => by rw [sand_dg he, if_neg h]
  have h1 := dg_mul_dg he hxy hx hy
  refine ⟨dg ε w x, dg ε w y, h1, dg_mul_dg he hyx hy hx, ?_, hm x, hm y, ?_, ?_⟩
  · have key : ∀ z a b, ε a * st z * ε b = st (ε (τ b) * z * ε (τ a)) := fun z a b => by
      rw [hst, hst, hε, hε, hτ, hτ, mul_assoc]
    refine ext_sand he fun a b => ?_
    rw [key, sand_dg he, sand_dg he, ← hs, key, hw, hw]
    by_cases h : w a = w b
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun e => h (neg_inj.1 e).symm), map_zero]
  · intro a b hab
    have hab' : w a ≤ w b := by simpa using hab
    rw [← h1, ← sub_mul, sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : w c = w b
    · rw [mul_sub, sub_mul, sand_dg he]
      split_ifs with h2
      · rw [sub_self, zero_mul]
      · rw [hx a c (lt_of_le_of_ne (h ▸ hab') h2), sub_self, zero_mul]
    · rw [hm y c b h, mul_zero]
  · intro S₀ h0 hx0 hy0
    have : ∀ z ∈ S₀, dg ε w z ∈ S₀ := fun z hz =>
      sum_mem fun a _ => sum_mem fun b _ => by
        split_ifs
        · exact mul_mem (mul_mem (h0 a) hz) (h0 b)
        · exact zero_mem _
    exact ⟨this x hx0, this y hy0⟩

end GlobalTheory.WeightPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNumberFieldBddDenomConjNormLeOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NumFin

theorem finite_bdd_denom_conj_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  intro E _ _ d hd
  have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  set S := {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} with hS
  have hF := NumberField.Embeddings.finite_of_norm_le E ℂ (d : ℝ)
  have himg : (fun z : E => (d : E) * z) '' S ⊆ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ)} := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((d : E) * z) fun w => by
        have h := hz1 w
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        convert h using 2
        rw [← map_natCast (algebraMap E (w.adicCompletion E)) d, ← map_mul]
        rfl
      show IsIntegral ℤ ((d : E) * z)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      calc (d : ℝ) * ‖φ z‖ ≤ (d : ℝ) * 1 := by gcongr; exact hz2 φ
        _ = d := mul_one _
  have hinj : Set.InjOn (fun z : E => (d : E) * z) S := fun a _ b _ h => mul_left_cancel₀ hd0 h
  exact Set.Finite.of_finite_image (hF.subset himg) hinj

end GlobalTheory.NumFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  first | exact @GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff | exact GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff | (intros; apply GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff <;> assumption)
end

