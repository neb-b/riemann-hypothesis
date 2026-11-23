module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ConjOfSqNonneg
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open Polynomial
open scoped IntermediateField

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

private theorem sq_parts (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) :
    z.re ^ 2 - z.im ^ 2 = a ∧ z.re * z.im = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at h1 h2
  exact ⟨by linarith, by linarith⟩

private theorem conj_of_sq_nonneg (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : 0 ≤ a) :
    z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have him : z.im = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.im]
    · exact h3
  exact (Complex.conj_eq_iff_im.mpr him).symm

private theorem conj_of_sq_nonpos (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : a ≤ 0) :
    -z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

end UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.mkQ :
    MkQ := by
  intro Y Ω _ _ _ _ _ _ x a hx ⟨g, hg⟩
  have hxa : x ^ 2 = algebraMap Y Ω (a : Y) := by rw [hx, map_intCast]
  have heval : aeval x (X ^ 2 - C (a : Y) : Y[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hxa, sub_self]
  have hint : IsIntegral Y x := ⟨X ^ 2 - C (a : Y), monic_X_pow_sub_C _ two_ne_zero, heval⟩
  have hirr : Irreducible (X ^ 2 - C (a : Y) : Y[X]) := by
    refine X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hg ?_)
    have h2 : x ^ 2 = (algebraMap Y Ω b) ^ 2 := by rw [hxa, ← map_pow, hb]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · rw [h]; exact g.commutes b
    · rw [h, map_neg]; congr 1; exact g.commutes b
  have hmin : minpoly Y x = X ^ 2 - C (a : Y) :=
    (minpoly.eq_of_irreducible_of_monic hirr heval (monic_X_pow_sub_C _ two_ne_zero)).symm
  have hdeg : (minpoly Y x).natDegree = 2 := by rw [hmin, natDegree_X_pow_sub_C _]
  have hfin : Module.finrank Y Y⟮x⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField Y⟮x⟯ := NumberField.of_module_finite Y _
  have hconj : x ∈ GlobalTheory.CMSub.conjStable Ω := by
    have hφ : ∀ φ : Ω →+* ℂ, (φ x) ^ 2 = (a : ℂ) := fun φ => by rw [← map_pow, hx, map_intCast]
    rcases le_total 0 a with ha | ha
    · exact ⟨x, fun φ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonneg _ a (hφ φ) ha⟩
    · exact ⟨-x, fun φ => by rw [map_neg]; exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonpos _ a (hφ φ) ha⟩
  have hle : Y⟮x⟯ ≤ GlobalTheory.CMSub.conjField Y Ω := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hconj
  have cm : IsCMField Y⟮x⟯ := GlobalTheory.CMSub.isCMField_of_le _ hle
  have hxK : x ∈ Y⟮x⟯ := IntermediateField.mem_adjoin_simple_self Y x
  have hspan : ∀ y : Y⟮x⟯, ∃ b c : Y, y = algebraMap Y Y⟮x⟯ b + algebraMap Y Y⟮x⟯ c * ⟨x, hxK⟩ := by
    intro y
    obtain ⟨f, hf, rfl⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y
    rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have hf' : f = C (f.coeff 1) * X + C (f.coeff 0) := Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    rw [hf', map_add (f := _), map_mul, aeval_C, aeval_C, aeval_X, IntermediateField.adjoin.powerBasis_gen, add_comm]
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, coeff_C_zero, coeff_C_succ, mul_zero, mul_one, zero_add, add_zero]
    rfl
  refine ⟨⟨Y⟮x⟯, nf, cm, hfin⟩, hxK, hspan, ?_⟩
  intro F _ _ h hY hhx y
  obtain ⟨b, c, rfl⟩ := hspan y
  have hb : ∀ e : Y, h (algebraMap Y Ω e) = algebraMap Y Ω e := hY
  show h ((algebraMap Y Ω b) + (algebraMap Y Ω c) * x) = (algebraMap Y Ω b) + (algebraMap Y Ω c) * x
  rw [map_add (f := _), map_mul, hb, hb, hhx]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecGen
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem valuation_apply_le_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (x : Ω) (hx : A.valuation x ≤ 1) : A.valuation (e x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  have h2 := ValuationSubring.smul_mem_pointwise_smul e x A hx
  open Pointwise in
  have h3 : e • A = A := he
  rw [h3] at h2
  exact h2

private theorem valuation_apply_lt_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (z : Ω) (hz : A.valuation z < 1) : A.valuation (e z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hz
  have hez : e z ≠ 0 := by simpa using hz0
  have key : 1 < A.valuation z⁻¹ := by
    rw [Valuation.one_lt_val_iff _ (inv_ne_zero hz0), inv_inv]
    exact hz
  have h1 : 1 < A.valuation (e z)⁻¹ := by
    by_contra hc
    push_neg at hc
    have h4 := valuation_apply_le_one_of_mem_dec A e⁻¹ (inv_mem he) _ hc
    have h5 : e⁻¹ (e z)⁻¹ = z⁻¹ := by
      rw [map_inv₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [h5] at h4
    exact absurd key (not_lt.mpr h4)
  rw [Valuation.one_lt_val_iff _ (inv_ne_zero hez), inv_inv] at h1
  exact h1

private theorem inv_mul_mul_mem_ine_of_mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (d τ : G F Ω) (hd : d ∈ Dec A) (hτ : τ ∈ Ine A) :
    d⁻¹ * τ * d ∈ Ine A := by
  have hτD : τ ∈ Dec A := Ine_le_Dec A hτ
  obtain ⟨_, hτ2⟩ := hτ
  refine ⟨(Dec A).mul_mem ((Dec A).mul_mem ((Dec A).inv_mem hd) hτD) hd, fun x hx => ?_⟩
  have h1 := hτ2 (d x) (valuation_apply_le_one_of_mem_dec A d hd x hx)
  have h2 := valuation_apply_lt_one_of_mem_dec A d⁻¹ ((Dec A).inv_mem hd) _ h1
  have e : (d⁻¹ * τ * d) x - x = d⁻¹ (τ (d x) - d x) := by
    rw [map_sub, ← AlgEquiv.mul_apply d⁻¹ d, inv_mul_cancel, AlgEquiv.one_apply, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply]
  rw [e]
  exact h2

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.decGen :
    DecGen := by
  intro F Ω _ _ _ _ _ A v hAv φ hφ X hX hXI g hg
  set Y : Set Ω := {y | ∀ τ ∈ Ine (F := F) A, τ y = y} with hYdef
  have hφD : φ ∈ Dec A := hφ.1
  have hstab : ∀ (k : ℤ) (y : Ω), y ∈ Y → (φ ^ k) y ∈ Y := by
    intro k y hy τ hτ
    have h1 := hy _ (inv_mul_mul_mem_ine_of_mem_dec A (φ ^ k) τ (zpow_mem hφD k) hτ)
    have h2 := congrArg (φ ^ k) h1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply (φ ^ k) (φ ^ k)⁻¹,
      mul_inv_cancel, AlgEquiv.one_apply] at h2
    exact h2
  let φ' : Dec A := ⟨φ, hφD⟩
  have hdense := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hAv φ' hφ
  have hP : ∀ h ∈ (Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)),
      ∃ k : ℤ, ∀ y ∈ Y, (h : G F Ω) y = (φ ^ k) y := by
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨k, fun y _ => by rw [Subgroup.coe_zpow]⟩
      · refine ⟨0, fun y hy => ?_⟩
        rw [zpow_zero, AlgEquiv.one_apply]
        exact hy _ (Subgroup.mem_subgroupOf.mp hx)
    | one => exact ⟨0, fun y _ => by rw [zpow_zero]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, fun z hz => ?_⟩
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hb z hz, ha _ (hstab b z hz), zpow_add,
        AlgEquiv.mul_apply]
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨-a, fun z hz => ?_⟩
      have hw := ha _ (hstab (-a) z hz)
      have e1 : (φ ^ a) ((φ ^ (-a)) z) = z := by
        rw [← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply]
      rw [e1] at hw
      rw [Subgroup.coe_inv]
      calc ((x : G F Ω)⁻¹) z = ((x : G F Ω)⁻¹) ((x : G F Ω) ((φ ^ (-a)) z)) := by rw [hw]
        _ = (φ ^ (-a)) z := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Finite X := hX.to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F X) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let O : Set (Dec A) := Subtype.val ⁻¹' ((fun σ : G F Ω => g⁻¹ * σ) ⁻¹'
    ((IntermediateField.adjoin F X).fixingSubgroup : Set (G F Ω)))
  have hO : IsOpen O :=
    ((IntermediateField.adjoin F X).fixingSubgroup_isOpen.preimage (continuous_const_mul g⁻¹)).preimage
      continuous_subtype_val
  have hgO : (⟨g, hg⟩ : Dec A) ∈ O := by
    show g⁻¹ * g ∈ (IntermediateField.adjoin F X).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  have hmem : (⟨g, hg⟩ : Dec A) ∈
      ((Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)).topologicalClosure : Set (Dec A)) := by
    rw [hdense]
    exact Subgroup.mem_top _
  rw [Subgroup.topologicalClosure_coe] at hmem
  obtain ⟨h, hhO, hhK⟩ := (mem_closure_iff.mp hmem) O hO hgO
  obtain ⟨k, hk⟩ := hP h hhK
  refine ⟨k, fun x hx => ?_⟩
  have hfix : g⁻¹ * (h : G F Ω) ∈ (IntermediateField.adjoin F X).fixingSubgroup := hhO
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix x
    (IntermediateField.subset_adjoin F X hx)
  have hxY : x ∈ Y := fun τ hτ => hXI τ hτ x hx
  rw [← hk x hxY]
  have h2 := congrArg g h1
  rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
  exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameQuot

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem decPow : DecPow := by
  intro F Ω _ _ _ _ _ A t hA p hp hpt ζ hζ
  have hN : ¬ A.valuation (p : Ω) < 1 := by
    simpa using not_valuation_lt_one_of_isPlaceOver hpt hA 1
  have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
  have hint : ζ ∈ IntCl F Ω :=
    IsIntegral.of_pow hp.pos (by rw [hz1]; exact isIntegral_one)
  have hv : A.valuation ζ ≤ 1 := by
    have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
    exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
  refine ⟨fun g hg => ?_, fun τ hτ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_pow_cong hA hg {⟨ζ, hint⟩}
    refine ⟨i, eq_of_pow_eq_one A hN ?_ ?_ (hi ⟨ζ, hint⟩ (Finset.mem_singleton_self _))⟩
    · rw [← map_pow, hz1, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
  · exact eq_of_pow_eq_one A hN (by rw [← map_pow, hz1, map_one]) hz1 ((mem_Ine.1 hτ).2 ζ hv)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshChar
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem chi_of_pow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (k : ℕ) (h : g ζ = ζ ^ k) :
    ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  have h1 := hζ.autToPow_spec F g
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨p, (Fact.out : p.Prime).pos, hζ.pow_eq_one⟩
  rw [h, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1

private theorem chi_one {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (h : g ζ = ζ) : hζ.autToPow F g = 1 := by
  apply Units.ext
  rw [chi_of_pow hζ g 1 (by rw [h, pow_one])]
  simp

private theorem exists_prim {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (p : Ω) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

private theorem chi_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (j : Ω →+* ℂ) (c : G F Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    hζ.autToPow F c = -1 := by
  have hp := (Fact.out : p.Prime)
  have hw : (j ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hp.ne_zero
  have hcz : c ζ = ζ ^ (p - 1) := by
    apply j.injective
    rw [hc, ← Complex.inv_eq_conj hn, map_pow]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hw]
  apply Units.ext
  rw [chi_of_pow hζ c (p - 1) hcz, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self]
  simp

private theorem good_ker {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ}
    [Fact p.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (lam : (ZMod p)ˣ →* ℂˣ) (h1 : lam (-1) = 1) :
    Good (lam.comp (hζ.autToPow F)).ker := by
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  refine ⟨?_, Abelianization.commutator_subset_ker _, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (G F Ω) ζ) ?_
      (stabilizer_isOpen_of_isIntegral (K := F) ζ)
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_one hζ g hg, map_one]
  · intro j c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_conj hζ j c hc, h1]

private theorem lam_pow {p n : ℕ} [Fact p.Prime] (lam : (ZMod p)ˣ →* ℂˣ) (hn : lam ^ n = 1) (a : (ZMod p)ˣ) :
    lam a ^ n = 1 := by
  rw [← MonoidHom.pow_apply, hn, MonoidHom.one_apply]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshChar :
    PowChar → InertiaGen → DecPow → FreshPrime → FreshChar := by
  intro hPow hIG hDP hFP F Ω _ _ _ _ _ U hU T hT n hn
  obtain ⟨u, huT, hpr, hpu, hpu2, hdec, hdvd, hTt⟩ := hFP F Ω U hU T hT n hn
  haveI : Fact (Nat.Prime (normV u)) := ⟨hpr⟩
  obtain ⟨lam, hlamn, hlam1, hlamord⟩ := hPow (normV u) n hn hdvd
  obtain ⟨ζ, hζ⟩ := exists_prim (F := F) (Ω := Ω) (normV u)
  refine ⟨lam.comp (hζ.autToPow F), good_ker hζ lam hlam1, ?_, ?_, u, huT, hpr, ?_, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, lam_pow lam hlamn, MonoidHom.one_apply]
  · intro t ht A hA g hg
    obtain ⟨hpt, b, hb⟩ := hTt t ht
    obtain ⟨hD, -⟩ := hDP F Ω A t hA (normV u) hpr hpt ζ hζ
    obtain ⟨k, hk⟩ := hD g hg
    have hχ := chi_of_pow hζ g _ hk
    push_cast at hχ
    rw [← hb] at hχ
    rw [MonoidHom.comp_apply]
    by_cases hb0 : b = 0
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [pow_zero] at hχ
        rw [show hζ.autToPow F g = 1 from Units.ext (by simpa using hχ), map_one]
      · exfalso
        rw [hb0, zero_pow hn.ne', zero_pow hk0.ne'] at hχ
        exact (Units.ne_zero _) hχ
    · have hunit : hζ.autToPow F g = (Units.mk0 b hb0) ^ (n * k) :=
        Units.ext (by rw [hχ]; simp [pow_mul])
      rw [hunit, map_pow, pow_mul, lam_pow lam hlamn, one_pow]
  · intro A hA
    refine ⟨hdec A hA, ?_⟩
    obtain ⟨τ, hτ, a, ha, hτz⟩ := hIG F Ω A u hA (normV u) hpu hpu2 ζ hζ
    refine ⟨τ, hτ, ?_⟩
    have hχ := chi_of_pow hζ τ _ hτz
    rw [ZMod.natCast_zmod_val] at hχ
    rw [MonoidHom.comp_apply, show hζ.autToPow F τ = a from Units.ext hχ]
    exact hlamord a ha
  · intro t A hA hpt τ hτ
    obtain ⟨-, hI⟩ := hDP F Ω A t hA (normV u) hpr hpt ζ hζ
    rw [MonoidHom.comp_apply, chi_one hζ τ (hI τ hτ), map_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshPrime
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private lemma normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show 0 < Nat.card (𝓞 F ⧸ t.asIdeal)
  rw [h]
  exact Nat.pos_of_ne_zero (fun h0 => t.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

private lemma normV_mem' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show ((Nat.card (𝓞 F ⧸ t.asIdeal) : ℕ) : 𝓞 F) ∈ t.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshPrime :
    SplitPlace → RootMod → FreshPrime := by
  intro hS hR
  unfold SplitPlace at hS
  unfold RootMod at hR
  unfold FreshPrime
  intro F Ω _ _ _ _ _ U hU T hT n hn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((2 * n : ℕ)) : Ω) := ⟨by exact_mod_cast (by omega : 2 * n ≠ 0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 * n)
  have hroot : ∀ t : HeightOneSpectrum (𝓞 F), ∃ x : Ω, x ^ n = (normV t : Ω) :=
    fun t => IsAlgClosed.exists_pow_nat_eq _ hn
  choose y hy using hroot
  set S : Set Ω := insert ζ (y '' T) with hSeq
  haveI : Finite S := (Set.Finite.insert ζ (hT.image y)).to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral)
  set U' : Subgroup (G F Ω) := U ⊓ (IntermediateField.adjoin F S).fixingSubgroup with hU'eq
  have hU' : IsOpen (U' : Set (G F Ω)) := by
    rw [hU'eq, Subgroup.coe_inf]
    exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hfix : ∀ g : G F Ω, g ∈ U' → ∀ x ∈ S, (g : Ω → Ω) x = x := by
    intro g hg x hx
    have hg2 := (Subgroup.mem_inf.mp hg).2
    exact (mem_fixingSubgroup_iff _).mp hg2 x (IntermediateField.subset_adjoin F S hx)
  have hfinset : ∀ a : 𝓞 F, a ≠ 0 → {w : HeightOneSpectrum (𝓞 F) | a ∈ w.asIdeal}.Finite := by
    intro a ha
    have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact ha
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors h0
  have hcast : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 F) ≠ 0 := fun m hm => by exact_mod_cast hm
  set B : Set (HeightOneSpectrum (𝓞 F)) :=
    T ∪ (⋃ t ∈ T, {w | ((normV t : ℕ) : 𝓞 F) ∈ w.asIdeal}) ∪ {w | ((2 * n : ℕ) : 𝓞 F) ∈ w.asIdeal}
    with hBeq
  have hB : B.Finite := by
    refine (hT.union (hT.biUnion fun t _ => hfinset _ (hcast _ (normV_pos' t).ne'))).union ?_
    exact hfinset _ (hcast _ (by omega))
  obtain ⟨u, huB, hp, hpu, hpu2, hdec⟩ := hS F Ω U' hU' B hB
  have hdvd_mem : ∀ m : ℕ, normV u ∣ m → ((m : ℕ) : 𝓞 F) ∈ u.asIdeal := by
    rintro m ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpu
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
  have hDA : ∀ x ∈ S, ∀ g ∈ Dec A, (g : Ω → Ω) x = x := fun x hx g hg => hfix g (hdec A hA hg) x hx
  refine ⟨u, fun h => huB (Or.inl (Or.inl h)), hp, hpu, hpu2,
    fun A' hA' => le_trans (hdec A' hA') inf_le_left, ?_, ?_⟩
  · refine (hR F Ω A u hA (normV u) hp rfl ζ (2 * n) (by omega) (hDA ζ (Set.mem_insert _ _))).2 hζ ?_
    intro h2
    exact huB (Or.inr (hdvd_mem _ h2))
  · intro t ht
    refine ⟨?_, (hR F Ω A u hA (normV u) hp rfl (y t) n hn
      (hDA (y t) (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩))).1 (normV t) (hy t)⟩
    intro hut
    by_cases hd : normV u ∣ normV t
    · exact huB (Or.inl (Or.inr (Set.mem_biUnion ht (hdvd_mem _ hd))))
    · have hcop : Nat.Coprime (normV u) (normV t) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
      have hg := Nat.gcd_eq_gcd_ab (normV u) (normV t)
      rw [hcop] at hg
      have hg' := congrArg (Int.cast : ℤ → 𝓞 F) hg
      push_cast at hg'
      have h1 : (1 : 𝓞 F) ∈ t.asIdeal := by
        rw [hg']
        exact t.asIdeal.add_mem (Ideal.mul_mem_right _ _ hut) (Ideal.mul_mem_right _ _ (normV_mem' t))
      exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.IndexComap
section
namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem indexComap : IndexComap := by
  intro Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩
  have hN : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H' :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact H'.mul_mem h1 hn
  rw [Subgroup.relIndex_comap]
  set J := (H.comap f).map f with hJ
  have hJH : J ≤ H := Subgroup.map_comap_le _ _
  have hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)
  rw [Subgroup.relIndex_sup_left] at hmul
  have hne : H'.relIndex J ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hτ' (h ⟨τ, hτ, rfl⟩)
  exact (hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

