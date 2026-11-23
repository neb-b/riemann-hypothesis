module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnits
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NormUnits

theorem fg_quot_intUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    Group.FG (B.Aˣ ⧸ intUnits K.O B.A) := fun K B hP =>
  haveI := _root_.GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P K B hP
  _root_.GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg K (_root_.GlobalTheory.FieldUnitsQuotFG.fg_units_quot K) B.A (_root_.GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P K B hP)

theorem exists_finset_sq_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : Group.FG (G ⧸ N)) :
    ∃ F : Finset G, ∀ u : G, u ^ 2 ∈ N → ∃ f ∈ F, u * f⁻¹ ∈ N := by
  let M := Additive (G ⧸ N)
  haveI : AddGroup.FG M := inferInstance
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let K2 : Submodule ℤ M := LinearMap.ker (LinearMap.lsmul ℤ M 2)
  haveI : Module.Finite ℤ K2 := Module.IsNoetherian.finite ℤ K2
  haveI : Finite K2 := Module.finite_of_fg_torsion K2 (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, by
    apply Subtype.ext; have h := x.2; rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at h
    simpa using h⟩)
  let r : K2 → G := fun k => Quotient.out (Additive.toMul (k : M))
  refine ⟨(Set.finite_range r).toFinset, fun u hu => ?_⟩
  have hk : (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) ∈ K2 := by
    show (2 : ℤ) • (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) = 0
    rw [← ofMul_zpow]
    show Additive.ofMul ((QuotientGroup.mk u : G ⧸ N) ^ (2 : ℤ)) = Additive.ofMul 1
    congr 1
    rw [zpow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]; exact hu
  refine ⟨r ⟨_, hk⟩, by simp, ?_⟩
  have h1 : (QuotientGroup.mk (r ⟨_, hk⟩) : G ⧸ N) = QuotientGroup.mk u := by
    simp only [r]; exact Quotient.out_eq' _
  have := QuotientGroup.eq.mp h1.symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

theorem exists_finset_normUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ,
    (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  intro K B hP
  let N : Subgroup B.Aˣ := B.T ⊔ intUnits K.O B.A
  have hFG : Group.FG (B.Aˣ ⧸ N) :=
    haveI := fg_quot_intUnits K B hP
    Group.fg_of_surjective (f := QuotientGroup.map (intUnits K.O B.A) N (MonoidHom.id _) le_sup_right)
      (fun q => QuotientGroup.induction_on q fun x => ⟨QuotientGroup.mk x, rfl⟩)
  obtain ⟨F, hF⟩ := exists_finset_sq_mem N hFG
  refine ⟨F, fun u ⟨w, hw, hwu⟩ => ?_⟩
  let su : B.Aˣ := Units.map (B.σ : B.A →* B.A) u
  have hsu : (su : B.A) = B.σ u := rfl
  have ht : u * su⁻¹ ∈ B.T := by
    show ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A) = 1
    have h1 : B.σ ((su⁻¹ : B.Aˣ) : B.A) * u = 1 := by
      have : B.σ ((su⁻¹ : B.Aˣ) : B.A) * B.σ (su : B.A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rwa [hsu, B.σ_σ] at this
    calc ((u * su⁻¹ : B.Aˣ) : B.A) * B.σ ((u * su⁻¹ : B.Aˣ) : B.A)
        = (B.σ ((su⁻¹ : B.Aˣ) : B.A) * u) * ((su : B.A) * ((su⁻¹ : B.Aˣ) : B.A)) := by
          simp only [Units.val_mul, map_mul]; rw [hsu]; ring
      _ = 1 := by rw [h1, Units.mul_inv, one_mul]
  have hsq : u ^ 2 ∈ N := by
    have : u ^ 2 = (u * su⁻¹) * w := by
      ext; rw [Units.val_mul, hwu, ← hsu]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul]
      calc (u : B.A) ^ 2 = (u : B.A) * u * (((su⁻¹ : B.Aˣ) : B.A) * su) := by rw [Units.inv_mul, mul_one, sq]
        _ = _ := by ring
    rw [this]; exact N.mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hw)
  obtain ⟨f, hfF, hf⟩ := hF u hsq
  obtain ⟨t, htT, z, hz, htz⟩ := Subgroup.mem_sup.mp hf
  refine ⟨f, hfF, t, htT, ?_⟩
  have : u * f⁻¹ * t⁻¹ = z := by rw [← htz, mul_comm t z, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]; exact hz

end GlobalTheory.NormUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbit
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem orbit_stab_cut_finite (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω) :
    ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  classical
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef
  have hS : S.Finite := by
    refine ((minpoly E y).rootSet_finite Ω).subset ?_
    rintro t ⟨τ, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv]
    simp [minpoly.aeval]
  set O := hS.toFinset with hOdef
  have hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t := fun t => by simp [O, S]
  set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP
  refine ⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩
  have key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔
      P.map (σ : Ω →+* Ω) = P := by
    constructor
    · intro h
      ext n
      rw [coeff_map]
      by_cases hn : n ≤ P.natDegree
      · exact h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]; simp
    · intro h x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
  have hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t)) := by
    simp [hP, Polynomial.map_prod]
  rw [key, hmap]
  constructor
  · intro h τ hτ
    have h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)
    rw [h, hP, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, ht0⟩ := h0
    obtain ⟨τ', hτ', rfl⟩ := (hmemO t).1 ht
    refine ⟨τ', hτ', ?_⟩
    simpa [sub_eq_zero] using ht0
  · intro h
    have hinj : Function.Injective (σ : Ω → Ω) := σ.injective
    have hsub : O.image σ ⊆ O := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨τ, hτ, rfl⟩ := (hmemO t).1 ht
      obtain ⟨τ', hτ', he⟩ := h τ hτ
      exact (hmemO _).2 ⟨τ', hτ', he.symm⟩
    have heq : O.image σ = O :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
    calc ∏ t ∈ O, (X - C (σ t)) = ∏ u ∈ O.image σ, (X - C u) :=
          by
          rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
      _ = P := by rw [heq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroup
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_finset_fix_subset_of_isOpen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)),
    IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A,
      (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  intro E Ω _ _ _ _ _ A M hM
  obtain ⟨U, hU, hUM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : G E Ω) ∈ U := by
    have : (1 : Ine (F := E) A) ∈ (Subtype.val ⁻¹' U) := by rw [hUM]; exact M.one_mem
    simpa using this
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds h1)
  have hfg : L.toSubalgebra.FG := by
    apply Subalgebra.fg_of_fg_toSubmodule
    exact Module.Finite.iff_fg.mp hL
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun σ hσ => ?_⟩
  have hmem : (σ : G E Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ Algebra.adjoin E (t : Set Ω) := by rw [ht]; exact hx
    have key : Set.EqOn ((σ : G E Ω) : Ω →ₐ[E] Ω) (AlgHom.id E Ω) (Algebra.adjoin E (t : Set Ω)) :=
      AlgHom.eqOn_adjoin_iff.mpr (fun y hy => hσ y hy)
    exact key hx'
  have : σ ∈ (Subtype.val ⁻¹' U : Set (Ine (F := E) A)) := hLU hmem
  rw [hUM] at this
  exact this

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixingActsAsFrobeniusPowerResidue
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Pointwise

namespace GlobalTheory.GaloisLift

theorem cong_pow_of_cong_pow_int (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) {σ : G E Ω} (hdec : σ ∈ Dec (F := E) A) {q : ℕ}
    (hcong : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b ^ q) < 1) :
    ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  have hdec' : σ • A = A := hdec
  intro x hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hcs := hcong s hs
  have hct := hcong t ht
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[E] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec'] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

theorem lift_resAut_of_fixes (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (K : IntermediateField E Ω) [FiniteDimensional E K]
    (σ₀ : G E Ω) (hσ₀ : σ₀ ∈ Dec (F := E) A)
    (hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1) :
    ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ρ ∈ Dec (F := E) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (ρ b - σ₀ b) < 1 := by
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set Q := primeBelow (F := K) A with hQ
  set P := Q.under (𝓞 K) with hP
  haveI : Q.LiesOver P := ⟨rfl⟩

  have hint : ∀ (g : G E Ω) (b : IntCl K Ω), IsIntegral (𝓞 K) (g (b : Ω)) := fun g b =>
    ((isIntegral_int_of_isIntegral b.2).map (g.toAlgHom.restrictScalars ℤ)).tower_top
  let e : IntCl K Ω ≃+* IntCl K Ω :=
    { toFun := fun b => ⟨σ₀ b, hint σ₀ b⟩
      invFun := fun b => ⟨σ₀⁻¹ b, hint σ₀⁻¹ b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (mul_inv_apply (b : Ω))
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have he : ∀ b : IntCl K Ω, ((e b : IntCl K Ω) : Ω) = σ₀ b := fun _ => rfl
  have hQe : Q = Q.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap]
    show A.valuation (b : Ω) < 1 ↔ A.valuation (σ₀⁻¹ (b : Ω)) < 1
    exact (valuation_apply_lt_one_iff ((Dec (F := E) A).inv_mem hσ₀) _).symm
  let ψ₀ : (IntCl K Ω ⧸ Q) ≃+* (IntCl K Ω ⧸ Q) := Ideal.quotientEquiv Q Q e hQe
  have hψ₀ : ∀ b, ψ₀ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (e b) := fun _ => rfl
  have hlin : ∀ x : 𝓞 K ⧸ P, ψ₀ (algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x) =
      algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hψ₀, Ideal.Quotient.eq]
    have hz : ((algebraMap (𝓞 K) (IntCl K Ω) a : IntCl K Ω) : Ω) ∈ K := ((a : K)).2
    have := hK _ hz (valuation_le_one_intCl A _)
    exact this
  let ψ : (IntCl K Ω ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (IntCl K Ω ⧸ Q) := AlgEquiv.ofRingEquiv (f := ψ₀) hlin
  obtain ⟨⟨ρ₀, hρ₀Q⟩, hρ₀⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) P Q ψ
  have hρ₀Q' : ρ₀ • Q = Q := hρ₀Q
  have hcong : ∀ b : IntCl K Ω, A.valuation (ρ₀ (b : Ω) - σ₀ b) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ₀ • b) = Ideal.Quotient.mk Q (e b) :=
      DFunLike.congr_fun hρ₀ (Ideal.Quotient.mk Q b)
    have h2 : ρ₀ • b - e b ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
    exact h2
  have hdec : ρ₀ • A = A := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (ρ₀ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρ₀Q']
  refine ⟨ρ₀.restrictScalars E, fun z hz => ρ₀.commutes ⟨z, hz⟩, ?_, fun b hb => hcong ⟨b, hb.tower_top⟩⟩
  show (ρ₀.restrictScalars E) • A = A
  conv_rhs => rw [← hdec]
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_fixing_actsAs : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  intro E Ω _ _ _ _ _ A w h K _ d hd j hdK
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hφ1 : ActsAs A (normV w) φ 1 0 := actsAs_one_iff.mpr hφ
  have hpow : ∀ n : ℕ, ActsAs A (normV w) (φ ^ n) n 0 := by
    intro n
    induction n with
    | zero => exact ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
    | succ n ih => simpa [pow_succ] using ih.mul hφ1
  have hφj := hpow j
  set σ₀ : G E Ω := d⁻¹ * φ ^ j with hσ₀def
  have hσ₀ : σ₀ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hφj.1
  have hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1 := by
    intro z hz hz1
    rw [← valuation_apply_lt_one_iff hd, map_sub]
    have e1 : d (σ₀ z) = (φ ^ j) z := by
      rw [hσ₀def, AlgEquiv.mul_apply, mul_inv_apply]
    rw [e1]
    have h1 := hφj.2 z hz1
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (cong_symm (hdK z hz hz1))
  obtain ⟨ρ, hρK, hρA, hρc⟩ := lift_resAut_of_fixes E Ω A K σ₀ hσ₀ hK
  set τ : G E Ω := σ₀⁻¹ * ρ with hτdef
  have hτ : τ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hσ₀) hρA
  have hτc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (τ b - b ^ 1) < 1 := by
    intro b hb
    rw [pow_one, ← valuation_apply_lt_one_iff hσ₀, map_sub]
    have e3 : σ₀ (τ b) = ρ b := mul_inv_apply (ρ b)
    rw [e3]
    exact hρc b hb
  have hτI : ActsAs A (normV w) τ 0 0 :=
    ⟨hτ, fun x hx => by simpa using cong_pow_of_cong_pow_int E Ω A hτ hτc x hx⟩
  refine ⟨ρ, hρK, ?_⟩
  have e2 : d * ρ = φ ^ j * τ := by
    rw [hτdef, hσ₀def]; group
  rw [e2]
  simpa using hφj.mul hτI

end GlobalTheory.GaloisLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerMapIsIntegralUnramifiedInvolutionEx
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem intMap_isIntegral_of_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  intro K K' d φ hU
  obtain ⟨φO, hφO⟩ := exists_intMap_of_unr hU
  refine ⟨φO, hφO, ?_⟩
  letI : Algebra K.O K'.O := φO.toAlgebra
  obtain ⟨u, hu⟩ := exists_int_basis_of_unr K K' d φ hU
  have hspan : Submodule.span K.O (Set.range u) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      change φ (algebraMap K.O K.E (a i)) * _ = algebraMap K'.O K'.E (φO (a i)) * _
      rw [hφO]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Module.Finite K.O K'.O := ⟨Submodule.fg_def.2 ⟨_, Set.finite_range u, hspan⟩⟩
  exact Algebra.IsIntegral.of_finite K.O K'.O

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicBasePolynomialRootNearDecomposition
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_monic_base_root_near : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  intro E Ω _ _ _ _ _ A hdense f hf hfix β hβ r hr
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set n := f.natDegree with hn
  have hvr : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have hvrn : A.valuation r ^ n ≠ 0 := pow_ne_zero _ hvr
  have happ : ∀ i, ∃ e : E,
      A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i < A.valuation r ^ n := by
    intro i
    by_cases hb : β = 0
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · obtain ⟨e, he⟩ := hdense (f.coeff 0) (fun d hd => hfix d hd 0) (r ^ n) (pow_ne_zero _ hr)
        exact ⟨e, by simpa [map_pow] using he⟩
      · refine ⟨0, ?_⟩
        simp only [hb, map_zero, zero_pow hi.ne', mul_zero]
        exact zero_lt_iff.mpr hvrn
    · have hbi : β ^ i ≠ 0 := pow_ne_zero _ hb
      obtain ⟨e, he⟩ := hdense (f.coeff i) (fun d hd => hfix d hd i) (r ^ n / β ^ i)
        (div_ne_zero (pow_ne_zero _ hr) hbi)
      refine ⟨e, ?_⟩
      have hvb : A.valuation β ^ i ≠ 0 := by
        rw [← map_pow]; exact (Valuation.ne_zero_iff _).mpr hbi
      rw [map_div₀, map_pow, map_pow] at he
      calc A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i
          < A.valuation r ^ n / A.valuation β ^ i * A.valuation β ^ i :=
            mul_lt_mul_of_pos_right he (zero_lt_iff.mpr hvb)
        _ = A.valuation r ^ n := div_mul_cancel₀ _ hvb
  choose c hc using happ
  let p : E[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : p.degree < n := degree_sum_fin_lt _
  let g : E[X] := X ^ n + p
  have hgm : g.Monic := monic_X_pow_add hp
  have hgd : g.natDegree = n := by
    show (X ^ n + p).natDegree = n
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have h0 : f.eval β = β ^ n + ∑ i ∈ Finset.range n, f.coeff i * β ^ i := by
    conv_lhs => rw [hf.as_sum]
    simp [Polynomial.eval_finsetSum, ← hn]
  have hga : aeval β g = β ^ n + ∑ i ∈ Finset.range n, algebraMap E Ω (c i) * β ^ i := by
    show aeval β (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_pow, aeval_X, map_sum, map_mul, aeval_C]
    rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap E Ω (c i) * β ^ i) n]
  have hgβ : aeval β g = ∑ i ∈ Finset.range n, (algebraMap E Ω (c i) - f.coeff i) * β ^ i := by
    have : aeval β g = aeval β g - f.eval β := by rw [hβ, sub_zero]
    rw [this, hga, h0]
    simp [sub_mul, Finset.sum_sub_distrib]
  have hvg : A.valuation (aeval β g) < A.valuation r ^ n := by
    rw [hgβ]
    refine Valuation.map_sum_lt _ hvrn fun i _ => ?_
    rw [map_mul, map_pow]; exact hc i
  set G := g.map (algebraMap E Ω) with hG
  have hGm : G.Monic := hgm.map _
  have hGd : G.natDegree = n := by rw [hG, natDegree_map, hgd]
  have hprod : (G.roots.map fun a => X - C a).prod = G :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGm IsAlgClosed.card_roots_eq_natDegree
  have hev : aeval β g = (G.roots.map fun a => β - a).prod := by
    rw [aeval_def, ← eval_map, ← hG]
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hex : ∃ a ∈ G.roots, A.valuation (β - a) < A.valuation r := by
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation r ^ n ≤ A.valuation (aeval β g) := by
      rw [hev, map_multiset_prod, Multiset.map_map]
      have hcard : (G.roots.map (A.valuation ∘ fun a => β - a)).card = n := by
        rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hGd]
      calc A.valuation r ^ n = A.valuation r ^ (G.roots.map (A.valuation ∘ fun a => β - a)).card := by
            rw [hcard]
        _ ≤ _ := Multiset.pow_card_le_prod (by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
            exact hcon a ha)
    exact absurd hvg (not_lt.mpr h1)
  obtain ⟨a, ha, hva⟩ := hex
  refine ⟨g, hgm, hgd, a, ?_, ?_⟩
  · have := (mem_roots hGm.ne_zero).mp ha
    rw [aeval_def, ← eval_map]; exact this
  · rwa [Valuation.map_sub_swap]

end GlobalTheory.WeilDeligne
end

