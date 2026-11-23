module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

section Fix

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
  [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω]

theorem natCast_mem_of_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (g n : ℕ)
    (hn : 0 < n) (hN : normV v = g ^ n) : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 K ⧸ v.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (pow_eq_zero_iff hn.ne').1 hc

theorem fix_of_ine (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) (e : E') : σ (algebraMap E' Ω e) = algebraMap E' Ω e := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let LL := IntermediateField.normalClosure E E' Ω
  have : NumberField (LL) :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap E (LL)).injective
      to_finiteDimensional := Module.Finite.trans E (LL) }
  have : IsGalois E' (LL) := IsGalois.tower_top_of_isGalois E E' (LL)
  have hmem : ∀ x : 𝓞 (LL), (((x : LL) : Ω)) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.2).map (IsScalarTower.toAlgHom ℤ (LL) Ω))
  let ψ : 𝓞 (LL) →+* A :=
    { toFun := fun x => ⟨((x : LL) : Ω), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let P : Ideal (𝓞 (LL)) := (IsLocalRing.maximalIdeal A).comap ψ
  have hP : ∀ x : 𝓞 (LL), x ∈ P ↔ A.valuation (((x : LL) : Ω)) < 1 := fun x => A.valuation_lt_one_iff (ψ x)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hcE : ∀ x : 𝓞 E, (((algebraMap (𝓞 E) (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E Ω (x : E) :=
    fun x => rfl
  have hcE' : ∀ x : 𝓞 E', (((algebraMap (𝓞 E') (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E' Ω (x : E') :=
    fun x => rfl
  have : P.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE]
    exact (h x).symm⟩
  have : P.LiesOver w'.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE']
    exact (h' x).symm⟩
  have : w'.asIdeal.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, ← h' _, ← h x]
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E Ω (x : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (x : E)).symm
    rw [e1]⟩
  have : IsGaloisGroup (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) E (LL)
  have : IsGaloisGroup (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) E' (LL)
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E] LL) w.asIdeal P
  have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E'] LL) w'.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal P (LL ≃ₐ[E] LL)] at c1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w'.asIdeal P (LL ≃ₐ[E'] LL)] at c2
  have tower := Ideal.ramificationIdx_tower (R := 𝓞 E) w'.asIdeal P
  have hcard : Nat.card (P.inertia (LL ≃ₐ[E] LL)) ≤ Nat.card (P.inertia (LL ≃ₐ[E'] LL)) := by
    rw [c1, c2, tower, he, one_mul]
  let f : P.inertia (LL ≃ₐ[E'] LL) → P.inertia (LL ≃ₐ[E] LL) := fun τ => ⟨τ.1.restrictScalars E, fun x => τ.2 x⟩
  have hf : Function.Injective f := fun τ τ' hτ =>
    Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ))
  have hbij := hf.bijective_of_nat_card_le hcard
  let σb : LL ≃ₐ[E] LL := σ.restrictNormal (LL)
  have hcomm : ∀ y : LL, ((σb y : LL) : Ω) = σ ((y : LL) : Ω) := fun y => AlgEquiv.restrictNormal_commutes σ (LL) y
  have hσb : σb ∈ P.inertia (LL ≃ₐ[E] LL) := fun x => by
    show σb • x - x ∈ P
    rw [hP]
    have e2 : (((σb • x - x : 𝓞 (LL)) : LL) : Ω) = ((σb (x : LL) : LL) : Ω) - ((x : LL) : Ω) := rfl
    rw [e2, hcomm]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hmem x))
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨σb, hσb⟩
  have hτ' : τ.1.restrictScalars E = σb := congrArg Subtype.val hτ
  have key : σb (algebraMap E' (LL) e) = algebraMap E' (LL) e := by
    rw [← hτ']
    exact τ.1.commutes e
  have e5 : (((algebraMap E' (LL) e : LL)) : Ω) = algebraMap E' Ω e := rfl
  rw [← e5, ← hcomm, key]

end Fix

theorem ine_lift {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ t : G E' Ω, t ∈ Ine (F := E') A ∧ AlgEquiv.restrictScalars E t = σ := by
  have hgw' := natCast_mem_of_normV w' g n hn hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    intro _
    have hmap : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal ^ 2 := fun hle => hg (by
      have := hle (Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hgw)
      rwa [map_natCast] at this)
    have hlt := Ideal.ramificationIdx'_lt hmap
    rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal w'.asIdeal w.ne_bot] at hlt
    have hpos := Ideal.ramificationIdx_pos (R := 𝓞 E) w'.asIdeal
    omega
  have hfix := fix_of_ine A w h w' h' he σ hσ
  let t : G E' Ω := { σ.toRingEquiv with commutes' := hfix }
  refine ⟨t, ⟨?_, fun x hx => hσ.2 x hx⟩, AlgEquiv.ext fun x => rfl⟩
  show t • A = A
  have hd : σ • A = A := hσ.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
section
noncomputable section

open GlobalTheory.GLq
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

theorem sum_rho_eq_zero {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) (U : Subgroup G) {_ : Fintype U}
    (h : ∑ u : U, τ.character (u : G) = 0) : ∑ u : U, τ.ρ (u : G) = 0 := by
  obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ τ, E = ∑ u : U, τ.ρ (u : G) := ⟨_, rfl⟩
  rw [← hE]
  have hinv : ∀ v : U, τ.ρ (v : G) * E = E := by
    intro v
    rw [hE, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun u => ?_
    simp [map_mul]
  have hsq : E * E = (Fintype.card U : ℂ) • E := by
    calc E * E = ∑ u : U, τ.ρ (u : G) * E := by nth_rewrite 1 [hE]; rw [Finset.sum_mul]
      _ = ∑ _u : U, E := Finset.sum_congr rfl fun u _ => hinv u
      _ = (Fintype.card U : ℂ) • E := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have htE : LinearMap.trace ℂ τ E = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, map_sum]
    exact h
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ τ, P = (Fintype.card U : ℂ)⁻¹ • E := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hP, smul_mul_assoc, mul_smul_comm, hsq, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hproj : LinearMap.IsProj (LinearMap.range P) P :=
    ⟨fun x => LinearMap.mem_range_self P x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact congrArg (fun f : Module.End ℂ τ => f y) hPP⟩
  have htP : LinearMap.trace ℂ τ P = 0 := by
    rw [hP, map_smul, htE, smul_zero]
  rw [hproj.trace, Nat.cast_eq_zero, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at htP
  calc E = (Fintype.card U : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = 0 := by rw [htP, smul_zero]

variable {g : ℕ} [Fact g.Prime]

theorem res_eq {n a : ℕ} (ha : a < n) (χ : Gn g n → ℂ) :
    res a (n - a) χ 1 1 = ((g : ℂ) ^ (a * (n - a)))⁻¹ *
      ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a), χ (u : Gn g n) := by
  unfold res
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => x ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g)
    (GlobalTheory.FiniteGL.twoBlocks n a)) _ (fun x => by rw [GlobalTheory.SerSys.TameGen.mem_unipRadical_iff ha]; simp) χ]

theorem sum_unip_eq_zero {n a : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) (h0 : 0 < a) (ha : a < n) :
    ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a), τ.ρ (u : Gn g n) = 0 := by
  refine sum_rho_eq_zero τ _ ?_
  have hres := hτ.2.2 a h0 ha
  rw [res_eq ha] at hres
  refine (mul_eq_zero.1 hres).resolve_left ?_
  have : (g : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  exact inv_ne_zero (pow_ne_zero _ this)

end DiscreteGroups.sglob.DzLc
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTame
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}

theorem val_lt_iff_of_dec {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {a b : Ω} (hb : b ≠ 0) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  have hb' : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have h1 : 0 < A.valuation b := (Valuation.pos_iff _).mpr hb
  have h2 : 0 < A.valuation (σ b) := (Valuation.pos_iff _).mpr hb'
  rw [← div_lt_one₀ h1, ← div_lt_one₀ h2, ← map_div₀ A.valuation (σ a), ← map_div₀ A.valuation a, ← map_div₀ σ]
  exact valuation_apply_lt_one_iff hσ (a / b)

theorem val_apply_eq {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (x : Ω) : A.valuation (σ x) = A.valuation x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have key : ∀ τ ∈ Dec (F := E) A, ∀ y : Ω, y ≠ 0 → A.valuation (τ y) < A.valuation y → False := by
    intro τ hτ y hy hlt
    have hne : ∀ k : ℕ, (τ ^ k) y ≠ 0 := fun k => (map_ne_zero _).mpr hy
    have hdec : ∀ k : ℕ, A.valuation ((τ ^ (k + 1)) y) < A.valuation ((τ ^ k) y) := by
      intro k
      induction k with
      | zero => simpa using hlt
      | succ k ih =>
        have := (val_lt_iff_of_dec hτ (hne k)).mpr ih
        simpa only [← AlgEquiv.mul_apply, ← pow_succ'] using this
    have hanti : StrictAnti fun k : ℕ => A.valuation ((τ ^ k) y) := strictAnti_nat_of_succ_lt hdec
    have hinj : Function.Injective fun k : ℕ => (τ ^ k) y := fun i j hij =>
      hanti.injective (by simp only at hij ⊢; rw [hij])
    have hint : IsIntegral E y := (Algebra.IsAlgebraic.isAlgebraic (R := E) y).isIntegral
    have hfin := (minpoly E y).rootSet_finite Ω
    apply Set.infinite_of_injective_forall_mem hinj (s := (minpoly E y).rootSet Ω) ?_ hfin
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [show (τ ^ k) y = ((τ ^ k : G E Ω) : Ω →ₐ[E] Ω) y from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero]
  rcases lt_trichotomy (A.valuation (σ x)) (A.valuation x) with h | h | h
  · exact (key σ hσ x hx h).elim
  · exact h
  · refine (key σ⁻¹ ((Dec (F := E) A).inv_mem hσ) (σ x) ((map_ne_zero σ).mpr hx) ?_).elim
    rwa [show (σ⁻¹ : G E Ω) (σ x) = x by simp]

theorem val_ratio {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) : A.valuation (σ x / x) = 1 := by
  rw [map_div₀, val_apply_eq hσ, div_self ((Valuation.ne_zero_iff _).mpr hx)]

theorem ratio_cong {σ ψ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (hψ : ψ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) :
    A.valuation (σ (ψ x) / ψ x - σ x / x) < 1 := by
  set y := ψ x / x with hy
  have hy1 : A.valuation y = 1 := val_ratio hψ hx
  have hy0 : y ≠ 0 := by intro h; rw [h, map_zero] at hy1; exact zero_ne_one hy1
  have hψx : ψ x = x * y := by rw [hy]; field_simp
  have hσx0 : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  have hσy0 : σ y ≠ 0 := (map_ne_zero σ).mpr hy0
  have e : σ (ψ x) / ψ x - σ x / x = (σ x / x) * ((σ y - y) / y) := by
    rw [hψx, map_mul]; field_simp
  rw [e, map_mul, val_ratio (Ine_le_Dec A hσ) hx, one_mul, map_div₀, hy1, div_one]
  exact hσ.2 y hy1.le

def ratioUnit {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) : Aˣ where
  val := ⟨σ x / x, (A.valuation_le_one_iff _).mp (val_ratio hσ hx).le⟩
  inv := ⟨x / σ x, (A.valuation_le_one_iff _).mp (by
    rw [map_div₀, val_apply_eq hσ, div_self ((Valuation.ne_zero_iff _).mpr hx)])⟩
  val_inv := by
    have : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    apply Subtype.ext; show σ x / x * (x / σ x) = 1; field_simp
  inv_val := by
    have : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    apply Subtype.ext; show x / σ x * (σ x / x) = 1; field_simp

theorem res_eq_of_cong {a b : A} (h : A.valuation ((a : Ω) - b) < 1) :
    IsLocalRing.residue A a = IsLocalRing.residue A b := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  simpa using h

def tameSym {x : Ω} (hx : x ≠ 0) : Ine (F := E) A →* (IsLocalRing.ResidueField A)ˣ where
  toFun σ := Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (ratioUnit (Ine_le_Dec A σ.2) hx)
  map_one' := by
    ext
    show IsLocalRing.residue A ⟨(1 : G E Ω) x / x, _⟩ = 1
    rw [← map_one (IsLocalRing.residue A)]
    congr 1
    apply Subtype.ext
    show (1 : G E Ω) x / x = 1
    simp [hx]
  map_mul' σ τ := by
    ext
    show IsLocalRing.residue A ⟨(σ * τ : G E Ω) x / x, _⟩ =
      IsLocalRing.residue A ⟨(σ : G E Ω) x / x, _⟩ * IsLocalRing.residue A ⟨(τ : G E Ω) x / x, _⟩
    rw [← map_mul]
    apply res_eq_of_cong
    show A.valuation ((σ * τ : G E Ω) x / x - (σ : G E Ω) x / x * ((τ : G E Ω) x / x)) < 1
    have hτx : (τ : G E Ω) x ≠ 0 := (map_ne_zero _).mpr hx
    have e : (σ * τ : G E Ω) x / x - (σ : G E Ω) x / x * ((τ : G E Ω) x / x) =
        ((σ : G E Ω) ((τ : G E Ω) x) / (τ : G E Ω) x - (σ : G E Ω) x / x) * ((τ : G E Ω) x / x) := by
      rw [AlgEquiv.mul_apply]; field_simp
    rw [e, map_mul, val_ratio (Ine_le_Dec A τ.2) hx, mul_one]
    exact ratio_cong σ.2 (Ine_le_Dec A τ.2) hx

theorem isWild_of_tameSym {σ : Ine (F := E) A} (h : ∀ (x : Ω) (hx : x ≠ 0), tameSym hx σ = 1) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) := by
  refine ⟨σ.2, fun x hx => ?_⟩
  have h1 := congrArg Units.val (h x hx)
  change IsLocalRing.residue A ⟨(σ : G E Ω) x / x, _⟩ = IsLocalRing.residue A 1 at h1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h1
  have h2 : A.valuation ((σ : G E Ω) x / x - 1) < 1 := by simpa using h1
  have hv : 0 < A.valuation x := (Valuation.pos_iff _).mpr hx
  have e : (σ : G E Ω) x - x = ((σ : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  calc A.valuation ((σ : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x :=
        mul_lt_mul_of_pos_right h2 hv
    _ = A.valuation x := one_mul _

theorem isWild_frob {q : ℕ} {φ : G E Ω} (hφ : IsFrob A q φ) (s : Ine (F := E) A) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A (((⟨φ * s * φ⁻¹, conj_mem_Ine hφ.1 s.2⟩ : Ine (F := E) A) * (s ^ q)⁻¹ :
      Ine (F := E) A) : G E Ω) := by
  refine isWild_of_tameSym fun x hx => ?_
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
  ext
  show IsLocalRing.residue A ⟨(φ * (s : G E Ω) * φ⁻¹) x / x, _⟩ = (IsLocalRing.residue A ⟨(s : G E Ω) x / x, _⟩) ^ q
  rw [← map_pow]
  apply res_eq_of_cong
  show A.valuation ((φ * (s : G E Ω) * φ⁻¹) x / x - ((s : G E Ω) x / x) ^ q) < 1
  have hφD : φ ∈ Dec (F := E) A := hφ.1
  have hφiD : φ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hφD
  set y := (φ⁻¹ : G E Ω) x with hy
  have hy0 : y ≠ 0 := (map_ne_zero _).mpr hx
  have hxy : x = φ y := by rw [hy, mul_inv_apply]
  have e1 : (φ * (s : G E Ω) * φ⁻¹) x / x = φ ((s : G E Ω) y / y) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hy, map_div₀]
    conv_lhs => rw [show x = φ y from hxy]
  have hz : A.valuation ((s : G E Ω) y / y) ≤ 1 := (val_ratio (Ine_le_Dec A s.2) hy0).le
  have c1 : A.valuation (φ ((s : G E Ω) y / y) - ((s : G E Ω) y / y) ^ q) < 1 := hφ.2 _ hz
  have c2 : A.valuation ((s : G E Ω) y / y - (s : G E Ω) x / x) < 1 := ratio_cong s.2 hφiD hx
  have c3 := cong_pow hz (val_ratio (Ine_le_Dec A s.2) hx).le c2 q
  rw [e1]
  exact cong_trans c1 c3

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
section
noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

open Polynomial GlobalTheory GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.SerSys.TameGen CategoryTheory
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def TameParamLe (b : ℕ) (L : LabelDatum g) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) : Prop :=
  ∀ ρ : GLRep g, ρ.1 ≤ b → IsSC ρ → ∀ (τ : FDRep ℂ (Gn g ρ.1)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    Inflates ρ.2.ρ τ → ine (rec ρ) = liftPoly L.teich P

def PinnedLe (b : ℕ) (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) :
    Prop :=
  ∀ ρ : GLRep g, ρ.1 ≤ b → IsSC ρ → ∀ τ : FDRep ℂ (Gn g ρ.1), Simple τ → FiniteGL.IsCuspidal τ.ρ →
    Inflates ρ.2.ρ τ → ∀ f, Representation.asAlgebraHom τ.ρ (S.e ρ.1 f) = 1 → ine (rec ρ) = liftPoly teich f

theorem InInd.rank_le {π : GLRep g} {T : List (GLRep g)} (h : InInd π T) : ∀ ρ ∈ T, ρ.1 ≤ π.1 := by
  induction h with
  | nil π _ _ => intro ρ hρ; simp at hρ
  | cons π σ ρ T _ _ _ hm ih =>
    intro ρ' hρ'
    have e : π.1 = σ.1 + ρ.1 := hm.1
    rcases List.mem_cons.1 hρ' with rfl | h'
    · omega
    · have := ih ρ' h'
      omega

theorem ine_eq_of_isSC_le (b : ℕ) (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {LP : Type} (ine : LP → ℂ[X])
    (rec : GLRep g → LP) (h2 : DepthZeroCuspidal g) (h3 : PinnedLe b S teich ine rec) (ρ : GLRep g) (hb : ρ.1 ≤ b)
    (hρ : IsSC ρ) (f : (ZMod g)[X]) (h : Has S ρ.2.ρ f) : ine (rec ρ) = liftPoly teich f := by
  obtain ⟨τ, φ, hs, hinj, heq, he⟩ := exists_simple_of_has S _ f h
  have hφ : (fixK1 ρ.2.ρ).subtype ∘ₗ φ ≠ 0 := fun e => by
    have h0 : ∀ u : τ, u = 0 := fun u => hinj (Subtype.ext (by simpa using LinearMap.congr_fun e u))
    exact id_nonzero τ (by ext u; exact (h0 _).trans (h0 _).symm)
  have hfix : fixK1 ρ.2.ρ ≠ ⊥ := fun e => hφ (LinearMap.ext fun u => (Submodule.eq_bot_iff _).1 e _ (φ u).2)
  refine h3 ρ hb hρ τ hs (fun c hc hc' u hu => hinj ?_) ⟨_, hφ, fun k w => ?_⟩ f he
  · rw [map_zero]
    exact h2 ρ hρ hfix c hc hc' _ fun x hx => by rw [← heq, hu x hx]
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, heq, repK_red]

theorem ine_eq_of_has_le (b : ℕ) (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) (LP : Type) (ine : LP → ℂ[X])
    (rec : GLRep g → LP) (h1 : SupportCompat ine rec) (h2 : DepthZeroCuspidal g) (h3 : PinnedLe b S teich ine rec)
    (π : GLRep g) (hb : π.1 ≤ b) (hπ : IsIrrRep π.2.ρ) (hs : PRep.IsSmooth π.2.ρ) (f : (ZMod g)[X])
    (h : Has S π.2.ρ f) : ine (rec π) = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod := by
  obtain ⟨L, hL, hsc, he⟩ := h1 π hπ hs
  have hbL : ∀ ρ ∈ L, ρ.1 ≤ b := fun ρ hρ => (InInd.rank_le hL ρ hρ).trans hb
  obtain ⟨fs, hfs, rfl⟩ := _root_.GlobalTheory.SerSys.has_prod_of_inInd g S π L hL f h
  rw [he]
  change _ = liftPoly teich fs.prod
  clear he hL h
  suffices fs.prod.Monic ∧ (L.map fun ρ => ine (rec ρ)).prod = liftPoly teich fs.prod from this.2
  induction hfs with
  | nil => simp [liftPoly_one]
  | @cons ρ f L fs hρ _ ih =>
    obtain ⟨hm, ih⟩ := ih (fun ρ' h' => hsc ρ' (List.mem_cons_of_mem _ h'))
      (fun ρ' h' => hbL ρ' (List.mem_cons_of_mem _ h'))
    refine ⟨by simpa using (Has.monic hρ).mul hm, ?_⟩
    rw [List.map_cons, List.prod_cons, List.prod_cons, liftPoly_mul _ (Has.monic hρ).ne_zero hm.ne_zero, ih,
      ine_eq_of_isSC_le b S teich ine rec h2 h3 ρ (hbL ρ List.mem_cons_self) (hsc ρ List.mem_cons_self) f hρ]

theorem pinned_of_green_le (b : ℕ) (S : Sys g) (L : LabelDatum g) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP)
    (hG : Green) (hT : TameParamLe b L ine rec) (hS : LabelsCusp S L) : PinnedLe b S L.teich ine rec := by
  intro ρ hb hρ τ hs hc hi f he
  obtain ⟨t, h1, -, h3⟩ := hG g L ρ.1 hρ.1
  obtain ⟨P, hP, e⟩ := h3 _ (isCusp_character hρ.1 τ hs hc)
  have hP' : IsCuspOf L P τ.character := e ▸ (h1 P hP).1
  have : f = P := by
    by_contra hne
    apply hS _ τ P hP'
    rw [← one_mul (Representation.asAlgebraHom τ.ρ _), ← he, ← map_mul, S.orth _ _ _ hne, map_zero]
  rw [this]
  exact hT ρ hb hρ τ P hP' hi

theorem ine_eq_of_has_green_le (b : ℕ) (S : Sys g) (L : LabelDatum g) (LP : Type) (ine : LP → ℂ[X])
    (rec : GLRep g → LP) (h1 : SupportCompat ine rec) (h2 : DepthZeroCuspidal g) (hG : Green)
    (hT : TameParamLe b L ine rec) (hS : LabelsCusp S L) (π : GLRep g) (hb : π.1 ≤ b) (hπ : IsIrrRep π.2.ρ)
    (hs : PRep.IsSmooth π.2.ρ) (f : (ZMod g)[X]) (h : Has S π.2.ρ f) :
    ine (rec π) = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (L.teich x)).prod :=
  ine_eq_of_has_le b S L.teich LP ine rec h1 h2 (pinned_of_green_le b S L ine rec hG hT hS) π hb hπ hs f h

end DiscreteGroups.sglob.DzType.Rt

end
end

