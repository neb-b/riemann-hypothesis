module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteDvrExtensionEmbeddingResidueField
section
namespace GlobalTheory

open Polynomial IsLocalRing

theorem exists_finite_dvr_algHom_mem_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (θ : K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ θ ∈ Set.range e := by
  let k := ResidueField B
  letI : Algebra k K := (ResidueField.lift (algebraMap B K)).toAlgebra
  have : IsScalarTower B k K := .of_algebraMap_eq fun b =>
    (ResidueField.lift_residue_apply (algebraMap B K) b).symm
  have hθ : IsIntegral k θ := (Algebra.IsIntegral.isIntegral (R := B) θ).tower_top
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hθ)
  let B' := AdjoinRoot μ
  have hμθ : aeval θ μ = 0 := by
    rw [← aeval_map_algebraMap k]
    exact (congrArg (aeval θ) hμ).trans (minpoly.aeval k θ)
  let e : B' →ₐ[B] K := AdjoinRoot.liftAlgHom μ (Algebra.ofId B K) θ hμθ
  have he₀ : e (AdjoinRoot.root μ) = θ := AdjoinRoot.liftAlgHom_root ..
  have he : ∀ g : B[X], e (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, he₀]
  have hu : ∀ y : B', e y ≠ 0 → IsUnit y := fun y hy => by
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
    exact isUnit_adjoinRoot_mk_of_aeval_ne_zero hθ hμm hμ (he g ▸ hy)
  have : Nontrivial B' := e.toRingHom.domain_nontrivial
  have : IsLocalRing B' := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => by
    by_cases hy : e y = 0
    · exact Or.inr (hu _ (by simp [hy]))
    · exact Or.inl (hu _ hy)
  have hm : ∀ y : B', y ∈ maximalIdeal B' ↔ e y = 0 := fun y =>
    ⟨fun hy => by_contra fun h => hy (hu y h), fun hy h => (h.map e).ne_zero hy⟩
  have hfin : Module.Finite B B' := hμm.finite_adjoinRoot
  have : Module.Free B B' := hμm.free_adjoinRoot
  have hmap : (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) fun y hy => ?_
    · rw [Ideal.mem_comap, hm, AlgHom.commutes, algebraMap_eq_zero_iff_mem_maximalIdeal (K := K)]
      exact hb
    · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [hm, he, ← aeval_map_algebraMap k] at hy
      obtain ⟨c, hc⟩ := minpoly.dvd k θ hy
      obtain ⟨c, rfl⟩ := map_surjective (algebraMap B k) residue_surjective c
      have h₀ : (g - μ * c).map (algebraMap B k) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hμ, hc, sub_self]
      have h₁ : AdjoinRoot.mk μ (g - μ * c) ∈ (maximalIdeal B).map (algebraMap B B') := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [(g - μ * c).as_sum_support_C_mul_X_pow, map_sum]
        refine Ideal.sum_mem _ fun i _ => ?_
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        change algebraMap B B' _ ∈ _
        refine Ideal.mem_map_of_mem _ ?_
        rw [← residue_eq_zero_iff]
        change algebraMap B k _ = 0
        rw [← coeff_map, h₀, coeff_zero]
      rwa [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero] at h₁
  have : IsNoetherianRing B' := IsNoetherianRing.of_finite B B'
  obtain ⟨_, _⟩ := exists_isDiscreteValuationRing_of_flat B B' hmap
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B').ne_top)
  have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := B) B'
  rw [hmap] at hc
  exact ⟨B', inferInstance, inferInstance, inferInstance, hc, inferInstance, hfin,
    FaithfulSMul.algebraMap_injective B B', e, ⟨fun y hy => hu y hy.ne_zero⟩,
    AdjoinRoot.root μ, he₀⟩

theorem exists_finite_dvr_algHom_subset_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (s : Finset K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ (s : Set K) ⊆ Set.range e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, fun _ _ h => h, Algebra.ofId B K, ‹IsLocalHom (algebraMap B K)›, by simp⟩
  | insert θ s _ ih =>
    obtain ⟨C, _, _, _, _, _, hfin, hinj, e, hloc, hs⟩ := ih
    letI : Algebra C K := (e : C →+* K).toAlgebra
    have : IsScalarTower B C K := .of_algebraMap_eq fun b => (e.commutes b).symm
    have : IsLocalHom (algebraMap C K) := hloc
    have : Module.Finite C K := .of_restrictScalars_finite B C K
    obtain ⟨D, _, _, _, _, _, hfin', hinj', e', hloc', hθ⟩ :=
      exists_finite_dvr_algHom_mem_range (B := C) θ
    letI : Algebra B D := ((algebraMap C D).comp (algebraMap B C)).toAlgebra
    have : IsScalarTower B C D := .of_algebraMap_eq fun _ => rfl
    refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.Finite.trans C D, hinj'.comp hinj, e'.restrictScalars B, hloc', ?_⟩
    rw [Finset.coe_insert]
    refine Set.insert_subset hθ fun x hx => ?_
    obtain ⟨c, rfl⟩ := hs hx
    exact ⟨algebraMap C D c, e'.commutes c⟩

theorem exists_finite_dvr_residueField_ringHom :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] (k' : Type) [Field k'] [Algebra (ResidueField W) k'] [FiniteDimensional (ResidueField W) k'], ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W') (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'), Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ ∃ e : k' →+* ResidueField W', ∀ v : W, e (algebraMap (ResidueField W) k' (residue W v)) = residue W' (algebraMap W W' v) := by
  intro W _ _ _ _ K _ _ _
  letI : Algebra W K := ((algebraMap (ResidueField W) K).comp (residue W)).toAlgebra
  have : IsScalarTower W (ResidueField W) K := .of_algebraMap_eq fun _ => rfl
  have : IsLocalHom (algebraMap W K) := ⟨fun b hb => by
    by_contra hn
    exact hb.ne_zero ((algebraMap_eq_zero_iff_mem_maximalIdeal (K := K) b).mpr hn)⟩
  have hfin : Module.Finite W K := Module.Finite.trans (ResidueField W) K
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨W', _, _, _, _, _, hfin', hinj, e, hloc, hsub⟩ :=
    exists_finite_dvr_algHom_subset_range (B := W) s
  have hsurj : Function.Surjective e := fun x => by
    have : x ∈ LinearMap.range e.toLinearMap := by
      have h : Submodule.span W (s : Set K) ≤ LinearMap.range e.toLinearMap :=
        Submodule.span_le.mpr hsub
      exact h (hs ▸ Submodule.mem_top)
    exact this
  let f : ResidueField W' →+* K := ResidueField.lift (e : W' →+* K)
  have hf : ∀ w, f (residue W' w) = e w := fun w => ResidueField.lift_residue_apply _ w
  have hbij : Function.Bijective f := ⟨f.injective, fun x => by
    obtain ⟨w, rfl⟩ := hsurj x
    exact ⟨_, hf w⟩⟩
  refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfin',
    hinj, (RingEquiv.ofBijective f hbij).symm, fun v => ?_⟩
  refine (RingEquiv.symm_apply_eq _).mpr ?_
  rw [RingEquiv.ofBijective_apply, hf, e.commutes]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowEqFractionRingOfPderivEqZero
section
open scoped BigOperators

namespace GlobalTheory.CubeFib

theorem exists_pow_eq_of_pderiv_eq_zero {k : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {σ : Type} [DecidableEq σ] (F : MvPowerSeries σ k)
    (hF : ∀ i, MvPowerSeries.pderiv (R := k) i F = 0) : ∃ g : MvPowerSeries σ k, g ^ p = F := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  let g : MvPowerSeries σ k :=
    fun d => (frobeniusEquiv k p).symm (MvPowerSeries.coeff (p • d) F)
  have hg : ∀ d, MvPowerSeries.coeff d g =
      (frobeniusEquiv k p).symm (MvPowerSeries.coeff (p • d) F) := fun d => rfl
  refine ⟨g, ?_⟩
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext n
  rw [MvPowerSeries.coeff_map]
  by_cases! h : ∀ i, p ∣ n i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = n := ⟨n.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, hg]
    exact (frobeniusEquiv k p).apply_symm_apply _
  · obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have hni : n i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ n := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (n - Finsupp.single i 1)) (hF i)
    rw [MvPowerSeries.coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have h2 : (((n - Finsupp.single i 1 : σ →₀ ℕ) i : k) + 1) = (n i : k) := by
      rw [← Nat.cast_succ]; congr 1; simp; omega
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact h3.symm
    · exact absurd ((CharP.cast_eq_zero_iff k p _).mp h3) hi

theorem derivation_mem_pow_smul_top {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) (I : Ideal A) (m : ℕ) :
    ∀ a ∈ I ^ (m + 1), D a ∈ (I ^ m • ⊤ : Submodule A M) := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [Derivation.leibniz]
      refine add_mem (Submodule.smul_mem_smul hx Submodule.mem_top) ?_
      rw [pow_succ', ← smul_eq_mul, Submodule.smul_assoc]
      exact Submodule.smul_mem_smul hy (ih x hx)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

theorem derivation_algebraMap_perfect {k K : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [Field K] [Algebra k K] (D : Derivation ℤ K K) (c : k) :
    D (algebraMap k K c) = 0 := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨b, rfl⟩ := (frobeniusEquiv k p).surjective c
  rw [frobeniusEquiv_apply, frobenius_def, map_pow, Derivation.leibniz_pow, nsmul_eq_mul,
    CharP.cast_eq_zero, zero_mul]

theorem derivation_eq_zero_of_kaehler {k A K : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [CommRing A] [Algebra k A] [Field K] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] (f : A) (hd : KaehlerDifferential.D k A f = 0) (D : Derivation ℤ K K) :
    D (algebraMap A K f) = 0 := by
  let L : A →ₗ[k] K :=
    { toFun := fun a => D (algebraMap A K a)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [Algebra.smul_def, map_mul, Derivation.leibniz,
          ← IsScalarTower.algebraMap_apply, derivation_algebraMap_perfect p D c, smul_zero,
          add_zero, RingHom.id_apply, Algebra.smul_def c, smul_eq_mul] }
  let D' : Derivation k A K := Derivation.mk' L (fun a b => by
    change D (algebraMap A K (a * b)) =
      a • D (algebraMap A K b) + b • D (algebraMap A K a)
    rw [map_mul, Derivation.leibniz, Algebra.smul_def a, Algebra.smul_def b, smul_eq_mul,
      smul_eq_mul])
  have h := D'.liftKaehlerDifferential_comp_D f
  rw [hd, map_zero] at h
  exact h.symm

theorem exists_pow_eq_fractionRing_of_pderiv_eq_zero : ∀ (k : Type) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A] [Algebra.EssFiniteType k A] (σ : Type) [Fintype σ] [DecidableEq σ] (j : A →ₐ[k] MvPowerSeries σ k), (∀ (m : ℕ) (a : A), j a ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ m ↔ a ∈ IsLocalRing.maximalIdeal A ^ m) → (∀ (m : ℕ) (s : MvPowerSeries σ k), ∃ a : A, j a - s ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ m) → ∀ f : A, (∀ i, MvPowerSeries.pderiv (R := k) i (j f) = 0) → ∃ h : FractionRing A, h ^ p = algebraMap A (FractionRing A) f := by
  intro k _ _ p _ _ A _ _ _ _ _ σ _ _ j hj hsurj f hf
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  haveI : CharP (FractionRing A) p :=
    charP_of_injective_algebraMap (algebraMap k (FractionRing A)).injective p
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : CharP (MvPowerSeries σ k) p :=
    charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p
  obtain ⟨g, hg⟩ := exists_pow_eq_of_pderiv_eq_zero p (j f) hf
  have hd : KaehlerDifferential.D k A f = 0 := by
    have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Ω[A⁄k])
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    rw [← Submodule.mem_bot A, ← key, Submodule.mem_iInf]
    intro m
    obtain ⟨a, ha⟩ := hsurj (m + 1) g
    have h1 : a ^ p - f ∈ IsLocalRing.maximalIdeal A ^ (m + 1) := by
      rw [← hj, map_sub, map_pow, ← hg, ← sub_pow_char]
      exact Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)
    have h2 := derivation_mem_pow_smul_top (KaehlerDifferential.D k A) _ m _ h1
    rw [map_sub, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero,
      zero_smul, zero_sub] at h2
    exact (neg_mem_iff).mp h2
  apply GlobalTheory.T.exists_pth_root_of_derivation_zero
  intro D
  exact derivation_eq_zero_of_kaehler p f hd D

end GlobalTheory.CubeFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorialWeightedPairingDetPowProportional
section
open ReciprocityTheory.PGsh MvPolynomial

namespace GlobalTheory.DetPowPairing

section General

variable {C : Type} [CommRing C] {κ : Type}

noncomputable def pairing (F : MvPolynomial κ C) : MvPolynomial κ C →ₗ[C] C :=
  ∑ A ∈ F.support, (AddMonoidAlgebra.coeff F A * (A.prod fun _ e => (e.factorial : C))) • lcoeff C A

end General

variable {C : Type} [CommRing C] {n : ℕ}

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_eq_sum_factorial (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing F G =
      ∑ A ∈ F.support, AddMonoidAlgebra.coeff F A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff G A := by
  rw [_root_.GlobalTheory.DetPowPairing.pairing, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]

open MvPolynomial in
variable {C : Type} [CommRing C] in
private theorem exists_cayOp_pow_cayDet_pow (n k Y : ℕ) :
    ∃ c : ℕ, (_root_.ReciprocityTheory.PGsh.cayOp n C ^ k) (_root_.ReciprocityTheory.PGsh.cayDet n C ^ Y) = c • _root_.ReciprocityTheory.PGsh.cayDet n C ^ (Y - k) := by
  induction k generalizing Y with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (Y - 1)
    have hC := _root_.ReciprocityTheory.PGsh.cayley
    unfold _root_.ReciprocityTheory.PGsh.CayleyStatement at hC
    refine ⟨(∏ j ∈ Finset.range n, (Y + j)) * c, ?_⟩
    rw [pow_succ, Module.End.mul_apply, hC, map_nsmul, hc, smul_smul]
    have : Y - 1 - k = Y - (k + 1) := by omega
    rw [this]

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_eq_sum_of_support_subset (F G : MvPolynomial κ C)
    (S : Finset (κ →₀ ℕ)) (hS : F.support ⊆ S) :
    _root_.GlobalTheory.DetPowPairing.pairing F G =
      ∑ A ∈ S, AddMonoidAlgebra.coeff F A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff G A := by
  rw [pairing_eq_sum_factorial]
  refine Finset.sum_subset hS fun A _ hA => ?_
  have h : AddMonoidAlgebra.coeff F A = 0 := by simpa using hA
  rw [h]; ring

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_comm' (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing F G = _root_.GlobalTheory.DetPowPairing.pairing G F := by
  classical
  rw [pairing_eq_sum_of_support_subset F G (F.support ∪ G.support)
      Finset.subset_union_left,
    pairing_eq_sum_of_support_subset G F (F.support ∪ G.support)
      Finset.subset_union_right]
  exact Finset.sum_congr rfl fun _ _ => by ring

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_monomial_eq_coeff_mul_prod_factorial_mul (F : MvPolynomial κ C) (A : κ →₀ ℕ) (b : C) :
    _root_.GlobalTheory.DetPowPairing.pairing F (monomial A b) =
      AddMonoidAlgebra.coeff F A * (A.prod fun _ e => (e.factorial : C)) * b := by
  classical
  rw [pairing_eq_sum_of_support_subset F _ (insert A F.support)
      (Finset.subset_insert _ _), Finset.sum_eq_single A]
  · rw [coeff_monomial, if_pos rfl]
  · intro B _ hB
    rw [coeff_monomial, if_neg (Ne.symm hB)]; ring
  · intro h; exact absurd (Finset.mem_insert_self _ _) h

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem prod_factorial_add_single_one_eq_succ_mul_prod_factorial (B : κ →₀ ℕ) (x : κ) :
    ((B + Finsupp.single x 1).prod fun _ e => (e.factorial : C)) =
      ((B x + 1 : ℕ) : C) * (B.prod fun _ e => (e.factorial : C)) := by
  classical
  have h1 : (B + Finsupp.single x 1).support ⊆ insert x B.support := by
    intro y hy
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      have hxy' : x ≠ y := Ne.symm hxy
      simpa [Finsupp.single_apply, hxy'] using hy
  rw [Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset B (Finset.subset_insert x B.support) _ (fun _ _ => by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self x B.support),
    ← Finset.mul_prod_erase _ (fun y => ((B y).factorial : C)) (Finset.mem_insert_self x B.support)]
  have h2 : ∏ y ∈ (insert x B.support).erase x, (((B + Finsupp.single x 1 : κ →₀ ℕ) y).factorial : C) =
      ∏ y ∈ (insert x B.support).erase x, ((B y).factorial : C) := by
    refine Finset.prod_congr rfl fun y hy => ?_
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    have hxy : x ≠ y := Ne.symm hyx
    simp [Finsupp.single_apply, hxy]
  rw [h2]
  simp [Nat.factorial_succ]
  ring

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_X_mul_eq_pairing_pderiv (x : κ) (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing (X x * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F (pderiv x G) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial A b =>
    rw [pairing_monomial_eq_coeff_mul_prod_factorial_mul, pderiv_monomial, pairing_monomial_eq_coeff_mul_prod_factorial_mul,
      coeff_X_mul']
    by_cases hx : A x = 0
    · have : x ∉ A.support := by simpa using hx
      rw [if_neg this, hx]; simp
    · rw [if_pos (by simpa using hx)]
      have hA : A = (A - Finsupp.single x 1) + Finsupp.single x 1 := by
        ext y
        by_cases hy : x = y
        · subst hy; simp; omega
        · simp [Finsupp.single_apply, hy]
      have hAx : (A - Finsupp.single x 1 : κ →₀ ℕ) x + 1 = A x := by simp; omega
      have hf : (A.prod fun _ e => (e.factorial : C)) =
          ((A x : ℕ) : C) * ((A - Finsupp.single x 1).prod fun _ e => (e.factorial : C)) := by
        conv_lhs => rw [hA]
        rw [prod_factorial_add_single_one_eq_succ_mul_prod_factorial, hAx]
      rw [hf]; ring
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

open MvPolynomial in
variable {C : Type} [CommRing C] {κ : Type} in
private theorem pairing_list_prod_X_mul_eq_pairing_list_prod_pderiv {ι : Type} (g : ι → κ) (L : List ι)
    (F G : MvPolynomial κ C) :
    _root_.GlobalTheory.DetPowPairing.pairing ((L.map fun j => X (g j)).prod * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F
        ((L.map fun j => ((pderiv (g j) : Derivation C (MvPolynomial κ C) (MvPolynomial κ C)).toLinearMap :
          Module.End C (MvPolynomial κ C))).prod G) := by
  induction L generalizing F with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc, mul_left_comm, ih,
      pairing_X_mul_eq_pairing_pderiv, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

open MvPolynomial in
variable {C : Type} [CommRing C] in
private theorem pairing_cayDet_mul' (n : ℕ) (F G : MvPolynomial (Fin n × Fin n) C) :
    _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n C * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F (_root_.ReciprocityTheory.PGsh.cayOp n C G) := by
  unfold _root_.ReciprocityTheory.PGsh.cayDet _root_.ReciprocityTheory.PGsh.cayOp _root_.ReciprocityTheory.PGsh.cayMono
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.det_apply, Finset.sum_mul, pairing_comm', map_sum,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, smul_mul_assoc, map_zsmul, LinearMap.smul_apply, map_zsmul,
    pairing_comm']
  congr 1
  have hprod : ∏ i, Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i =
      ((List.finRange n).map fun j => X (σ j, j)).prod := by
    rw [Fin.prod_univ_def]; rfl
  rw [hprod, pairing_list_prod_X_mul_eq_pairing_list_prod_pderiv (fun j => (σ j, j))]

open MvPolynomial in
variable {C : Type} [CommRing C] in
private theorem pairing_cayDet_pow_mul (n k : ℕ) (F G : MvPolynomial (Fin n × Fin n) C) :
    _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n C ^ k * F) G =
      _root_.GlobalTheory.DetPowPairing.pairing F ((_root_.ReciprocityTheory.PGsh.cayOp n C ^ k) G) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, ih, pairing_cayDet_mul', pow_succ', Module.End.mul_apply]


open MvPolynomial in
variable {C : Type} [CommRing C] {n : ℕ} in
theorem _root_.GlobalTheory.DetPowPairing.pairing_pow_proportional :
  (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * Q) A) * (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) A) = (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) * (∑ A ∈ (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) A)) := by
  intro C _ _ n₀ M Y Q hMY _
  simp only [← pairing_eq_sum_factorial]
  obtain ⟨c, hc⟩ := exists_cayOp_pow_cayDet_pow (C := C) n₀ (Y - M) Y
  have hYM : Y - (Y - M) = M := by omega
  rw [hYM] at hc
  have e1 : _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * Q) =
      c * _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) Q := by
    rw [pairing_comm', pairing_cayDet_pow_mul, hc, map_nsmul,
      pairing_comm', nsmul_eq_mul]
  have e2 : _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y) =
      c * _root_.GlobalTheory.DetPowPairing.pairing (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) (_root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M) := by
    have hsplit : _root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ Y = _root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ (Y - M) * _root_.ReciprocityTheory.PGsh.cayDet n₀ C ^ M := by
      rw [← pow_add]; congr 1; omega
    nth_rewrite 1 [hsplit]
    rw [pairing_cayDet_pow_mul, hc, map_nsmul, nsmul_eq_mul]
  rw [e1, e2]; ring

end GlobalTheory.DetPowPairing
end

