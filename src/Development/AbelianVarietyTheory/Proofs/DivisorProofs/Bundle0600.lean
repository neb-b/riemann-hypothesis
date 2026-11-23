module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitCoeffOfCoboundarySmall
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

def yZero : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O := Sum.elim (fun i => X i) (fun _ => 0)

theorem yZero_const : ∀ s, constantCoeff (yZero (O := O) (d := d) s) = 0 := by
  intro s; cases s <;> simp [yZero]

theorem hasSubst_yZero : HasSubst (yZero (O := O) (d := d)) :=
  hasSubst_of_constantCoeff_zero yZero_const

theorem constantCoeff_subst_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ O}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ O) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ O) :
    constantCoeff (MvPowerSeries.pderiv i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]; simp

theorem subst_X_self {σ : Type} (f : MvPowerSeries σ O) : subst (fun i => (X i : MvPowerSeries σ O)) f = f := by
  rw [← map_algebraMap_eq_subst_X]
  simp [Algebra.algebraMap_self, map_id]

theorem pderiv_right_formalGroupLawCoboundaryOne (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (t : MvPowerSeries (Fin d) O) (j : Fin d) :
    MvPowerSeries.pderiv (Sum.inr j) (cob1 μ t) =
      (∑ s, subst μ (MvPowerSeries.pderiv s t) * MvPowerSeries.pderiv (Sum.inr j) (μ s)) - inR (MvPowerSeries.pderiv j t) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  unfold cob1 inL inR
  rw [map_sub, map_sub, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst μ hμ,
    ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hl, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hr]
  have e1 : ∑ s : Fin d, subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (MvPowerSeries.pderiv s t) *
      MvPowerSeries.pderiv (Sum.inr j) (X (Sum.inl s)) = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [pderiv_X_of_ne (by simp), mul_zero]
  have e2 : ∑ s : Fin d, subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (MvPowerSeries.pderiv s t) *
      MvPowerSeries.pderiv (Sum.inr j) (X (Sum.inr s)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (MvPowerSeries.pderiv j t) := by
    rw [Finset.sum_eq_single j]
    · rw [pderiv_X_self, mul_one]
    · intro s _ hs; rw [pderiv_X_of_ne (by simpa using hs), mul_zero]
    · simp
  rw [e1, e2, sub_zero]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

theorem yZero_subst (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (g : MvPowerSeries (Fin d) O) :
    subst yZero (subst μ g) = g := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ.const) hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (μ s)) = fun i => X i := by
    have h := hμ.unit
    funext i
    have hi := congrFun h i
    simpa [op, at2, yZero] using hi
  rw [this, subst_X_self]

theorem yZero_inR (g : MvPowerSeries (Fin d) O) :
    subst yZero (inR g) = C (constantCoeff g) := by
  have hr : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  unfold inR
  rw [subst_comp_subst_apply hr hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O)) = 0 := by
    funext s; rw [subst_X hasSubst_yZero]; rfl
  rw [this, subst_zero_eq_C_constantCoeff]
  simp [Algebra.algebraMap_self, map_id]

theorem linear_coeff_law (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (s j : Fin d) :
    constantCoeff (MvPowerSeries.pderiv (Sum.inr j) (μ s)) = if s = j then 1 else 0 := by
  classical

  have hx : constantCoeff (MvPowerSeries.pderiv (Sum.inl j) (μ s)) = if s = j then 1 else 0 := by
    have h := congrFun hμ.unit s
    change subst yZero (μ s) = X s at h
    have h2 := congrArg (fun f => constantCoeff (MvPowerSeries.pderiv j f)) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ yZero_const, map_sum] at h2
    simp only [map_mul, constantCoeff_subst_of yZero_const] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Fintype.sum_sum_type, yZero,
      Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero, Finset.sum_const_zero, add_zero, pderiv_X, map_sum, map_mul] at h2
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    split_ifs at h2 ⊢ <;> exact h2
  have hsw : ∀ k : Fin d ⊕ Fin d, constantCoeff ((Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O))
      (fun i => X (Sum.inl i))) k) = 0 := by
    intro k; cases k <;> simp
  have h := hμ.comm s
  unfold swap at2 at h
  have h2 := congrArg (fun f => constantCoeff (MvPowerSeries.pderiv (Sum.inr j) f)) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hsw, map_sum] at h2
  simp only [map_mul, constantCoeff_subst_of hsw] at h2
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, pderiv_X, Pi.single_apply, Sum.inr.injEq,
    reduceCtorEq, if_false, map_zero, mul_zero, Finset.sum_const_zero, add_zero, apply_ite, map_one, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [← h2, hx]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

theorem isLocalRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add (f := _)]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

end GlobalTheory.Katz.SmallDeriv


open GlobalTheory.Katz.SmallDeriv in
theorem GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  intro p hpr C _ _ _ v O _ _ hpO _ _ hv d μ hμ t hlin hcob α ⟨i, hi⟩
  classical
  haveI : IsLocalRing O := isLocalRing_of_integers v O hv
  let π := IsLocalRing.residue O
  have hmem : ∀ a : O, π a = 0 ↔ ¬IsUnit a := by
    intro a
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast π, hmem]; exact hpO.out

  have hG : ∀ j, map π (MvPowerSeries.pderiv (Sum.inr j) (cob1 μ t)) = 0 := by
    intro j; ext n
    rw [coeff_map, coeff_pderiv, map_mul, coeff_zero]
    by_cases hn : p ∣ n (Sum.inr j) + 1
    · obtain ⟨m, hm⟩ := hn
      have e : π ((n (Sum.inr j) : O) + 1) = 0 := by
        have : ((n (Sum.inr j) : O) + 1) = ((n (Sum.inr j) + 1 : ℕ) : O) := by push_cast; ring
        rw [this, hm, Nat.cast_mul, map_mul, map_natCast, hp0, zero_mul]
      rw [e, mul_zero]
    · have := hcob (n + Finsupp.single (Sum.inr j) 1) ⟨Sum.inr j, by simpa using hn⟩
      rw [(hmem _).2 this, zero_mul]
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) (IsLocalRing.ResidueField O)) :=
    Matrix.of fun s j => map π (subst yZero (MvPowerSeries.pderiv (Sum.inr j) (μ s)))
  let w : Fin d → MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) := fun s => map π (MvPowerSeries.pderiv s t)
  have hvec : Matrix.vecMul w N = 0 := by
    funext j
    have e := congrArg (fun F => map π (subst yZero F)) (pderiv_right_formalGroupLawCoboundaryOne μ hμ.const t j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_subst hasSubst_yZero, hG j, ← coe_substAlgHom (hasSubst_yZero.map π), map_zero,
      ← coe_substAlgHom hasSubst_yZero, map_sub, map_sum] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, coe_substAlgHom, yZero_subst μ hμ, yZero_inR, constantCoeff_pderiv, map_sub, map_sum,
      map_C] at e
    have hl : π (coeff (Finsupp.single j 1) t) = 0 := (hmem _).2 (hlin j)
    rw [hl, map_zero, sub_zero] at e
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, N, w, Matrix.of_apply]
    exact e.symm
  have hN0 : (constantCoeff : MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) →+* _).mapMatrix N = 1 := by
    ext s j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply, constantCoeff_map,
      constantCoeff_subst_of yZero_const, linear_coeff_law μ hμ, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit N.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, hN0, Matrix.det_one]
    exact isUnit_one
  have hw : w i = 0 := by
    have h1 := congrArg (fun u => Matrix.vecMul u N.adjugate) hvec
    simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.zero_vecMul] at h1
    have h2 := congrFun h1 i
    simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at h2
    exact (hdet.mul_right_eq_zero).1 (by rw [mul_comm]; exact h2)
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (fun h => hi (h ▸ dvd_zero p))
  have hsub : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hαi)
  have hc := congrArg (coeff (α - Finsupp.single i 1)) hw
  simp only [w] at hc
  rw [coeff_map, coeff_pderiv, coeff_zero, hsub, map_mul] at hc
  have hcast : (((α - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : O) + 1 = ((α i : ℕ) : O) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hαi]
  rw [hcast, map_natCast] at hc
  have hne : ((α i : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    obtain ⟨u, u', h⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpr.out).2 hi)
    have h' := congrArg (Int.cast : ℤ → IsLocalRing.ResidueField O) h
    push_cast at h'
    rw [hp0] at h'
    intro h0; rw [h0] at h'; simp at h'
  exact (hmem _).1 ((mul_eq_zero.1 hc).resolve_right hne)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionClassNatural
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_spMap_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap σ)) : IsClosedImmersion φ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip this

theorem restrict_pull1_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO1 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull1 ((preRes χ q').pull1 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 y := by
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ y
  rfl

theorem restrict_pull2_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO2 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull2 ((preRes χ q').pull2 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 y := by
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ y
  rfl


set_option maxHeartbeats 1000000 in
theorem bock_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀ hc hc₀
    hS hs hq x z z' hB hB'
  obtain ⟨f, v, hfv, hf, hv⟩ := hB
  obtain ⟨f₂, v₂, hfv₂, hf₂, hv₂⟩ := hB'
  haveI : IsClosedImmersion φ := isClosedImmersion_of_isPullback_spMap_surj hS.1 h
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 h₀
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_spMap_surj hS.1 k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 k₀
  have hsec := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ hS hq
  obtain ⟨c₁, hc₁, hC₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R' σ X X' Y Y' s s' q q' φ χ h.w ψ ψ' w w' hc inferInstance).1 f x hf
  obtain ⟨c₂, hc₂, hC₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R' Y Y' q q' σ χ k.w).1 f₂ (pullHO1 w' x)).1 hf₂
  obtain ⟨e₁, he₁, hE₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hc₀ inferInstance).2 v z hv
  obtain ⟨e₂, he₂, hE₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ Y Y₀ q q₀ σ₀ χ₀ k₀.w).2.1 v₂ z').1 hv₂
  have nat : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ q q' V (mp (OAff q) a b) = mp (OPre χ q') a (preα χ q q' U b) :=
    fun a b ↦ (preCoef k.w).naturality a b
  have nat₀ : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ₀ q q₀ V (mp (OAff q) a b) = mp (OPre χ₀ q₀) a (preα χ₀ q q₀ U b) :=
    fun a b ↦ (preCoef k₀.w).naturality a b

  obtain ⟨g', hg'⟩ := (H1.mk_eq_mk (f := c₁)
    (f' := (CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂)).1 (by
      rw [hC₁, ← CoefMap.pullCohomologyOne_class, hC₂, restrict_pull1_preRes_pairFst])
  choose g hg using fun p : (Pair ψ)ᵒᵖ ↦ (hsec ((pairFst ψ).obj p)).1 (g' p)
  obtain ⟨F1, hF1⟩ : ∃ F1 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F1 a b u = (pairPull w).α b (f _ _ ((pairPull w).G.map u)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F2 a b u = f₂ _ _ ((pairFst ψ).map u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hred : ∀ a b (u : a ⟶ b),
      preα χ q q' ((pairFst ψ).obj b) ((F1 - F2 - d0 (OPair ψ q) g) a b u) = 0 := by
    intro a b u
    have hc₂' : ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u =
        preα χ q q' ((pairFst ψ).obj b) (f₂ _ _ ((pairFst ψ).map u)) := hc₂ _ _ _
    have e : g' b - mp (pairFst ψ ⋙ OPre χ q') u (g' a) =
        c₁.1 a b u - ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u :=
      congrFun (congrFun (congrFun hg' a) b) u
    have e' : preα χ q q' ((pairFst ψ).obj b) (mp (OPair ψ q) u (g a)) =
        mp (pairFst ψ ⋙ OPre χ q') u (g' a) := by
      have := nat ((pairFst ψ).map u) (g a)
      rw [hg a] at this
      exact this
    simp only [Pi.sub_apply, amitsur_d0_apply, map_sub]
    rw [hF1, hF2, ← hc₁, ← hc₂', hg b, e', e, sub_self]
  choose u₀ hu₀ using fun a b (u : a ⟶ b) ↦ ((hsec ((pairFst ψ).obj b)).2.1 _).1 (hred a b u)
  have hD : F1 - F2 - d0 (OPair ψ q) g = t • (u₀ : C1 (OPair ψ q)) := by
    funext a b u; exact hu₀ a b u
  obtain ⟨W1, hW1⟩ : ∃ W1 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W1 a b c u u' = (pairPull w).α c (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')) :=
    ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W2 a b c u u' = v₂ _ _ _ ((pairFst ψ).map u) ((pairFst ψ).map u') := ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  have hdF1 : d1 (OPair ψ q) F1 = t • W1 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv _) _) _)
      ((pairPull w).G.map u)) ((pairPull w).G.map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF1, hF1, hF1, hW1, ← (pairPull w).naturality, Functor.map_comp, ← map_sub, ← map_add (f := _), e,
      (pairPull w).smul]
    rfl
  have hdF2 : d1 (OPair ψ q) F2 = t • W2 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv₂ _) _) _)
      ((pairFst ψ).map u)) ((pairFst ψ).map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF2, hF2, hF2, hW2, Functor.map_comp]
    exact e
  have hdd : d1 (OPair ψ q) (d0 (OPair ψ q) g) = 0 := by
    have := commAlgFunctorCoboundaryZero_mem_cocyclesOne (OPair ψ q) g
    rw [commAlgFunctorCocyclesOne_eq_ker] at this
    exact this
  have hmain : t • (W1 - W2 - d1 (OPair ψ q) u₀) = 0 := by
    rw [smul_sub, smul_sub, ← hdF1, ← hdF2, ← (d1 (OPair ψ q)).map_smul, ← hD, map_sub, map_sub, hdd,
      sub_zero, sub_self]
  have hzero : ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      preα χ₀ q q₀ ((pairFst ψ).obj c) ((W1 - W2 - d1 (OPair ψ q) u₀) a b c u u') = 0 := by
    intro a b c u u'
    refine ((hsec ((pairFst ψ).obj c)).2.2.2 _).2 ?_
    exact congrFun (congrFun (congrFun (congrFun (congrFun hmain a) b) c) u) u'
  obtain ⟨ub, hub⟩ : ∃ ub : C1 (pairFst ψ ⋙ OPre χ₀ q₀), ∀ a b (u : a ⟶ b),
      ub a b u = preα χ₀ q q₀ ((pairFst ψ).obj b) (u₀ a b u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hH2 : H2.mk _ e₁ = H2.mk _ ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂) := by
    refine H2.mk_eq_mk.2 ⟨ub, ?_⟩
    funext a b c u u'
    have E := hzero a b c u u'
    simp only [Pi.sub_apply, d1_apply, map_sub, map_add (f := _)] at E
    have E1 : preα χ₀ q q₀ ((pairFst ψ).obj c) (mp (OPair ψ q) u' (u₀ a b u)) =
        mp (pairFst ψ ⋙ OPre χ₀ q₀) u' (ub a b u) := by
      rw [hub]; exact nat₀ ((pairFst ψ).map u') (u₀ a b u)
    have E2 : e₁.1 a b c u u' = preα χ₀ q q₀ _ (W1 a b c u u') := by rw [he₁, hW1]
    have E3 : ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂).1 a b c u u' =
        preα χ₀ q q₀ _ (W2 a b c u u') := by
      rw [hW2]; exact he₂ _ _ _ _ _
    simp only [d1_apply, Pi.sub_apply]
    rw [E2, E3, ← E1, hub, hub]
    linear_combination -E
  rw [hE₁, ← CoefMap.pullCohomologyTwo_class, hE₂, restrict_pull2_preRes_pairFst] at hH2
  exact ((GlobalTheory.AbCoh.pair_pre_bijective R₀ X Y Y₀ ψ χ₀ q₀).2.1.1 hH2).symm

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivSubstChainRule
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.PSChain


open scoped MvPowerSeries.WithPiTopology in
theorem continuous_pderiv_discrete {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv (R := R) i f) := by
  classical
  apply continuous_pi
  intro n
  have e : (fun f : MvPowerSeries σ R => (pderiv (R := R) i f) n) =
      (fun r : R => r * (n i + 1)) ∘ (fun f : MvPowerSeries σ R => coeff (n + Finsupp.single i 1) f) := by
    funext f
    exact coeff_pderiv f n
  rw [e]
  exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)


open scoped MvPowerSeries.WithPiTopology in
theorem pderiv_subst_chain {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ]
    (a : σ → MvPowerSeries τ R) (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (k : τ) :
    pderiv (R := R) k (subst a f) = ∑ j, subst a (pderiv (R := R) j f) * pderiv (R := R) k (a j) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hcs : Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ R) := continuous_subst ha
  have hs0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D1 : MvPowerSeries σ R → MvPowerSeries τ R := fun g => pderiv (R := R) k (subst a g)
  let D2 : MvPowerSeries σ R → MvPowerSeries τ R := fun g =>
    ∑ s, subst a (pderiv (R := R) s g) * pderiv (R := R) k (a s)
  have c1 : Continuous D1 := (continuous_pderiv_discrete _).comp hcs
  have c2 : Continuous D2 :=
    continuous_finsetSum _ fun i _ => (hcs.comp (continuous_pderiv_discrete _)).mul continuous_const
  have hpoly : ∀ p : MvPolynomial σ R, D1 (p : MvPowerSeries σ R) = D2 (p : MvPowerSeries σ R) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D1, D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D1, D2, MvPolynomial.coe_add, subst_add ha, map_add (f := _)] at hp hq ⊢
      rw [hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    | mul_X p s2 hp =>
      simp only [D1, D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
      have hX : ∀ i : σ, pderiv (R := R) i (X s2 : MvPowerSeries σ R) = if i = s2 then 1 else 0 := by
        intro i
        by_cases h : i = s2
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne (Ne.symm h)]
      have hterm : ∀ i : σ, subst a (pderiv (R := R) i ((p : MvPowerSeries σ R) * X s2)) * pderiv (R := R) k (a i) =
          (if i = s2 then subst a (p : MvPowerSeries σ R) * pderiv (R := R) k (a i) else 0) +
            a s2 * (subst a (pderiv (R := R) i (p : MvPowerSeries σ R)) * pderiv (R := R) k (a i)) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer c1 c2 (funext hpoly)
  exact congrFun this f

end GlobalTheory.PSChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferential
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

private theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem sec_res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

private theorem sec_map_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ x y

theorem red_chern_deg_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  intro Q q _ hqQ U u hQ a b ha hb
  refine (_root_.GlobalTheory.EtC.sec_ext_glue _ _ U).1 _ _ ?_
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u) ?_
  rintro V g ⟨v, hv⟩
  have hw : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  rw [sec_res_sub, (redMap Q q 1).nat, ha V g v hv, hb V g _ hw, ← (redMap Q q 1).comm, sec_res_map,
    GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ V g v hv, defect, sec_map_sub]

end GlobalTheory.EtC.RedChern
end

