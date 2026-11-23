module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyLtAdaptedCoordsIndependentFunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  intro Y _ _ q n _ B y U hy z J w u hc hJ F hind φ f a c hφ hf ha hc1 E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

  have hunit : ∀ g : Y.functionFieldˣ, UnitAt y (g : Y.functionField) → E.ord g = 0 := by
    rintro g ⟨b, hb, hbg⟩
    have h1 : (g : Y.functionField) ∈ E.ring := hE _ ⟨b, hbg⟩
    have h2 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈ E.ring := hE _ ⟨↑(hb.unit⁻¹), by
      rw [map_units_inv, IsUnit.unit_spec, hbg]; simp⟩
    have e1 := (E.ord_nonneg_iff g).2 h1
    have e2 := (E.ord_nonneg_iff _).2 h2
    rw [E.ord_inv] at e2
    omega
  have hfφ : E.ord f = E.ord φ := by
    have hg : UnitAt y ((f * φ⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      simpa [div_eq_mul_inv] using hf
    have h0 := hunit _ hg
    have : f = (f * φ⁻¹) * φ := by group
    rw [this, E.ord_mul, h0, zero_add]
  by_cases hyF : y ∈ Y.basicOpen F
  · have hφu : UnitAt y (φ : Y.functionField) := hφ ▸ (unitAt_fnOf_iff hy _ F).2 hyF
    have hfu : UnitAt y (f : Y.functionField) := by
      have := UnitAt.mul hf hφu
      rwa [div_mul_cancel₀ _ φ.ne_zero] at this
    have h0 := hunit f hfu
    have key := (IsSncChart.neg_one_lt_formOrd_sub_sum ℂ Y q n B y U hy z J w u hc E hE a).1 ha
    rw [h0]
    simpa using key
  · have hmax : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rintro (_ | ⟨j, hj⟩)
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hyF ((Scheme.mem_basicOpen Y F y hy).2 h))
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hJ j hj ((Scheme.mem_basicOpen Y (z j) y hy).2 h))
    have hv : ∀ j : Option J, ((j.elim φ fun j => u j : Y.functionFieldˣ) : Y.functionField) =
        algebraMap (Y.presheaf.stalk y) Y.functionField
          (Y.presheaf.germ U y hy (j.elim F fun j => z j)) := by
      rintro (_ | ⟨j, hj⟩)
      · simp only [Option.elim]
        rw [hφ, algebraMap_germ]
      · simp only [Option.elim]
        rw [hc.val j hj, algebraMap_germ]
    have hc' : ∀ j : Option J, (j.elim c fun j => a j) < 1 := by
      rintro (_ | ⟨j, hj⟩)
      · exact hc1
      · exact ha j hj
    have key := GlobalTheory.IndepDiscrep.neg_one_lt_formOrd_sub_sum Y q n hn y U hy (dOn q z) hc.frame
      (Option J) (fun j => Y.presheaf.germ U y hy (j.elim F fun j => z j)) hmax
      (fun j => j.elim φ fun j => u j) (fun j => j.elim c fun j => a j) (hind hmax) hv hc' E hE
    rw [Fintype.sum_option] at key
    simp only [Option.elim] at key
    rw [Finset.sum_coe_sort J (fun j => a j * (E.ord (u j) : ℚ))] at key
    rw [hfφ]
    linarith

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerHomotopyOperatorValuesGenerators
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Gen

variable {R B P : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing P] [Algebra R P]
  (v : Derivation R P P) {α : B →+* P} (h : SemiHom (RingHom.id R) α)

theorem ctr_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : ctr v (h.mDR x) = 0 := by
  induction x using indDR with
  | h b => rw [h.mDR_algebraMap, ctr_algebraMap]
  | hd b => rw [h.mDR_ι, h.m1_D, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, hv, map_zero]
  | hm x y hx hy => rw [map_mul, ctr_mul, hx, hy, zero_mul, mul_zero, add_zero]
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem lie_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : lie v (h.mDR x) = 0 := by
  rw [lie_apply, ctr_mDR_of_kill v h hv, map_zero, zero_add, ← h.mDR_dDR, ctr_mDR_of_kill v h hv]

theorem lie_smul_mDR (hv : ∀ b, v (α b) = 0) (p : P) (x : DR R B) :
    lie v (p • h.mDR x) = v p • h.mDR x := by
  rw [Algebra.smul_def, lie_mul, lie_algebraMap, lie_mDR_of_kill v h hv, mul_zero, add_zero, ← Algebra.smul_def]

theorem lie_pow_smul_mDR (hv : ∀ b, v (α b) = 0) (e : ℕ → P) (he0 : v (e 0) = 0)
    (hs : ∀ n, v (e (n + 1)) = e n) (x : DR R B) (n k : ℕ) :
    (lie v ^ k) (e n • h.mDR x) = (if k ≤ n then e (n - k) else 0) • h.mDR x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hk : k ≤ n
    · rw [if_pos hk, lie_smul_mDR v h hv]
      by_cases hk' : k + 1 ≤ n
      · rw [if_pos hk', show n - k = (n - (k + 1)) + 1 by omega, hs]
      · rw [if_neg hk', show n - k = 0 by omega, he0]
    · rw [if_neg hk, if_neg (by omega), zero_smul, map_zero]

end Gen

theorem alt_sum_choose_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) = 1 := by
  have h0 := Int.alternating_sum_range_choose (n := n + 1)
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, if_neg (Nat.succ_ne_zero n)] at h0
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * -1 * ((n + 1).choose (k + 1) : ℤ) =
      -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

theorem sum_e_mul {B : Type} [CommRing B] (Q : PDPoly B) (N n : ℕ) (hn : n < N) :
    ∑ k ∈ Finset.range N, ((-1) ^ k * Q.e (k + 1)) * (if k ≤ n then Q.e (n - k) else 0) = Q.e (n + 1) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, show (Finset.range N).filter (· ≤ n) = Finset.range (n + 1) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  have key : ∀ k ∈ Finset.range (n + 1), (-1 : Q.P) ^ k * Q.e (k + 1) * Q.e (n - k) =
      (((-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) : ℤ) : Q.P) * Q.e (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_assoc, Q.e_mul, show k + 1 + (n - k) = n + 1 by omega]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, ← Int.cast_sum, alt_sum_choose_succ, Int.cast_one, one_mul]

theorem hot_values : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  intro R B _ _ _ J δ Q _ _ η v h _ hB hs _ N n α
  have he0 : v (Q.e 0) = 0 := by rw [Q.e_zero]; exact v.map_one_eq_zero
  refine ⟨?_, fun hn ↦ ?_⟩
  · unfold hot
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [map_smul, ctr_mDR_of_kill v h hB, smul_zero, map_zero, smul_zero]
  · have hc : ctr v (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e n • h.mDR α := by
      rw [map_smul, ctr_ι_mul, Derivation.liftKaehlerDifferential_comp_D, hs 0, Q.e_zero, one_smul,
        ctr_mDR_of_kill v h hB, mul_zero, sub_zero]
    unfold hot
    simp only [hc, lie_pow_smul_mDR v h hB Q.e he0 hs, smul_smul]
    rw [← Finset.sum_smul, sum_e_mul Q N n hn]

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOrdSub
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.TauFormGen

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem dvd_ord_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G')
  (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ x, algebraMap (FractionRing R) F x = algebraMap (FractionRing V) F (gK x)) →
  ∀ (k : ℕ), IsUnit (k : R) → ∀ (ϖ : V), Irreducible ϖ → ∀ (O : ValuationSubring F) (φ : V →+* O) (σ : F →ₐ[FractionRing V] F) (π : F), IsLocalHom φ →
    (∀ w, (φ w : F) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) → (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    π ^ k = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ) → IsPrimitiveRoot (σ π / π) k →
  ∀ (ρ : D.toPre.X →+ D'.toPre.X) (e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A)),
    (∀ (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) →
    (∀ (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) →
    (∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ) (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a') →
  ∀ (a b : D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre (ρ a) (ρ b) x' →
    (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ _ hVb G' _ _ hG' D' A' U' g gK hgK F _ _ _ _ hF k hk ϖ hϖ O φ σ π hφ eφ hσ
    hπ hζ ρ e hW hGal hT a b x x' hx hx'
  obtain ⟨hR, _⟩ := hRb
  obtain ⟨hV, _⟩ := hVb
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV D' A' G' hG' U' F k hk1
  have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have wt₂ : ∀ (p p' : QkPt D'.toPre F k) (τ : Multiplicative D'.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A'.A A'.L (k : ℤ) (f' p) (f' p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₂ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have c₁ : ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' →
      (f p').left = spMap σ.toRingHom ≫ (f p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f p)
    have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
    rw [← this, hy]
  have c₂ : ∀ (σ : F →ₐ[FractionRing V] F) p p', QkExt σ.toRingHom p p' →
      (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds V (maximalIdeal V) hV D' A' G' hG' U' F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f' p)
    have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
    rw [← this, hy]
  have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
      WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
    GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'
  have tor : ∀ (τ' : Multiplicative D'.toPre.X →* Fˣ) (q' : QkPt D'.toPre F k), τ' ^ k = 1 → q'.y = 0 →
      GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt D.toPre F k,
      WeilIs A.A A.L (k : ℤ) (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y)))) := by
    intro τ' q' h₁ h₂ h₃ p
    obtain ⟨q, h₄, h₅⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ))
      (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)
    have : f q = e (f' q') :=
      hT _ τ' q q' (f q) (f' q') h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hw := wt₁ q p (τ'.comp (AddMonoidHom.toMultiplicative ρ)) h₄ h₅
    rw [this] at hw
    exact hw
  obtain ⟨p, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a
  obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
  obtain ⟨p', hp'⟩ := s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])
  have hp : f p = e (f' p') := by rw [hp', e.apply_symm_apply]
  obtain ⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by
    refine exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_
    obtain ⟨q', h₂, h₃⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁
    have h := hW _ _ _ (wt₂ q' p' τ' h₂ h₃)
    rw [← hp] at h
    exact uniq _ _ _ _ (tor τ' q' h₁ h₂ h₃ p) h

  let σR : F →ₐ[FractionRing R] F := { σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }
  have eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) := fun r => by
    rw [hF, hgK]; exact eφ _
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p
  obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
  obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O (φ.comp g) eφR k σR p r hr
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O (φ.comp g) eφR k hkO σR hσ p)
  obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor V _ hB' F O φ eφ k σ p' r' hr'
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart V _ hB' F O φ eφ k hkO σ hσ p')
  have hq : f q₁ = e (f' q₂) := by
    have h₁ : f r = e (f' r') := Over.OverMorphism.ext (by
      rw [c₁ σR p r hr, hGal (f' p') (f' r') (c₂ σ p' r' hr'), ← hp])
    rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp] at h₁
    exact mul_left_cancel h₁
  have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
    have h := tor τ₂ q₂ k₂ y₂ t₂ pb
    rw [← hq] at h
    exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre p'.y (ρ pb.y)
  obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre z (ρ pb.y)
  obtain ⟨s, s0, sv, sσ⟩ := v₁ _ x hx
  obtain ⟨s', s0', sv', sσ'⟩ := v₂ _ x'' hx''
  have sσ : σ s = _ := sσ
  have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord V F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'')
    (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
    (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_div₀, hF]; rfl)
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main V _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')
  rw [val_div, hu, (ord_vw V).map_mul, (ord_vw V).map_unit, (ord_vw V).map_mul, val_pow, zero_add, nsmul_eq_mul,
    ← sub_sub] at dv
  exact (dvd_sub_left (dvd_mul_right _ _)).1 dv

end GlobalTheory.TauFormGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.E8LatticePullbackGeneric

open GlobalTheory.CechPic

theorem sum_lamPts {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x y : T ⟶ G) (c : Pic G.left) (w : ℤ) :
    ∑ k : Fin 4, (-(w * GlobalTheory.PolDeg.negε k)) • pull (GlobalTheory.PolDeg.lamPts x y k) c = w • lam c x y := by
  simp only [Fin.sum_univ_four, GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, lam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [smul_add, smul_sub, mul_neg, mul_one, neg_neg, neg_smul]
  all_goals first
  | (norm_num; done)
  | (norm_num; abel)
  | (push_cast; abel)
  | (rw [sub_eq_add_neg, sub_eq_add_neg]; congr 1 <;> [congr 1; skip] <;> norm_num)

theorem lam_pull_hom {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] (φ : G' ⟶ G) [IsMonHom φ]
    (c : Pic G.left) (x y : T ⟶ G') : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem pull_fst_lam {S S' : Scheme.{0}} (f : S' ⟶ S) {X G : Over S} [GrpObj G] (c : Pic G.left) (x x' : X ⟶ G) :
    GlobalTheory.CechPic.pull (pullback.fst X.hom f) (lam c x x') =
      lam (GlobalTheory.CechPic.pull (pullback.fst G.hom f) c) ((Over.pullback f).map x) ((Over.pullback f).map x') := by
  have hfst : ∀ z : X ⟶ G, pullback.fst X.hom f ≫ z.left = ((Over.pullback f).map z).left ≫ pullback.fst G.hom f :=
    fun z => by simp [pullback.lift_fst]
  simp only [lam, map_add (f := _), map_sub, ← pull_comp, hfst, Functor.map_mul, Functor.map_one]


open GlobalTheory.E8LatticePullbackGeneric GlobalTheory.CechPic in
theorem exists_polAV_gen : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro hL₁ _ _ V₁ _ _ _ _ D₀ G₀ _ _ A₀ U₀ _ W hW
  have := A₀.isAb.comm

  let c := GlobalTheory.EighthPowerFactor.siegOne hL₁.globalFns A₀.isAb A₀.isLB A₀.g
  have hc1 : RelAmple c.A c.diag := GlobalTheory.EighthPowerFactor.relAmple_diag_lam A₀.isAb A₀.isLB
    (GlobalTheory.Moduli.cube_of_isLB _ A₀ A₀.L A₀.isLB) A₀.ample
  have hb := GlobalTheory.EighthPower.isSymBilin hL₁.globalFns c hc1
  have hpw := GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp A₀.A 8)
  have hu : ∀ (T : Over (Sp (FractionRing V₁))) (y : Fin 8 → (T ⟶ A₀.A)),
      ∃! x : T ⟶ powObj A₀.A 8, ∀ u, x ≫ powPr A₀.A u = y u := fun T y =>
    ⟨(powIsLimit A₀.A 8).lift (Fan.mk T y), fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩,
      fun x hx => (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by rw [(powIsLimit A₀.A 8).fac]; exact hx u⟩
  let Q : PolAV (Sp (FractionRing V₁)) :=
    { A := powObj A₀.A 8, isAb := hpw.2.2.2.1 A₀.isAb, g := 8 * A₀.g, smoothDim := hpw.2.2.1 _ A₀.smoothDim
      L := GlobalTheory.MatrixBundle.matLB c.P (powPr A₀.A) W, isLB := LB.isLB_linComb c.isLB _ _
      rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      ample := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hL₁.globalFns _ _ 8 _ _ _ _ c _ (powPr A₀.A) W
        (fun u => powPr.isMonHom A₀.A u) hu hc1 hW.1
      ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u) hu hW.2
        (fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam A₀.isLB A₀.ktriv x hx) }

  let F := Over.pullback (jK V₁)
  have hP : IsLimit (Fan.mk (F.obj (powObj G₀ 8)) fun u => F.map (powPr G₀ u)) :=
    isLimitFanMkObjOfIsLimit F _ _ (powIsLimit G₀ 8)
  let y : Fin 8 → (F.obj (powObj G₀ 8) ⟶ A₀.A) := fun u => F.map (powPr G₀ u) ≫ U₀.gen.hom
  let gen : F.obj (powObj G₀ 8) ≅ Q.A :=
    { hom := (powIsLimit A₀.A 8).lift (Fan.mk _ y)
      inv := hP.lift (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv)
      hom_inv_id := hP.hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp only [Fan.mk_π_app]
        erw [(powIsLimit A₀.A 8).fac_assoc (Fan.mk _ y) ⟨u⟩]
        simp [y]
      inv_hom_id := (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [(powIsLimit A₀.A 8).fac (Fan.mk _ y) ⟨u⟩]
        simp only [Fan.mk_π_app, y]
        rw [← Category.assoc]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp }
  have hgen : ∀ u, gen.hom ≫ powPr A₀.A u = y u := fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩
  have := U₀.gen_hom
  refine ⟨Q, gen, ?_, ?_⟩
  · refine GlobalTheory.EighthPowerFactor.isMonHom_of_coord (fun u => powPr.isMonHom A₀.A u) hu fun u => ?_
    rw [hgen u]
    infer_instance
  · have hA := A₀.isLB
    have hLG := U₀.LG.isLB
    have hQ : Q.L.IsLB := Q.isLB
    have hE : (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).IsLB := LB.isLB_linComb hLG _ _
    have hext : pull (pullback.fst G₀.hom (jK V₁)) (cls _ hLG) = pull U₀.gen.hom.left (cls _ hA) := by
      obtain ⟨w, hw⟩ := U₀.ext
      have e := (cls_eq_iff (pull_isLB hA _) (pull_isLB hLG _)).2 ⟨w, hw⟩
      rw [cls_pull hA, cls_pull hLG] at e
      exact e.symm
    have key : ∀ x x' : powObj G₀ 8 ⟶ G₀, pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (lam (cls _ hLG) x x') =
        lam (cls _ hA) (F.map x ≫ U₀.gen.hom) (F.map x' ≫ U₀.gen.hom) := by
      intro x x'
      rw [pull_fst_lam, hext, lam_pull_hom]
    have hlam : cls c.P c.isLB = lam (cls _ hA) (fst A₀.A A₀.A) (snd A₀.A A₀.A) := cls_cube_two hA _ _ c.isLB
    have eL : pull gen.hom.left (cls Q.L hQ) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [show cls Q.L hQ = _ from cls_linComb c.isLB
        (fun uv : Fin 8 × Fin 8 => (lift (powPr A₀.A uv.1) (powPr A₀.A uv.2)).left) (fun uv => W uv.1 uv.2) hQ, map_sum]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [map_zsmul, hlam]
      erw [pull_lam, pull_lam]
      rw [lift_fst, lift_snd]
      erw [hgen, hgen]
    have eR : pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (cls _ hE) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls _ hE = _ from cls_linComb hLG (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => GlobalTheory.PolDeg.lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * GlobalTheory.PolDeg.negε k.2)) hE, Fintype.sum_prod_type]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [sum_lamPts, map_sum, map_zsmul, key, y]
    refine (cls_eq_iff (pull_isLB hQ _) (pull_isLB hE _)).1 ?_
    rw [cls_pull hQ, cls_pull hE, eL, eR]

end GlobalTheory.E8LatticePullbackGeneric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR A → ∃ g : Fn2 A, IsAdd (fv f) g := by
  first | exact @GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | exact GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | (intros; apply GlobalTheory.PtExt.exists_isAdd_of_mem_primDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  first | exact @GlobalTheory.TwistCompare.exists_twist_even | exact GlobalTheory.TwistCompare.exists_twist_even | (intros; apply GlobalTheory.TwistCompare.exists_twist_even <;> assumption)
end

