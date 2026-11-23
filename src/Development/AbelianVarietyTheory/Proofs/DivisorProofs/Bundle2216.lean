module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmul
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} {δ : DividedPowers J}

theorem divPowerCompatFunctionDifferential_smul (r : R) (b : B) : kd0 R δ (r • b) = r • kd0 R δ b := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul (r : R) (x : K1 R δ) : kd1 R δ (r • x) = r • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_smul (r : R) (x : K R δ 2) : kd2 R δ (r • x) = r • kd2 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatTwoFormDerivative_mk, divPowerCompatTwoFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

variable {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul (r : R) (x : K1 R δ) : km1 h hd (r • x) = σ r • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

theorem km_smul (j : ℕ) (r : R) (x : K R δ j) : km h hd j (r • x) = σ r • km h hd j x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, km_mk, km_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

end Ring

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem crystallineCompatibleFormsComplex_functionMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).M0.map φ (r • x) = r • (KK κ t).M0.map φ x := map_smul (mp (O κ t) φ) r x

theorem crystallineCompatibleFormsComplex_oneFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).M1.map φ (r • x) = r • (KK κ t).M1.map φ x := divPowerCompatOneFormMap_smul (SemiHom.of_algHom φ.φ) φ.dp r x

theorem crystallineCompatibleFormsComplex_twoFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).M2.map φ (r • x) = r • (KK κ t).M2.map φ x := km_smul (SemiHom.of_algHom φ.φ) φ.dp 2 r x

theorem crystallineCompatibleFormsComplex_functionDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).d0 T (r • x) = r • (KK κ t).d0 T x := divPowerCompatFunctionDifferential_smul r x

theorem crystallineCompatibleFormsComplex_oneFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).d1 T (r • x) = r • (KK κ t).d1 T x := divPowerCompatOneFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_twoFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).d2 T (r • x) = r • (KK κ t).d2 T x := divPowerCompatTwoFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_totalDifferentialOne_smul (r : R) (c : (KK κ t).T1) : (KK κ t).D1 (r • c) = r • (KK κ t).D1 c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    show (KK κ t).M0.map ψ (r • c.1 T T' φ) - r • c.1 T T'' (φ ≫ ψ) + r • c.1 T' T'' ψ =
      r • ((KK κ t).M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ)
    rw [crystallineCompatibleFormsComplex_functionMap_smul, smul_add, smul_sub]
  · funext T T' φ
    show r • c.2 T' - (KK κ t).M1.map φ (r • c.2 T) - (KK κ t).d0 T' (r • c.1 T T' φ) =
      r • (c.2 T' - (KK κ t).M1.map φ (c.2 T) - (KK κ t).d0 T' (c.1 T T' φ))
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, smul_sub, smul_sub]
  · funext T
    exact crystallineCompatibleFormsComplex_oneFormDifferential_smul T r (c.2 T)

theorem crystallineCompatibleFormsComplex_cocyclesOne_smul_mem (r : R) {c : (KK κ t).T1} (hc : c ∈ (KK κ t).Z1) : r • c ∈ (KK κ t).Z1 := by
  have h0 : (KK κ t).D1 c = 0 := hc
  show (KK κ t).D1 (r • c) = 0
  rw [crystallineCompatibleFormsComplex_totalDifferentialOne_smul, h0, smul_zero]

theorem crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem (r : R) {c : (KK κ t).T2} (hc : c ∈ (KK κ t).Z2) : r • c ∈ (KK κ t).Z2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · show (KK κ t).M0.map χ (r • c.1 T T' T'' φ ψ) + r • c.1 T T'' T''' (φ ≫ ψ) χ =
      r • c.1 T T' T''' φ (ψ ≫ χ) + r • c.1 T' T'' T''' ψ χ
    rw [crystallineCompatibleFormsComplex_functionMap_smul, ← smul_add, ← smul_add, h1]
  · show r • c.2.1 T T'' (φ ≫ ψ) = (KK κ t).M1.map ψ (r • c.2.1 T T' φ) + r • c.2.1 T' T'' ψ +
      (KK κ t).d0 T'' (r • c.1 T T' T'' φ ψ)
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, ← smul_add, ← smul_add, h2]
  · show r • c.2.2 T' = (KK κ t).M2.map φ (r • c.2.2 T) + (KK κ t).d1 T' (r • c.2.1 T T' φ)
    rw [crystallineCompatibleFormsComplex_twoFormMap_smul, crystallineCompatibleFormsComplex_oneFormDifferential_smul, ← smul_add, h3]
  · show (KK κ t).d2 T (r • c.2.2 T) = 0
    rw [crystallineCompatibleFormsComplex_twoFormDifferential_smul, h4, smul_zero]

end Site

theorem rel_add_smul : ∀ (D : Data) (Λ : Lift D),
    (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧
    (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧
    (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧
    ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  intro D Λ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add (f := _), hf, hf'], by rw [map_add (f := _), hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V c ↦ (congrArg₂ (· + ·) (hr.1 U V c) (hr'.1 U V c)).trans (map_add (Λ.e V) _ _).symm,
        fun U ↦ (congrArg₂ (· + ·) (hr.2 U) (hr'.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (w.1.2 U + w'.1.2 U))
      rw [map_add (f := _), Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesOne_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V c ↦ (congrArg (r • ·) (hr.1 U V c)).trans (map_smul (Λ.e V) r _).symm,
        fun U ↦ (congrArg (r • ·) (hr.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (r • w.1.2 U))
      rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add (f := _), hf, hf'], by rw [map_add (f := _), hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V W c d ↦ (congrArg₂ (· + ·) (hr.1 U V W c d) (hr'.1 U V W c d)).trans (map_add (Λ.e W) _ _).symm,
        fun U V c ↦ (congrArg₂ (· + ·) (hr.2.1 U V c) (hr'.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg₂ (· + ·) (hr.2.2 U) (hr'.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (w.1.2.1 U V c + w'.1.2.1 U V c))
        rw [map_add (f := _), Submodule.Quotient.mk_add]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (w.1.2.2 U + w'.1.2.2 U))
        rw [map_add (f := _), Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V W c d ↦ (congrArg (r • ·) (hr.1 U V W c d)).trans (map_smul (Λ.e W) r _).symm,
        fun U V c ↦ (congrArg (r • ·) (hr.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg (r • ·) (hr.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (r • w.1.2.1 U V c))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (r • w.1.2.2 U))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (E : DivOver q), E.Through y → ∀ a : Fin n → ℚ, ((∀ j ∈ J, a j < 1) → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) ∧ ((∀ j ∈ J, a j ≤ 1) → -1 ≤ ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc E hE a
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen k _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  have h0 : formOf U (gen_mem hy) (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hc.frame).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).2 (by rw [hc.val j hj]; exact hE _ (regAt_fnOf hy _ (z j)))
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy hE z h0 (J := {j // j ∈ J})
    Subtype.val Subtype.val_injective (fun j => u j.1) fun j => hc.val j.1 j.2
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hA
  have hF := DivOver.formOrd_formOf_nonneg hn hy hE (dOn q z) h0
  set F := E.formOrd (formOf U (gen_mem hy) (dOn q z))
  have hAq : ∑ j ∈ J, (E.ord (u j) : ℚ) - 1 ≤ F := by exact_mod_cast hA
  have hFq : (0 : ℚ) ≤ F := by exact_mod_cast hF
  have hnq : ∀ j ∈ J, (0 : ℚ) ≤ E.ord (u j) := fun j hj => by exact_mod_cast hnn j hj
  have hle : (∀ j ∈ J, a j ≤ 1) → ∀ j ∈ J, a j * (E.ord (u j) : ℚ) ≤ E.ord (u j) :=
    fun ha j hj => by nlinarith [ha j hj, hnq j hj]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · change -1 < (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    by_cases hz : ∀ j ∈ J, (E.ord (u j) : ℚ) = 0
    · rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]]
      linarith
    · push Not at hz
      obtain ⟨j, hj, hj0⟩ := hz
      have hpos : (0 : ℚ) < E.ord (u j) := lt_of_le_of_ne (hnq j hj) hj0.symm
      have := Finset.sum_lt_sum (hle fun j hj => (ha j hj).le)
        ⟨j, hj, by nlinarith [ha j hj]⟩
      linarith
  · change -1 ≤ (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    have := Finset.sum_le_sum (hle ha)
    linarith

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqTo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
open GlobalTheory.AbTan GlobalTheory.AbTan.Transl GlobalTheory.TanForms GlobalTheory.InvForm

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvSpan

variable {R : Type} [CommRing R]

theorem dVal_smul {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] DualNumber D) (b : B) (m : Ω[B⁄R]) : dVal φ (b • m) = redHom φ b * dVal φ m := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact (map_smul (Derivation.liftKaehlerDifferential _) b m).trans (Algebra.smul_def _ _)

variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W]

def tr (A : Over (Sp R)) [GrpObj A] : TrTy A := fun B M ↦ tau A B M

theorem tr_bij : TrBij A (tr A) := fun _ _ _ _ _ _ _ _ P hP ↦ bijOn_tau A P hP

theorem tr_nat : TrNat A (tr A) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ α f β hβ P hP z hz ↦
  tau_natural A α f β hβ P hP z hz

theorem exists_tangent (T : TanRep A W) (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    ∃ z : Sp (DualNumber D) ⟶ A.left, Lifts A.hom (unitPt A D) z ∧
      tau A D D (spMap (redHom φ) ≫ affPt A.hom U) z =
        spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U ∧
      ∀ w, T.Φ z w = dVal φ (eU T (tr A) U w) := by
  letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]
  haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨hz0, hτz0⟩ := back_spec (τ := tr A) U tr_bij (pt A U (KaehlerDifferential.D R (Sec A.hom U.1)))
    (pt_lifts A U _)
  let α : Sec A.hom U.1 →ₐ[R] D := { redHom φ with commutes' := redHom_algebraMap φ }
  have hf : ∀ (b : Sec A.hom U.1) (m : Ω[Sec A.hom U.1⁄R]), (dVal φ).toAddMonoidHom (b • m) =
      redHom φ b • (dVal φ).toAddMonoidHom m := fun b m ↦ dVal_smul φ b m
  let β := sumHom (redHom φ) (dVal φ).toAddMonoidHom hf
  have hβ : IsSum β α (dVal φ) := sumHom_isSum _ (dVal φ).toAddMonoidHom hf
  obtain ⟨hl, hnat⟩ := tau_natural A α (dVal φ) β hβ (affPt A.hom U) (affPt_w A.hom U) _ hz0
  have hpt : spMap β ≫ pt A U (KaehlerDifferential.D R (Sec A.hom U.1)) =
      spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U := by
    rw [pt, ← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply, show TanForms.derHom (KaehlerDifferential.D R (Sec A.hom U.1)) b =
      TrivSqZeroExt.inl b + TrivSqZeroExt.inr (KaehlerDifferential.D R (Sec A.hom U.1) b) from rfl, map_add,
      hβ.1, hβ.2, dVal_D]
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq (φ b)
  refine ⟨_, hl, ?_, fun w ↦ ?_⟩
  · refine hnat.trans ?_
    rw [← hpt]
    exact congrArg _ hτz0
  · rw [T.nat α (dVal φ) β hβ _ hz0]
    rfl

def form (T : TanRep A W) (w : W) : GlobForm A.hom :=
  ⟨fun V ↦ eU T (tr A) V.unop w, fun _ _ a ↦ eU_nat T tr_bij tr_nat a w⟩

theorem red_w (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    (spMap (redHom φ) ≫ affPt A.hom U) ≫ A.hom = spMap (algebraMap R D) := by
  rw [Category.assoc, affPt_w, sp_comp]
  exact congrArg spMap (RingHom.ext (redHom_algebraMap φ))

theorem isInv_form [IsCommMonObj A] (T : TanRep A W) (w : W) : IsInv A (form T w) := by
  intro D _ _ U V φ ψ p q q₀ hp hq hpq
  obtain ⟨z, hz, hτ, hΦ⟩ := exists_tangent T U φ
  obtain ⟨z', hz', hτ', hΦ'⟩ := exists_tangent T V ψ
  change dVal φ (eU T (tr A) U w) = dVal ψ (eU T (tr A) V w)
  rw [← hΦ, ← hΦ']
  suffices h : z = z' by rw [h]
  rw [tau_eq A _ (red_w U φ) z hz.1, ← hp] at hτ
  rw [tau_eq A _ (red_w V ψ) z' hz'.1, ← hpq] at hτ'
  let c : ovT R D D ⟶ ovT R D D :=
    Over.homMk (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (TrivSqZeroExt.fstHom D D D).toRingHom) (by
      rw [Category.assoc, fst_w]
      exact sp_comp _ _)
  let p' : ovT R D D ⟶ A := p
  let q' : ovT R D D ⟶ A := q
  have e1 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom φ) ≫ affPt A.hom U) (inl_w A _ (red_w U φ)) =
      c ≫ p' := by
    ext
    change spMap _ ≫ spMap (redHom φ) ≫ affPt A.hom U = (spMap _ ≫ spMap _) ≫ p.left
    rw [hp, Category.assoc, ← Category.assoc (spMap _) (spMap (φ : Sec A.hom U.1 →+* DualNumber D)), sp_comp]
    rfl
  have e2 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom ψ) ≫ affPt A.hom V) (inl_w A _ (red_w V ψ)) =
      c ≫ (p' * q') := by
    ext
    change spMap _ ≫ spMap (redHom ψ) ≫ affPt A.hom V = (spMap _ ≫ spMap _) ≫ (p * q).left
    rw [hpq, Category.assoc, ← Category.assoc (spMap _) (spMap (ψ : Sec A.hom V.1 →+* DualNumber D)), sp_comp]
    rfl
  have e3 : c ≫ q' = q' := by
    ext
    change (_ ≫ _) ≫ q.left = q.left
    rw [hq, Category.assoc]
    change _ ≫ _ ≫ spMap (TrivSqZeroExt.inlHom D D) ≫ q₀ = _
    rw [← Category.assoc (spMap _) (spMap _) q₀, fst_inl, Category.id_comp]
  rw [e1] at hτ
  rw [e2, MonObj.comp_mul, e3] at hτ'
  have k1 : (c ≫ p') * Over.homMk (U := ovT R D D) (V := A) z hz.1 = p' := Over.OverMorphism.ext hτ
  have k2 : (c ≫ p') * q' * Over.homMk (U := ovT R D D) (V := A) z' hz'.1 = p' * q' :=
    Over.OverMorphism.ext hτ'
  have k3 : Over.homMk (U := ovT R D D) (V := A) z hz.1 = Over.homMk (U := ovT R D D) (V := A) z' hz'.1 := by
    rw [mul_right_comm] at k2
    exact mul_left_cancel (k1.trans (mul_right_cancel k2).symm)
  exact congrArg CommaMorphism.left k3

theorem span_eq_top_of_tanRep [IsCommMonObj A] (T : TanRep A W) (U : AffOp A.left) :
    Submodule.span (Sec A.hom U.unop.1) (Set.range fun w : InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using (eU_isBaseChange T tr_bij tr_nat U.unop).inductionOn with
  | tmul w => exact Submodule.subset_span ⟨⟨form T w, isInv_form T w⟩, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)
  | add a b ha hb => exact add_mem (ha trivial) (hb trivial)

theorem span_invForm_eq_top : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left,
    Submodule.span (Sec A.hom U.unop.1)
      (Set.range fun w : GlobalTheory.InvForm.InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  intro R _ A _ g hA _ U
  have := hA.comm
  obtain ⟨W, _, _, -, -, ⟨T⟩⟩ := _root_.GlobalTheory.TanRepr.exists_tanRep R A hA.smooth
  exact span_eq_top_of_tanRep T U

end GlobalTheory.InvSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanPairIsPrimeHeightTwoOfCotangentIndependent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PointSep

open IsLocalRing

theorem span_pair_isPrime_and_height_eq_two : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (a b : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R), LinearIndependent (IsLocalRing.ResidueField R) (![(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, (IsLocalRing.maximalIdeal R).toCotangent ⟨b, hb⟩] : Fin 2 → IsLocalRing.CotangentSpace R) → (Ideal.span {a, b}).IsPrime ∧ (Ideal.span {a, b}).height = 2 := by
  intro R _ _ a b ha hb h
  classical
  have hdom : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := LinearIndependent.pair_iff.mp h
  have hsmul : ∀ (r : R) (x : maximalIdeal R),
      (maximalIdeal R).toCotangent (r • x) = (residue R r) • (maximalIdeal R).toCotangent x := by
    intro r x
    rw [map_smul]; rfl

  have ha2 : a ∉ maximalIdeal R ^ 2 := by
    intro h2
    have h0 : (maximalIdeal R).toCotangent ⟨a, ha⟩ = 0 := by
      rw [Ideal.toCotangent_eq_zero]; exact h2
    have := hp 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hpa : Prime a := ReciprocityTheory.AnForm.R.prime_of_not_mem_sq ha ha2
  have ha0 : a ≠ 0 := hpa.ne_zero

  have hba : b ∉ Ideal.span {a} := by
    intro hb'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb'
    have heq : (⟨b, hb⟩ : maximalIdeal R) = r • ⟨a, ha⟩ := by
      ext; simp [hr]
    have := hp (-(residue R r)) 1 (by rw [heq, hsmul]; simp)
    exact one_ne_zero this.2

  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hle := h.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  set n := Module.finrank (ResidueField R) (CotangentSpace R) with hn
  have hdim : ringKrullDim R = (((n - 2) + 2 : ℕ) : WithBot ℕ∞) := by
    rw [← hfin, Nat.sub_add_cancel hle]
  have hind : ∀ c : Fin 2 → R, ∑ i, c i * (![a, b] : Fin 2 → R) i ∈ maximalIdeal R ^ 2 →
      ∀ i, c i ∈ maximalIdeal R := by
    intro c hc
    have hc' : (maximalIdeal R).toCotangent (c 0 • ⟨a, ha⟩ + c 1 • ⟨b, hb⟩) = 0 := by
      rw [Ideal.toCotangent_eq_zero]
      simpa [Fin.sum_univ_two] using hc
    rw [map_add (f := _), hsmul, hsmul] at hc'
    obtain ⟨h0, h1⟩ := hp _ _ hc'
    intro i
    fin_cases i
    · exact (residue_eq_zero_iff _).mp h0
    · exact (residue_eq_zero_iff _).mp h1
  have hmem : ∀ i, (![a, b] : Fin 2 → R) i ∈ maximalIdeal R := by
    intro i; fin_cases i
    · exact ha
    · exact hb
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quotient_span_range R (n - 2) 2 ![a, b] hdim hmem hind
  have hrange : Set.range (![a, b] : Fin 2 → R) = {a, b} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hrange] at hreg
  have hqdom : IsDomain (R ⧸ Ideal.span {a, b}) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hP : (Ideal.span {a, b}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hqdom
  refine ⟨hP, le_antisymm ?_ ?_⟩
  · have hmin : Ideal.span {a, b} ∈ (Ideal.span ((({a, b} : Finset R)) : Set R)).minimalPrimes := by
      rw [Finset.coe_insert, Finset.coe_singleton, Ideal.minimalPrimes_eq_subsingleton_self]
      rfl
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_le_two
  · have hPa : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha0).mpr hpa
    have h1 : (⊥ : Ideal R) < Ideal.span {a} := by
      rw [bot_lt_iff_ne_bot]; simpa using ha0
    have h2 : Ideal.span {a} < Ideal.span {a, b} := by
      refine lt_of_le_of_ne (Ideal.span_mono (by simp)) ?_
      intro he
      exact hba (he ▸ Ideal.subset_span (by simp))
    have hlt1 := Ideal.height_strict_mono_of_isPrime h1
    have hlt2 := Ideal.height_strict_mono_of_isPrime h2
    have hne : (Ideal.span {a}).height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
    have e1 : (⊥ : Ideal R).height + 1 ≤ (Ideal.span {a}).height := Order.add_one_le_of_lt hlt1
    have e2 : (Ideal.span {a}).height + 1 ≤ (Ideal.span {a, b}).height := Order.add_one_le_of_lt hlt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal R).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Ideal.span {a}).height + 1 := by gcongr
      _ ≤ _ := e2

end GlobalTheory.PointSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fraction_injective_of_tensor_injective : ∀ (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁] [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K] (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L), Function.Injective β → (∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r) → ∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
  first | exact @GlobalTheory.tensor_fraction_injective_of_injective | exact GlobalTheory.tensor_fraction_injective_of_injective | (intros; apply GlobalTheory.tensor_fraction_injective_of_injective <;> assumption)
end

