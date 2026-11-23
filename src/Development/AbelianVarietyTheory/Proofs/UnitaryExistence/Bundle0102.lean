module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjDatum
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPoint
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedInFunctionFieldOfAutFixPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id | exact GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id | (intros; apply GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpaceStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameUniformisation_prescribedSpace : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  first | exact @GlobalTheory.FrameUnif.exists_unf_of_space | exact GlobalTheory.FrameUnif.exists_unf_of_space | (intros; apply GlobalTheory.FrameUnif.exists_unf_of_space <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeIsometryConjSplitPointAnyLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat


open ConjIsometry in
theorem exists_isometry_of_conj_split_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    _root_.GlobalTheory.ConjSplitAnyLevel.exists_conj_lattice_map E H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := _root_.GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := _root_.GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpacesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompSystem.exists_orthogonal_idempotents | exact GlobalTheory.CompSystem.exists_orthogonal_idempotents | (intros; apply GlobalTheory.CompSystem.exists_orthogonal_idempotents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CompRat.SplitSum

theorem finrank_prod_int {E : Type} [Field E] [NumberField E] (M N : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N] :
    Module.finrank (𝓞 E) (M × N) = Module.finrank (𝓞 E) M + Module.finrank (𝓞 E) N := by
  have h1 := (TensorProduct.isBaseChange (𝓞 E) (M × N) E).finrank_eq
  have h2 := (TensorProduct.isBaseChange (𝓞 E) M E).finrank_eq
  have h2' := (TensorProduct.isBaseChange (𝓞 E) N E).finrank_eq
  have h3 := (TensorProduct.prodRight (𝓞 E) E E M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

def prodSubEquiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Submodule R M) (B : Submodule R N) : (A.prod B) ≃ₗ[R] A × B where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_prod_sub {E : Type} [Field E] [NumberField E] {M N : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N]
    (A : Submodule (𝓞 E) M) (B : Submodule (𝓞 E) N) :
    Module.finrank (𝓞 E) (A.prod B) = Module.finrank (𝓞 E) A + Module.finrank (𝓞 E) B := by
  rw [(prodSubEquiv A B).finrank_eq, finrank_prod_int]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem splitLat_sum {D D' : Datum H} (h : SplitLat D) (h' : SplitLat D') : SplitLat (DatumSum.sumDatum D D') := by
  obtain ⟨Lp, Lm, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨Lp', Lm', h1', h2', h3', h4', h5', h6'⟩ := h'
  have := D.fin
  have := D'.fin
  have hE : ∀ x y : D.La × D'.La, (DatumSum.sumDatum D D').EF x y = D.EF x.1 y.1 + D'.EF x.2 y.2 :=
    fun x y => DatumSum.sumForm_apply D.EF D'.EF x y
  have hR : ∀ x : D.La × D'.La, (DatumSum.sumDatum D D').EF (H.rt • x) x =
      D.EF (H.rt • x.1) x.1 + D'.EF (H.rt • x.2) x.2 := fun x => hE _ _
  refine ⟨Lp.prod Lp', Lm.prod Lm', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : Lp.prod Lp' ⊔ Lm.prod Lm' = ⊤ := by
      rw [Submodule.prod_sup_prod, h1, h1', Submodule.prod_top]
    exact this
  · intro a ha b hb
    refine (hE a b).trans ?_
    rw [h2 _ ha.1 _ hb.1, h2' _ ha.2 _ hb.2, add_zero]
  · exact (finrank_prod_sub Lp Lp').trans (by rw [h3, h3']; rfl)
  · exact (finrank_prod_sub Lm Lm').trans (by rw [h4, h4']; rfl)
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h5' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h5 _ ha.1 h0
      · exact add_pos (h5 _ ha.1 h0) (h5' _ ha.2 h0')
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h6' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h6 _ ha.1 h0
      · exact add_neg (h6 _ ha.1 h0) (h6' _ ha.2 h0')

end GlobalTheory.CompRat.SplitSum

namespace GlobalTheory.CompRat

theorem exists_splitLat_of_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  intro E _ _ _ H p q ⟨D, hp, hq⟩
  refine ⟨DatumSum.sumDatum (powDatum D p) (powDatum (CM.ConjDatum.conj D) q), ?_, ?_, ?_⟩
  · change p * D.p + q * D.q = p
    simp [hp, hq]
  · change p * D.q + q * D.p = q
    simp [hp, hq]
  · refine SplitSum.splitLat_sum (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inr ?_)) (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inl ?_))
    · change p * D.q = 0
      simp [hq]
    · change q * D.q = 0
      simp [hq]

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ un dict mu, C.IsDict dict ∧ GlobalTheory.FrameUnif.FramesOK C.e C.F C.M un ∧ PkgLaws V C.hr C.ι Kf χ (C.unf un) dict mu C.x₀ := by
  intro D H Dw l Xo c σ V r C hC Kf hK χ hχ hχF
  have hS := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hT := GlobalTheory.firstFiveLaws.2.1.secTwist
  have hneg : GlobalTheory.FrameUnif.NegXi C.M :=
    (_root_.GlobalTheory.Member.exists_ctx D H Dw l Xo c σ V r C.hr C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨un, hun⟩ := GlobalTheory.FrameUnif.exists_framesOK hS hT _ H Dw l Xo c σ C.g C.e C.F r C.M hC.good hC.base hneg
  obtain ⟨dict, hd⟩ := _root_.GlobalTheory.Member.Ctx.exists_isDict D H Dw l Xo c σ V r C hC
  obtain ⟨mu, hval, hmul, hnorm, hrat, hcont⟩ := _root_.GlobalTheory.Member.exists_muVal D V χ hχ hχF
  have hU := GlobalTheory.FrameUnif.isUnf_built hS _ H Dw l Xo c σ C.g C.e C.F r C.M un hC.good hC.base hneg hun
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨un, dict, mu, hd, hun, ?_⟩
  refine
    { unf := (Formalism.L2.PjFree.isUnf_ofPj (C.unf un)).1 hU
      unTest := fun k x => GlobalTheory.Frames.allTest_of_secBaseChange hS _ H Dw l Xo c (CAt σ) (un k x)
      chi1 := hC.base.chi
      modelW := hC.modelW
      familyUniformisationBasePointOrthogonal := hC.orth
      muUnit := ⟨hmul, hnorm, hrat, (_root_.GlobalTheory.Member.dict_invariant D H Dw l Xo c σ V r C hC dict hd Kf hK).2.2.2.1⟩
      muCont := hcont
      muVal := hval
      adelAut := _root_.GlobalTheory.Member.adel_leftInv_and_continuous D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hcont
      expo := fun ρ => ⟨GlobalTheory.CuspCentre.latZ _ r ρ _ C.M.X,
        GlobalTheory.ExpoModels.expoMatch_models _ H Dw l Xo _ C.g _ C.F r C.M ρ hC.base hC.lA⟩
      dictLaws := ⟨C.g, C.e, C.F, id, C.M.φ, C.th, fun _ τ => hC.inf τ.1,
        _root_.GlobalTheory.Member.dictIsUnif_of_isDict D H Dw l Xo c σ V r C hC dict hd Kf hK, ⟨hC.base.ef, fun k x => ?_⟩, fun h => ?_⟩ }
  · obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun.1 k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  · obtain ⟨γ, ⟨h1, h2, h3⟩, h4⟩ := hd.1 h
    refine ⟨γ, h1, h2, h3, fun τ => ?_⟩
    exact congrFun h4 τ

end GlobalTheory.Member
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntChartFrTruncExists
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem GlobalTheory.IntChartTrunc.intChart_frTrunc_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT :=
  fun E _ _ _ H Dw l Xo c _ hstar T io y =>
    GlobalTheory.IntChartTrunc.exists_intChart_frTrunc _root_.GlobalTheory.intChart E H Dw l Xo c hstar (_root_.GlobalTheory.chartTransport_holds E H Dw l Xo c) T io y
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem marking_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∀ s, C.ActsBy τ io l.M s → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty F h1 h2 h3 h4 τ hτ C io hio i P hP i' P' hP' hs hu s hact
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := _root_.GlobalTheory.CompRat.exists_isometry_of_conj_split E H D l Xo σ g ty F h1 h2 h3 h4 τ hτ C io hio i P hP i' P' hP' hs hu
  refine ⟨Φ, hΦ1, hΦ2, hΦ3, fun v hv a ha b hb hab => ?_⟩
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have key := hΦ4 l.M s hM hact a ha b hb
  have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ Xo.univ.eta v).left = y ≫ (Xo.univ.eta v).left := by
    intro y
    rw [Over.comp_left]
    congr 1
  rw [← hab, ← F.ex_eta i P hP v hv, tu, ← Category.assoc, hu, ← tu, F.ex_eta i' P' hP' v hv] at key
  set w := Φ (wE H s • a + H.bar (wE H s) • b) with hw
  have e : F.ex i' P' ((l.M : ℂ)⁻¹ • P' (F.t i' v)) = F.ex i' P' ((l.M : ℂ)⁻¹ • P' w) := Over.OverMorphism.ext key
  have e' := F.ex_add i' P' hP' ((l.M : ℂ)⁻¹ • P' (F.t i' v - w)) ((l.M : ℂ)⁻¹ • P' w)
  rw [← smul_add, ← map_add (f := _), sub_add_cancel, e] at e'
  obtain ⟨x, hx⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
  refine ⟨x, ?_⟩
  rw [← sub_eq_iff_eq_add']
  apply hP'.2.1
  rw [map_nsmul, hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hM', one_smul]

end GlobalTheory.CompRat
end

