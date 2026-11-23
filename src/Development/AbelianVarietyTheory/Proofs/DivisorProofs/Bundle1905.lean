module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionGeneratesAtVanishesAtFinset
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.CommonEqnOpen

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_pow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_pow_mul_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) (t : Γ(X, U))
    (ht : genericPoint X ∈ X.basicOpen t) {f : X.functionField}
    (h : ∀ z ∈ X.basicOpen t, RegAt z f) :
    ∃ (n : ℕ) (a : Γ(X, U)), fnOf U hg t ^ n * f = fnOf U hg a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := hU.isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, U)) : fnOf _ ht (algebraMap Γ(X, U) Γ(X, X.basicOpen t) c) =
      fnOf U hg c := fnOf_resG (X.basicOpen_le t) ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

theorem exists_regularAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨W, hW, hgW⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htW, ht⟩ := hU.exists_basicOpen_le ⟨x, hW⟩ hxU
  obtain ⟨t', htV, ht'⟩ := hU.exists_basicOpen_le ⟨y, hV⟩ hyU
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq hU (gen_mem hxU) (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgW z (htW hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf U (gen_mem hxU) (t' ^ n)) := by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hyU _ _).2 ht') n
  refine ⟨t ^ n, (unitAt_fnOf_iff hxU (gen_mem hxU) _).1 (by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hxU _ _).2 ht) n), g', hgV y hV, ?_⟩
  have := (regAt_fnOf hyU (gen_mem hxU) a).mul hu.inv.regAt
  rw [← e] at this
  convert this using 1
  have h0 := hu.ne_zero
  rw [map_pow] at h0
  rw [map_mul, map_pow, map_pow, mul_pow]
  field_simp

theorem exists_vanishesAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U)
    (hxy : x ∉ closure ({y} : Set X)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hU hxU hg hyU
  obtain ⟨t, htU, ht⟩ := hU.exists_basicOpen_le
    (V := ⟨(closure ({y} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨x, hxy⟩ hxU
  have hz : ZeroAt y (fnOf U (gen_mem hxU) t) := zeroAt_iff.2 ⟨regAt_fnOf hyU _ _,
    fun h => htU ((unitAt_fnOf_iff hyU _ _).1 h) (subset_closure rfl)⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf U (gen_mem hxU) s)]
  exact hz.mul hr

theorem exists_generatesAt_vanishesAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U →
    ∀ (D : CartierDiv X) (x : X), x ∈ U →
    ∀ (T : Finset X), (∀ y ∈ T, y ∈ U) → (∀ y ∈ T, y ≠ x → x ∉ closure ({y} : Set X)) →
    ∃ f : X.functionField, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  intro X _ U hU D x hxU T hTU hT
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff hxU _ _).2 hs
  have key (y : X) (hyU : y ∈ U) (s t : Γ(X, U))
      (h : D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf U (gen_mem hxU) (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf hyU (gen_mem hxU) t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simpa using hxU, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih (fun z hz => hTU z (Finset.mem_insert_of_mem hz))
      fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    have hyU := hTU y (Finset.mem_insert_self _ _)
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hU hxU hg hyU (hT y (Finset.mem_insert_self _ _) hyx)
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ hyU _ _ h'
    · exact key _ (hTU z (Finset.mem_insert_of_mem hz)) _ _ (h z hz hzx)

end GlobalTheory.Cartier.CommonEqnOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteIsAlgClosedComplexRatVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RatNorm

open Cardinal IsLocalRing

theorem mk_le_of_dense {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

end GlobalTheory.RatNorm

namespace GlobalTheory.MBLow

open Cardinal IsLocalRing GlobalTheory.RatNorm ReciprocityTheory.ChartRestriction.G.DVR

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFramedPointOverComponentGenericPoin
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.AllWt (ptF)

namespace GlobalTheory.GenCxPt

open Cardinal

theorem mk_le_aleph0 (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] : #K ≤ ℵ₀ := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  rw [Cardinal.mkRat, max_self] at h
  exact h

theorem transcendental_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    Algebra.Transcendental K ℂ := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  have h := Algebra.IsAlgebraic.cardinalMk_le_max K ℂ
  rw [Cardinal.mk_complex, max_eq_right (mk_le_aleph0 K)] at h
  exact absurd h (not_le.2 Cardinal.aleph0_lt_continuum)

theorem infinite_of_isTranscendenceBasis (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {κ : Type}
    {w : κ → ℂ} (hw : IsTranscendenceBasis K w) : Infinite κ := by
  haveI : Nonempty κ := hw.nonempty_iff_transcendental.2 (transcendental_complex K)
  have h := hw.lift_cardinalMk_eq_max_lift
  simp only [Cardinal.lift_id, Cardinal.mk_complex] at h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have h1 : #κ ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite κ).le
  have h2 : #K ⊔ #κ ⊔ ℵ₀ ≤ ℵ₀ := sup_le (sup_le (mk_le_aleph0 K) h1) le_rfl
  rw [← h] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

theorem nonempty_algHom_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (L : Type) [Field L]
    [Algebra K L] (n : ℕ) (hn : Algebra.trdeg K L = n) : Nonempty (L →ₐ[K] ℂ) := by
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' K L
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' K ℂ
  haveI := infinite_of_isTranscendenceBasis K hw
  have hι : #ι < ℵ₀ := by rw [hv.cardinalMk_eq_trdeg, hn]; exact Cardinal.natCast_lt_aleph0
  haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.1 hι
  have hle : #ι ≤ #κ := hι.le.trans (Cardinal.infinite_iff.1 inferInstance)
  obtain ⟨f⟩ := hle
  obtain ⟨j, -⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hv (hw.1.comp f f.injective)
  exact ⟨j⟩

end GlobalTheory.GenCxPt

namespace GlobalTheory.GenCxPt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

end GlobalTheory.GenCxPt


open GlobalTheory.GenCxPt in
theorem GlobalTheory.GenCxPt.exists_frPt_ptF_eq_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c),
    ∃ y : FrPt Xo c ℂ, ∀ s, ptF y s = genPt Z := by
  intro E _ _ _ H Dw l Xo c Z
  haveI := c.fin
  obtain ⟨e⟩ := nonempty_algHom_complex c.F (kap Z) Dw.dim ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2 Z)
  have hsnd : spMap (e : kap Z →+* ℂ) ≫ genSp Z ≫ strK = spMap (algebraMap c.F ℂ) := by
    rw [genSp_strK, spMap_comp_spMap, AlgHom.comp_algebraMap]
  have hx : (spMap (e : kap Z →+* ℂ) ≫ xGen Z) ≫ Xo.s = sOf c ℂ := by
    rw [xGen, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (genSp Z),
      ← Category.assoc, hsnd, sOf, spMap_comp_spMap]
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt _ hx
  refine ⟨y, fun s => ?_⟩
  have hpt : ptF y = spMap (e : kap Z →+* ℂ) ≫ genSp Z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hy, xGen, Category.assoc]
    · rw [ptF, pullback.lift_snd, Category.assoc, ← hsnd]
  rw [hpt]
  have : (spMap (e : kap Z →+* ℂ) ≫ genSp Z) s ∈ Set.range (genSp Z) :=
    ⟨spMap (e : kap Z →+* ℂ) s, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [genSp, Scheme.range_fromSpecResidueField] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOnStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_integral_framedPoint_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  first | exact @GlobalTheory.IntFrComp.exists_liesOn | exact GlobalTheory.IntFrComp.exists_liesOn | (intros; apply GlobalTheory.IntFrComp.exists_liesOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantComponentFunctionComplexValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.OneValue

theorem isAlgebraic_of_one_value {F A C : Type} [Field F] [CommRing A] [Nontrivial A] [IsReduced A] [Algebra F A]
    [Algebra.FiniteType F A] [Field C] [IsAlgClosed C] [Algebra F C] (s : A)
    (h : ∀ φ ψ : A →ₐ[F] C, φ s = ψ s) : IsAlgebraic F s := by
  have hJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have key : ∀ m : Ideal A, m.IsMaximal →
      ∃ φ : A →ₐ[F] C, (∀ a, φ a = 0 → a ∈ m) ∧ IsAlgebraic F (φ s) := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
    let σ : (A ⧸ m) →ₐ[F] C := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨σ.comp (Ideal.Quotient.mkₐ F m), fun a ha => ?_, ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.1 (σ.toRingHom.injective (ha.trans (map_zero σ.toRingHom).symm))
    · exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m s)).algHom σ
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -, P, hP, hPs⟩ := key m₀ hm₀
  refine ⟨P, hP, ?_⟩
  have hj : Polynomial.aeval s P ∈ (⊥ : Ideal A).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ, -⟩ := key m hm
    refine hφ _ ?_
    rw [← Polynomial.aeval_algHom_apply, h φ φ₀, hPs]
  rwa [hJ.out (Ideal.isRadical_bot_iff.2 inferInstance), Ideal.mem_bot] at hj

theorem valR_spMap_fromSpec {X : Scheme.{0}} {R : Type} [CommRing R] {U W : X.Opens} (hW : IsAffineOpen W)
    (e : W ≤ U) (φ : Γ(X, W) →+* R) (f : Γ(X, U)) :
    valR (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) U f = φ (resG X e f) := by
  have h0 : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun y _ => e (h0 (Set.mem_univ ((Spec.map (CommRingCat.ofHom φ)) y)))
  unfold valR
  rw [dite_eq_left h]
  have e1 : (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h =
      X.presheaf.map (homOfLE e).op ≫ hW.fromSpec.appLE W ⊤ h0 ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [← Category.assoc, Scheme.Hom.map_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ _ le_rfl).symm
  have e2 : hW.fromSpec.appLE W ⊤ h0 = (Scheme.ΓSpecIso Γ(X, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f =
    (X.presheaf.map (homOfLE e).op ≫ CommRingCat.ofHom φ).hom f
  rw [e1, e2, Category.assoc, Category.assoc]
  erw [n]
  erw [(Scheme.ΓSpecIso Γ(X, W)).inv_hom_id_assoc]

theorem exists_eq_algX {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [GeometricallyIntegral p]
    [LocallyOfFiniteType p] (e : F →+* ℂ) (f : Γ(Y, ⊤))
    (h : ∀ y y' : Sp ℂ ⟶ Y, y ≫ p = spMap e → y' ≫ p = spMap e → valR y ⊤ f = valR y' ⊤ f) :
    ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2)
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) := hc
  letI : Algebra F ℂ := e.toAlgebra
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hpt : ∀ φ : Γ(Y, U) →ₐ[F] ℂ,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec : Sp ℂ ⟶ Y) ≫ p = spMap e := by
    intro φ
    rw [Category.assoc, hg, ← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a
  obtain ⟨P, hP, hPs⟩ := isAlgebraic_of_one_value (F := F) (C := ℂ) (resG Y hUV f) fun φ ψ => by
    have := h _ _ (hpt φ) (hpt ψ)
    rwa [valR_spMap_fromSpec hU hUV, valR_spMap_fromSpec hU hUV] at this
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Y p (GlobalTheory.Cartier.fnOf ⊤ trivial f) ⟨P, hP, by
    rw [← GlobalTheory.Cartier.fnOf_comp_algX p U hxU, ← GlobalTheory.Cartier.fnOf_resG hUV hxU, ← Polynomial.hom_eval₂]
    exact (congrArg _ hPs).trans (map_zero _)⟩
  exact ⟨a, (GlobalTheory.Cartier.fnOf_injective ⊤ trivial ha).symm⟩

theorem exists_eq_constFn_of_one_value :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (f : Γ(Xo.XF c, U)), GeometricallyConnected (U.ι ≫ toF Xo c) → (∀ y y' : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → valR y U f = valR y' U f) → ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (toF Xo c) U a := by
  intro E _ _ _ H D l Xo c U e f hU h
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2
  have hval : ∀ y : Sp ℂ ⟶ U.toScheme, valR y ⊤ ((U.ι.appLE U ⊤ hle).hom f) = valR (y ≫ U.ι) U f := by
    intro y
    have h1 : ⊤ ≤ y ⁻¹ᵁ ⊤ := le_top
    have h2 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := fun x _ => (y x).2
    unfold valR
    rw [dite_eq_left h1, dite_eq_left h2, ← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ hle h1]
    rfl
  have hr : ∀ y : Sp ℂ ⟶ U.toScheme, Set.range (y ≫ U.ι) ⊆ U := by
    rintro y _ ⟨x, rfl⟩
    exact (y x).2
  obtain ⟨a, ha⟩ := exists_eq_algX (U.ι ≫ toF Xo c) e ((U.ι.appLE U ⊤ hle).hom f) fun y y' hy hy' => by
    rw [hval, hval]
    exact h _ _ ((Category.assoc _ _ _).trans hy) ((Category.assoc _ _ _).trans hy') (hr y) (hr y')
  refine ⟨a, ?_⟩
  have hiso : IsIso (U.ι.appLE U ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : U.ι ''ᵁ ⊤ = U := U.ι_image_top
    have : IsIso (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) U.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (U.ι.appLE U ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE U.ι (toF Xo c) ⊤ U ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.OneValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltLocusFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
open GlobalTheory.Adelic.LinSys
namespace GlobalTheory.BoundaryFibre

theorem eff_nsmul {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

end GlobalTheory.BoundaryFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerSemiAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_eighthPower_semiAbelianScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∃ (G₈ : Over (Sp R)) (_ : GrpObj G₈) (prG : Fin 8 → (G₈ ⟶ G)), IsSemiAbelian G₈ ∧ (∀ u, IsMonHom (prG u)) ∧ ∀ (T : Over (Sp R)) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ G₈, ∀ u, x ≫ prG u = y u := by
  intro R _ G _ hG
  haveI : IsCommMonObj G := hG.comm
  refine ⟨powObj G 8, inferInstance, powPr G, ?_, fun u => inferInstance, fun T y => ?_⟩
  · exact GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G 8) G 8 (powIsPowGrp G 8) hG
  · refine ⟨(powIsLimit G 8).lift (Fan.mk T y), fun u => (powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩, ?_⟩
    intro x hx
    apply (powIsLimit G 8).hom_ext
    rintro ⟨u⟩
    exact (hx u).trans ((powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩).symm

end GlobalTheory.MBLow
end

