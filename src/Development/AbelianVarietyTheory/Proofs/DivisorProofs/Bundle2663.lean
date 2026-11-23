module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentNumberFieldEndomorphismsTateMod
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CMFaithful

theorem linearIndependent_actTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => actTate α.toRingAct l (ptOver K Ω) (a i)) := by
  intro K Ω _ _ _ _ A _ _ hA hd F _ _ O _ _ _ α l _ hl n a ha
  obtain ⟨d, hd0, hdim⟩ := hd
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let t := spMap (algebraMap K (AlgebraicClosure Ω))
  let B := (Over.pullback t).obj A
  let β := OAct.pullback t A α
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme (AlgebraicClosure Ω) B hB
  obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := GlobalTheory.SS.exists_quadraticForm_end (AlgebraicClosure Ω) B hB L hL
  let ψ : O →+ Additive (B ⟶ B) := AddMonoidHom.mk' (fun x => Additive.ofMul (β.act x))
    (fun x y => by rw [β.add]; rfl)
  let H : AddSubgroup (Additive (B ⟶ B)) :=
    { carrier := {f | IsMonHom (Additive.toMul f)}
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        haveI : IsMonHom (Additive.toMul f) := hf
        haveI : IsMonHom (Additive.toMul g) := hg
        rw [Hom.mul_def]; infer_instance
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f)⁻¹
        haveI : IsMonHom (Additive.toMul f) := hf
        infer_instance }
  have hu : ∀ i, ψ (a i) ∈ H := fun i => β.hom (a i)
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx =>
    _root_.GlobalTheory.ActTrivialInj.eq_zero_of_act_pullback_eq_one K Ω A hA ⟨d, hd0, hdim⟩ l hl F O α x (by
      have : Additive.toMul (ψ x) = Additive.toMul 0 := congrArg _ hx
      exact this)
  have hindep : LinearIndependent ℤ (fun i => ψ (a i)) := by
    have h1 : LinearIndependent ℤ (fun i => algebraMap O F (a i)) := ha.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ a := by
      refine LinearIndependent.of_comp (algebraMap O F).toAddMonoidHom.toIntLinearMap ?_
      exact h1
    exact h2.map' ψ.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨e, he, hE⟩ := _root_.GlobalTheory.exists_dvd_coords_of_definite_form (Additive (B ⟶ B)) H (fun f => Q (Additive.toMul f))
    (fun f g => by
      have := hQ1 (Additive.toMul f) (Additive.toMul g)
      simpa [div_eq_mul_inv] using this)
    (fun f => hQ2 _) (fun f hf h0 => by
      have := hQ3 (Additive.toMul f) hf h0
      exact this) n (fun i => ψ (a i)) hu hindep
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj⟩ := hne
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.padicInt_toZModPow_not_dvd_mul l (c j) hj e he
  haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let m : Fin n → ℤ := fun i => ((PadicInt.toZModPow N (c i)).val : ℤ)
  have hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)) := fun i => by
    simp [m]
  let φ : Fin n → ((ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A)) := fun i => actPts α.toRingAct (ptOver K Ω) (a i)
  have kill := GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation (ptOver K Ω ⟶ A) l n φ c hc N m hm
  let x : O := ∑ i, m i • a i
  have hcomp : ∀ y : ptOver K Ω ⟶ A, y ≫ α.act x = ∏ i, (y ≫ α.act (a i)) ^ m i := by
    intro y
    let χ : O →+ Additive (ptOver K Ω ⟶ A) := AddMonoidHom.mk' (fun z => Additive.ofMul (y ≫ α.act z))
      (fun z w => by rw [α.add, MonObj.comp_mul]; rfl)
    have e1 : χ x = ∑ i, m i • χ (a i) := by simp only [x, map_sum, map_zsmul]
    have e2 := congrArg Additive.toMul e1
    rw [toMul_sum] at e2
    simp only [toMul_zsmul] at e2
    exact e2
  have hcard : ∀ k : ℕ, Nat.card {y : ptOver K Ω ⟶ A // y ^ (l ^ k) = 1} = l ^ (2 * d * k) := fun k => by
    rw [_root_.GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hdim (l ^ k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm k]
  have hx : ∀ y : ptOver K Ω ⟶ A, y ^ (l ^ N) = 1 → y ≫ α.act x = 1 := by
    intro y hy
    obtain ⟨tt, rfl⟩ := _root_.GlobalTheory.exists_tate_lev_eq_of_card_torsion (ptOver K Ω ⟶ A) l (2 * d) hcard N y hy
    rw [hcomp, ← kill tt]
    rfl
  obtain ⟨h, hh, hfh⟩ := _root_.GlobalTheory.SepClosedDivisible.divisible_algClosure K Ω A hA (l ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl) (α.act x) (α.hom x) hx
  have hsum : (l ^ N) • Additive.ofMul h = ∑ i, m i • ψ (a i) := by
    rw [← ofMul_pow, ← hfh]
    change ψ x = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, map_sum, map_zsmul]
  have := hE (l ^ N) m (Additive.ofMul h) hh hsum j
  exact hN (m j) (hm j) (by exact_mod_cast this)

end GlobalTheory.CMFaithful
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointEqOfAlgIndependentQuotients
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.GenericImage

open scoped GlobalTheory.ProjSpace

theorem map_genericPoint_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  intro k _ X _ p D _ π hπ x hx0 ⟨h, hx⟩ hinj
  set W := π ⁻¹ᵁ ProjSpace.chart k D 0 with hW
  let Φ : Γ(PSpace k D, ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ W (genericPoint X) h).hom.comp (π.appLE (ProjSpace.chart k D 0) W le_rfl).hom
  have hconst : (X.presheaf.germ W (genericPoint X) h).hom.comp
      (GlobalTheory.QCoh.Qcqs.baseRingHom (π ≫ PSpace.str k D) W).hom = GlobalTheory.toFunctionField p := by
    subst hπ
    refine RingHom.ext fun a => ?_
    simp only [GlobalTheory.QCoh.Qcqs.baseRingHom, GlobalTheory.toFunctionField, Scheme.Hom.appLE, CommRingCat.hom_comp,
      RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  have key : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 → Φ a ≠ 0 := by
    intro a ha
    obtain ⟨P, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 a
    let s : Fin (D + 1) → MvPolynomial (Fin D) k := Fin.cons 1 MvPolynomial.X
    have e1 : ∀ (A : Type) [CommRing A] (c : k →+* A) (r : Fin (D + 1) → A), r 0 = 1 →
        MvPolynomial.eval₂Hom c r P =
          MvPolynomial.eval₂Hom c (fun j : Fin D => r j.succ) (MvPolynomial.bind₁ s P) := by
      intro A _ c r hr
      rw [MvPolynomial.eval₂Hom_bind₁]
      congr 2
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [s, hr]
      · simp [s]
    have e2 : Φ (MvPolynomial.aeval (ProjSpace.ratio k D 0) P) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) P := by
      have := congrArg (fun t => t P) (ProjSpace.appLE_comp_aeval_ratio (φ := π) (W := W) (i := 0) (hi := le_rfl))
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this
      simp only [Φ, RingHom.comp_apply]
      erw [this]
      rw [MvPolynomial.map_eval₂Hom, hconst]
      congr 2
      funext j
      exact hx j
    rw [e2, e1 _ _ _ (div_self hx0)]
    intro h0
    have hQ : MvPolynomial.bind₁ s P = 0 := hinj (h0.trans (map_zero _).symm)
    apply ha
    rw [MvPolynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom,
      e1 _ _ _ (by rw [ProjSpace.ratio, ProjSpace.ratioOn_self]), hQ, map_zero]
  have hmem : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 →
      π (genericPoint X) ∈ (PSpace k D).basicOpen a := by
    intro a ha
    have h1 : genericPoint X ∈ X.basicOpen ((π.appLE (ProjSpace.chart k D 0) W le_rfl).hom a) := by
      rw [Scheme.mem_basicOpen X _ _ h]
      exact (key a ha).isUnit
    have h2 := (Scheme.basicOpen_appLE π W _ le_rfl a).le h1
    exact h2.2
  refine IsGenericPoint.eq ?_ (genericPoint_spec _)
  refine Dense.closure_eq (dense_iff_inter_open.2 fun U hU hne => ?_)
  obtain ⟨y, -, hyU, hyc⟩ := (IrreducibleSpace.isIrreducible_univ (PSpace k D)).2 U
    (ProjSpace.chart k D 0 : Set (PSpace k D)) hU (ProjSpace.chart k D 0).2
    (by simpa using hne) ⟨π (genericPoint X), trivial, h⟩
  obtain ⟨f, hf, hyf⟩ := (ProjSpace.isAffineOpen_chart k D 0).exists_basicOpen_le
    (V := ⟨U, hU⟩) ⟨y, hyU⟩ hyc
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  exact ⟨_, hf (hmem f hf0), rfl⟩

end GlobalTheory.GenericImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasIntegralEqChartDensityIntegral
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.VolDens

theorem meas_integral_in_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D) (c : AlgChart p σ D) (S : Set (CxPts p σ))
    (F : CxPts p σ → ℝ), MeasurableSet S → S ⊆ c.e.source → Continuous F →
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) ∧
    ∫ y in S, F y ∂ω.meas = ∫ v in c.e '' S, F (c.e.symm v) * ω.dens c (c.e.symm v) := by
  intro k _ X _ p D hX σ ω c S F hS hc hF
  haveI : SecondCountableTopology (CxPts p σ) :=
    CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have hmeas : ∀ A : Set (CxPts p σ), MeasurableSet A → A ⊆ c.e.source →
      ω.meas A = ∫⁻ v in c.e '' A, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
    intro A hA hAc
    rw [VolDens.meas, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
      rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hA hAc,
      ChartGlue.chartMeas_apply_of_subset _ _ hA hAc]
  refine ⟨hmeas S hS hc, ?_⟩
  have hSm : MeasurableSet (c.e '' S) := ChartGlue.measurableSet_image c.e hS hc
  have hSt : c.e '' S ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hc hy)
  set f : _ → ENNReal := fun v => ENNReal.ofReal (ω.dens c (c.e.symm v)) with hf
  set ν := (volume.restrict (c.e '' S)).withDensity f with hν
  have haem : AEMeasurable c.e.symm ν :=
    ((c.e.continuousOn_symm.mono hSt).aemeasurable hSm).mono_ac (withDensity_absolutelyContinuous _ _)
  have hrest : ω.meas.restrict S = Measure.map c.e.symm ν := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable haem hA,
      hmeas (A ∩ S) (hA.inter hS) (Set.inter_subset_right.trans hc), hν, withDensity_apply' _ _,
      Measure.restrict_restrict' hSm]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hyS⟩, rfl⟩
      exact ⟨by simpa [c.e.left_inv (hc hyS)] using hyA, ⟨y, hyS, rfl⟩⟩
    · rintro ⟨hvA, y, hyS, rfl⟩
      exact ⟨y, ⟨by simpa [c.e.left_inv (hc hyS)] using hvA, hyS⟩, rfl⟩
  have hfm : AEMeasurable f (volume.restrict (c.e '' S)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
    refine ContinuousOn.aemeasurable ?_ hSm
    refine (ω.cont c).comp (c.e.continuousOn_symm.mono hSt) ?_
    intro v hv
    exact c.e.map_target (hSt hv)
  rw [hrest, integral_map haem hF.aestronglyMeasurable, hν,
    integral_withDensity_eq_integral_toReal_smul₀ hfm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hSm fun v hv => ?_
  have hpos := ω.pos c _ (c.e.map_target (hSt hv))
  simp only [hf, smul_eq_mul, ENNReal.toReal_ofReal hpos.le, mul_comm]

end GlobalTheory.HSAmp.VolDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ) (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (L : Fin D → MLine p σ) (g : CxPts p σ → ℝ), Measurable g → (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧ (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  first | exact @GlobalTheory.Mix.int_eq_mInt | exact GlobalTheory.Mix.int_eq_mInt | (intros; apply GlobalTheory.Mix.int_eq_mInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubscheme
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem cycInt_of_closedImmersion : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (σ : k →+* ℂ), IsProjOver p → ∀ [IsIntegral Y] (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (D : ℕ)
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ),
    (CycIntg L f (π (genericPoint Y)) ↔ Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y))) ∧
      cycInt L f (π (genericPoint Y)) = Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp _ π _ hπ D L f
  generalize hz : π (genericPoint Y) = z
  obtain ⟨_, -, -, hY⟩ := GlobalTheory.ClosFacts.clos_facts X z
  obtain ⟨g, hgπ, -, -, hiso⟩ := hY Y π hz
  have : IsIso g := hiso inferInstance
  subst hgπ
  have hpz : IsProjOver (closι z ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hq : IsProjOver q := hπ ▸ ProjSpace.isProjOver_comp_of_isClosedImmersion (g ≫ closι z) hp
  have hg : g ≫ (closι z ≫ p) = q := by rw [← Category.assoc]; exact hπ
  obtain ⟨hI, hE⟩ := _root_.GlobalTheory.MixIso.intg_int_pull k (clos z) Y (closι z ≫ p) q σ hpz g hg D (fun i => (L i).pull (closι z) rfl)
    (fun y => f (ptMap (closι z) rfl σ y))
  have hiso' : ∀ i, (((L i).pull (closι z) rfl).pull g hg).Isom ((L i).pull (g ≫ closι z) hπ) := fun i =>
    (_root_.GlobalTheory.Mix.isom_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl).2.2.2.2.2 Y q g hg hπ (L i)
  have hpart : ∀ ε, part (fun i => ((L i).pull (closι z) rfl).pull g hg) ε = part (fun i => (L i).pull (g ≫ closι z) hπ) ε :=
    _root_.GlobalTheory.Mix.part_eq_of_isom k Y q σ hq D _ _ hiso'
  have hfun : (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) = fun y => f (ptMap (g ≫ closι z) hπ σ y) := by
    funext y; exact congrArg f (PtsOver.map_map _ _ _ _ _ y)
  have hI' : Intg (fun i => ((L i).pull (closι z) rfl).pull g hg) (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) ↔
      Intg (fun i => (L i).pull (g ≫ closι z) hπ) (fun y => f (ptMap (g ≫ closι z) hπ σ y)) := by
    rw [hfun]; simp only [Intg, hpart]
  have hE' : Mix.int (fun i => ((L i).pull (closι z) rfl).pull g hg) (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) =
      Mix.int (fun i => (L i).pull (g ≫ closι z) hπ) (fun y => f (ptMap (g ≫ closι z) hπ σ y)) := by
    rw [hfun]; simp only [Mix.int, hpart]
  exact ⟨hI.symm.trans hI', hE.symm.trans hE'⟩

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_iso_symm : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T →
    ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧
    (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)),
      recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧
    (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ)
      (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  intro _ k _ Y _ _ q hq e hY T hT M r hr
  have hd : ∀ z : Y, ((M.div hr).mult z : ℝ) ≠ 0 → HasDim z e := fun z hz =>
    ((_root_.GlobalTheory.MixHt.dimOne k Y q hq e hY).1 z).1
      (CartierDiv.coheight_eq_one_of_mult_ne_zero fun h => hz (by rw [h]; simp))
  refine ⟨fun L L' h => ?_, fun L τ => ?_, fun L M' h => ?_⟩
  · unfold recVal
    rw [(_root_.GlobalTheory.MixHt.mixArch_iso_symm_congr k Y q e L M r hr).1 L' h]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.iso e L L' z le_rfl (hd z hz) h]
  · unfold recVal
    rw [(_root_.GlobalTheory.MixHt.mixArch_iso_symm_congr k Y q e L M r hr).2.1 τ]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.symm e L τ z le_rfl (hd z hz)]
  · obtain ⟨r', hr', hdiv, hlog⟩ := h.exists_isRatSec hr
    refine ⟨r', hr', ?_⟩
    unfold recVal
    rw [(_root_.GlobalTheory.MixHt.mixArch_iso_symm_congr k Y q e L M r hr).2.2 M' r' hr' hdiv hlog, hdiv]

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAdditiveCubicalStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_add_cub : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hτ hF Z x x' y x₀ x₀' y₀ hx hx' hy z J J' hJ hJ'
  have hn : ∀ (T' : Over (Sp V)) (z : T'.left) (J : (T'.left ⟶ T.B.left) → T.M.L.ι)
      (J' : (T'.left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T' ⟶ D.P.A) (1 : T' ⟶ D.P.A)).left z J J' = 1 := fun T' z J J' hJ hJ' =>
    (_root_.GlobalTheory.TInj.lamVal_axes_one T ε n V D ω s e β ββ w hτ hF T' 1 z J J' hJ hJ').1
  have L := GlobalTheory.LamRigid.lam_iso_laws (Sp W) (Sp V) T.B D.P.A T.M _ T.cub D.cub (spMap ω) β ββ w hF.1 D.P.isAb
    hF.2.1 hF.2.2.1 hn
  have C₁ : IsCub (cubV D.cub z J') := isCub_cubV D.cub hJ'
  have C₀ : IsCub (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J) := isCub_cubV T.cub hJ
  have A₁ := (L Z x x' y z J J' hJ hJ').2 x₀ x₀' y₀ hx.symm hx'.symm hy.symm
  refine ⟨?_, ?_⟩
  · rw [A₁]; simp only [id]; ac_rfl
  · rw [(L Z y y (x * x') z J J' hJ hJ').1, (L Z y y x z J J' hJ hJ').1, (L Z y y x' z J J' hJ hJ').1,
      C₁.s01 y x x', C₁.s12 x y x', C₀.s01 y₀ x₀ x₀', C₀.s12 x₀ y₀ x₀', A₁]
    simp only [id]; ac_rfl

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCokerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_eq_inv_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ), Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  first | (exact @GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker) | (exact GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker) | (intros; apply GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker  <;> assumption)
end

