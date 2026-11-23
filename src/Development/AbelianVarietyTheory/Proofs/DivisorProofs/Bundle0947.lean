module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0038
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjOfRelSimilitudePairsSameForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlaces
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  first
  | exact @_root_.GlobalTheory.MultiplierOrders.exists_order
  | exact _root_.GlobalTheory.MultiplierOrders.exists_order
  | (apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultiplierOrders.exists_order <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultiplierOrders.exists_order ..)

theorem isIntV_order_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (OB : Subring G.C)
    (hfin : Module.Finite ℤ OB) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x) := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OB)
  have H := Filter.eventually_all.2 fun i : Fin k => Filter.eventually_all.2 fun m =>
    ratCast_mem_intV_eventually p ((Module.finBasis ℚ G.C).repr (g i : G.C) m)
  refine H.mono fun v hv x hx => ?_
  have hx' : (⟨x, hx⟩ : OB) ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
  have e : (1 : Qv v) ⊗ₜ[ℚ] x = ∑ i, ((c i : ℤ) : Qv v) ⊗ₜ[ℚ] (g i : G.C) := by
    have hx2 : x = ∑ i, (c i : ℤ) • (g i : G.C) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    rw [hx2, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    simp
  rw [e]
  exact isIntV_of_eq_sum G v _ _ _ (fun i _ => intCast_mem _ _) (fun i _ m => hv i m)

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum

def theta (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime] :
    ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C ≃ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.congr (adicCompletion.padicEquiv v.1).symm.toAlgEquiv AlgEquiv.refl

theorem theta_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℚ_[(primesEquiv v.1 : ℕ)]) (c : G.C) :
    theta p G v (r ⊗ₜ c) = (adicCompletion.padicEquiv v.1).symm r ⊗ₜ c := rfl

theorem padicEquiv_symm_coe_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℤ_[(primesEquiv v.1 : ℕ)]) :
    (adicCompletion.padicEquiv v.1).symm (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨x, hx, hxr⟩ := (adicCompletion.padicEquiv_bijOn v.1).surjOn
    (show (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ PadicInt.subring _ from r.2)
  rw [← hxr, ContinuousAlgEquiv.symm_apply_apply]
  exact hx

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum GlobalTheory.LKInvGood

theorem isIntV_theta_locOrder (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p)
    [Fact (primesEquiv v.1 : ℕ).Prime] (OB : Subring G.C)
    (hO : ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x)) (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (y : ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C) (hy : y ∈ locOrder (primesEquiv v.1 : ℕ) OB) :
    IsIntV G v (theta p G v y) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [theta_tmul, map_one]
    exact hO c hc
  | algebraMap r =>
    rw [Algebra.TensorProduct.algebraMap_apply, theta_tmul]
    intro k
    rw [basV_repr_tmul]
    have h1k := h1 k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul] at h1k
    exact mul_mem (padicEquiv_symm_coe_mem p G v r) h1k
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact isIntV_add' G v hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

theorem finite_dvd (p : ℕ) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ¬ (primesEquiv v.1 : ℕ) ∣ N := by
  have hfin : {v : AwayP p | (primesEquiv v.1 : ℕ) ∣ N}.Finite := by
    have hinj : Function.Injective fun v : AwayP p => (primesEquiv v.1 : ℕ) :=
      fun a b h => Subtype.ext (primesEquiv.injective (Subtype.ext h))
    refine Set.Finite.of_finite_image ?_ hinj.injOn
    refine (Set.finite_le_nat N).subset ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Nat.le_of_dvd hN hv
  exact hfin.eventually_cofinite_notMem

theorem matrixUnits_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C,
      (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧
      ∀ i j, IsIntV G v (E i j) := by
  intro p _ G
  obtain ⟨OB, hfin, hspan⟩ := exists_order G.C
  obtain ⟨N, hN, hmat⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F G.C G.n G.rankC OB hfin hspan
  filter_upwards [finite_dvd p N hN, isIntV_order_eventually p G OB hfin, intV_order_eventually p G]
    with v hv hO hord
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨ψ, -⟩ := hmat (primesEquiv v.1 : ℕ) hv
  let E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C := fun i j =>
    theta p G v ((ψ.symm (Matrix.single i j 1) : locOrder (primesEquiv v.1 : ℕ) OB) :
      ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C)
  refine ⟨E, fun i j k l => ?_, ?_, fun i j =>
    isIntV_theta_locOrder p G v OB hO hord.1 hord.2.1 _ (ψ.symm _).2⟩
  · simp only [E]
    rw [← map_mul, ← Subalgebra.coe_mul, ← map_mul]
    split_ifs with hjk
    · subst hjk
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := hjk), map_zero, ZeroMemClass.coe_zero, map_zero]
  · have hs : ∑ i, (Matrix.single i i (1 : cenOrder (primesEquiv v.1 : ℕ) G.F) :
        Matrix (Fin G.n) (Fin G.n) (cenOrder (primesEquiv v.1 : ℕ) G.F)) = 1 := by
      ext a b
      rw [Matrix.sum_apply, Matrix.one_apply, Finset.sum_eq_single a]
      · by_cases h : a = b
        · subst h; simp [Matrix.single_apply]
        · simp [Matrix.single_apply, h]
      · intro c _ hc; simp [Matrix.single_apply, hc]
      · simp
    simp only [E]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum (theta p G v), ← AddSubmonoidClass.coe_finsetSum, ← map_sum ψ.symm, hs, map_one,
      OneMemClass.coe_one, map_one]

end GlobalTheory.OrbFinAf.MatrixUnits₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ThetaSumNe

theorem exists_mem_schA_thetaSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  intro F _ _ κ _
  classical
  let V := κ → mixedEmbedding.mixedSpace F
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨pureA F f g, hmem, ?_⟩
  set t : (κ → F) → ℂ := fun ξ => pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) with ht
  have hsum : Summable t := summable_pureA F f hg
  have hre : ∀ ξ, (t ξ).re = b (fun i => mixedEmbedding F (ξ i)) *
      (g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))).re := fun ξ => by
    simp only [ht, pureA_algebraMap, hf, Complex.re_ofReal_mul]
  have hg0 : ∀ y, 0 ≤ (g y).re := fun y => by
    by_cases hy : y ∈ GlobalTheory.SchANonzero.intPts F κ
    · simp [g, Set.indicator_of_mem hy]
    · simp [g, Set.indicator_of_notMem hy]
  have hnn : ∀ ξ, 0 ≤ (t ξ).re := fun ξ => by
    rw [hre]; exact mul_nonneg (b.nonneg) (hg0 _)
  have hz : (t 0).re = 1 := by
    rw [hre]
    have h0 : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem (v.adicCompletionIntegers F)
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    rw [hx, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply, Complex.one_re, one_mul]
  have hpos : 0 < ∑' ξ, (t ξ).re :=
    (Complex.reCLM.summable hsum).tsum_pos hnn 0 (by show 0 < (t 0).re; rw [hz]; exact one_pos)
  intro h
  have : (thetaSum F (pureA F f g)).re = ∑' ξ, (t ξ).re := Complex.re_tsum hsum
  rw [h, Complex.zero_re] at this
  exact hpos.ne' this.symm

end GlobalTheory.ThetaSumNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDeg

theorem etale_morphismRestrict_of_goodCover {k : Type} [CommRing k] {X Y : Scheme.{0}}
    (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (U : X.Opens) (hG : GoodCover p π D δ U) :
    Etale (π ∣_ U) := by
  obtain ⟨hU, hπU, -, hét, -⟩ := hG
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_map_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (O : X.Opens) (hO : O = X.basicOpen g) (hle : O ≤ W) :
    (X.presheaf.map (homOfLE hle).op).hom.Etale := by
  subst hO
  have := hW.isLocalization_basicOpen g
  exact Algebra.Etale.of_isLocalizationAway g

theorem algX_comp {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X)
    (W : X.Opens) (V : Y.Opens) (h : V ≤ π ⁻¹ᵁ W) :
    ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) V =
      (π.appLE W V h).hom.comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) := by
  have e : (π ≫ p).appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) =
      p.appLE ⊤ W (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ π.appLE W V h := by
    first
      | rw [Scheme.Hom.appLE_comp_appLE]
      | (rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE])
      | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc, Scheme.Hom.naturality_assoc]; rfl)
  ext r
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, RingHom.comp_apply]
  rw [e, CommRingCat.comp_apply]

theorem etale_pullback_coords : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  intro k _ X Y p q π hπ D δ U hG W x hW hx z hzU hzW
  subst hπ
  have hE := etale_morphismRestrict_of_goodCover p π D δ U hG
  obtain ⟨hU, hπU, -⟩ := hG
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

end GlobalTheory.CoverDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSubgroup

theorem exists_finite_subgroup_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : LB A.left) (H : Over (Sp K)) (_ : GrpObj H) (j : H ⟶ A), L.IsLB ∧ IsProjBy A.hom ∧ (∃ t : LB.Gen (Theta A L), t.IsGen) ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧ IsFinite H.hom ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro K _ _ A _ hA
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  obtain ⟨H₀, m, s, hH₀, hva, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple K A hA
  have hP : IsProjBy A.hom := ⟨H₀, hH₀, m, s, hva⟩
  obtain ⟨L, hL, hR⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy hP
  obtain ⟨H, j, hj, hf, hH⟩ := GlobalTheory.KernelRep.exists_finite_closed_kernel hG K A hA L hL hR
  haveI : Mono j.left := inferInstance
  haveI : Mono j := (Over.forget _).mono_of_mono_map this
  have hjK : GlobalTheory.MemKL A L j := (hH H j).2 ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (hH _ (1 : 𝟙_ (Over (Sp K)) ⟶ A)).1 (GlobalTheory.memKL_one hL _)
  have hm := (hH _ ((fst H H ≫ j) * (snd H H ≫ j))).1
    (GlobalTheory.UU.InK.mul hL (hjK.comp (fst H H)) (hjK.comp (snd H H)))
  have hn := (hH _ j⁻¹).1 (GlobalTheory.UU.InK.inv hL hjK)
  obtain ⟨g, hg⟩ := GlobalTheory.PointQuot.exists_grpObj_of_mono j h1.choose hm.choose hn.choose
    h1.choose_spec hm.choose_spec hn.choose_spec
  exact ⟨L, H, g, j, hL, hP, GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA L hL, hg, hj, hf, hH⟩

end GlobalTheory.KernelSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.PolRangeInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adAt (w : InfinitePlace F) (c : w.Completion) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) (Pi.single w c)

theorem piInf_adAt_same (v : InfinitePlace F) (τ : EmbOver E v) (c : v.Completion) (x : E) :
    piInf τ (adAt v c ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding v c * τ.1 x := by
  change infEmb τ (evInf F v (adAt v c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt v c) = c := by
    change (Pi.single v c : Ainf F) v = c
    exact Pi.single_eq_same v c
  rw [this, infEmb_tmul]

theorem piInf_adAt_ne {v w : InfinitePlace F} (h : v ≠ w) (τ : EmbOver E v) (c : w.Completion) (x : E) :
    piInf τ (adAt w c ⊗ₜ[F] x) = 0 := by
  change infEmb τ (evInf F v (adAt w c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt w c) = 0 := by
    change (Pi.single w c : Ainf F) v = 0
    exact Pi.single_eq_of_ne h c
  rw [this, TensorProduct.zero_tmul, map_zero]

theorem ext_symm_real {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t) =
      (t : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem smul_adAt_tmul (u : AF F) (hu : evI F u = 0) (w : InfinitePlace F) (c : w.Completion) (x : E) :
    u • (adAt w c ⊗ₜ[F] x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  rw [TensorProduct.smul_tmul', smul_eq_mul]
  have : u * adAt w c = 0 := by
    refine Prod.ext ?_ ?_
    · change u.1 * (adAt w c).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (adAt w c).2 = 0
      exact mul_eq_zero_of_right _ rfl
  rw [this, TensorProduct.zero_tmul]

theorem exists_at_inf_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ),
    ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  intro F E _ _ _ _ _ σ h τ z
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  have hξ : ∀ w, ∃ ξ : E, ((τ w).1 ξ).im ≠ 0 := fun w => by
    by_contra hc
    push_neg at hc
    exact IsTotallyComplex.complexEmbedding_not_isReal (τ w).1
      (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (hc x)))
  choose ξ hξ using hξ
  let s : InfinitePlace F → ℝ := fun w => (z w).im / ((τ w).1 (ξ w)).im
  let r : InfinitePlace F → ℝ := fun w => (z w).re - s w * ((τ w).1 (ξ w)).re
  let cR : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  refine ⟨∑ w, (adAt w (cR w (r w)) ⊗ₜ[F] (1 : E) + adAt w (cR w (s w)) ⊗ₜ[F] ξ w), ?_, fun v => ?_⟩
  · intro u hu
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_adAt_tmul u hu, smul_adAt_tmul u hu, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single v]
      · rw [map_add (f := _), piInf_adAt_same, piInf_adAt_same]
        simp only [cR, ext_symm_real, map_one, mul_one]
        have h0 := hξ v
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, r]
          ring
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add, zero_mul,
            add_zero, s]
          field_simp
      · intro w _ hw
        rw [map_add (f := _), piInf_adAt_ne (Ne.symm hw), piInf_adAt_ne (Ne.symm hw), add_zero]
      · intro hv; exact absurd (Finset.mem_univ v) hv

end GlobalTheory.PolRangeInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOverSubfieldEmbedding
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_over_subfield_embedding : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  first | (exact @GlobalTheory.exists_left_basis_through_algHom) | (exact GlobalTheory.exists_left_basis_through_algHom) | (intros; apply GlobalTheory.exists_left_basis_through_algHom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonEigenvectorRhoAdjoinRootEmbeddingStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m) (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i → ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧ ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  first | (exact @GlobalTheory.StabFin.rho_jM_common_eigvec) | (exact GlobalTheory.StabFin.rho_jM_common_eigvec) | (intros; apply GlobalTheory.StabFin.rho_jM_common_eigvec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjOfRelSimilitudePairsSameFormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_rel_similitude_pairs_same_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ), 0 < s → 0 < s' → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → P.Rel P' → ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧ g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  first | (exact @GlobalTheory.LKCx.ConjR.conj_of_rel) | (exact GlobalTheory.LKCx.ConjR.conj_of_rel) | (intros; apply GlobalTheory.LKCx.ConjR.conj_of_rel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRootsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧ (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧ G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  first | (exact @GlobalTheory.LKMid.psi_eigenbasis) | (exact GlobalTheory.LKMid.psi_eigenbasis) | (intros; apply GlobalTheory.LKMid.psi_eigenbasis  <;> assumption)
end

