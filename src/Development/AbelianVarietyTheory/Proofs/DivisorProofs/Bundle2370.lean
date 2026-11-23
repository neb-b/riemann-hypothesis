module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.HypFlatBaseChange

theorem square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X X' : Scheme.{0}}
    {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap σ)
    {J : Type} [Preorder J] (U : J → X.affineOpens) (hU : Monotone U) (U' : J → X'.affineOpens)
    (hU' : Monotone U') (hle : ∀ i, (U' i).1 ≤ φ ⁻¹ᵁ (U i).1)
    (g : CoefMap σ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')) (θ : 𝟭 _ ⟶ g.G)
    (hg : ∀ T b, g.α T (mp (hU.functor.op ⋙ OAff s) (θ.app T) b) =
      GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), hle _⟩ b) (c : HH1 s) :
    pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op) (pullHH1 w c) =
      pullHyp1 g (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c) := by
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), hle i⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  have k := congrArg (pullHyp1 (CoefMap.restrict (OPair φ s') hp.functor.op)) (isPull1_pullHH1 w c)
  rw [← pullHyp1_comp, ← pullHyp1_comp] at k
  rw [← pullHyp1_comp]
  have k1 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairRes φ s').comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    (CoefMap.restrict (OAff s') hU'.functor.op) (𝟙 _) (fun T b ↦ mp_id (OAff s') _ b) (pullHH1 w c)
  have k2 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairPull w).comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    ((CoefMap.restrict (OAff s) hU.functor.op).comp g) (Functor.whiskerRight θ hU.functor.op)
    (fun T b ↦ hg T b) c
  exact k1.symm.trans (k.symm.trans k2)

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  intro R R' _ _ _ _ X X' s s' φ h hs hq
  obtain ⟨J, _, _, U, hU, hinf, hcov⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s hs hq
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  let U' : J → X'.affineOpens := fun i ↦ ⟨φ ⁻¹ᵁ (U i).1, (U i).2.preimage φ⟩
  have hU' : Monotone U' := fun i j hij x hx ↦ hU hij hx
  have hinf' : ∀ i j, (U' (i ⊓ j)).1 = (U' i).1 ⊓ (U' j).1 := fun i j ↦ by
    change φ ⁻¹ᵁ (U (i ⊓ j)).1 = _
    rw [hinf]; rfl
  have hcov' : ⨆ i, (U' i).1 = ⊤ := by
    change ⨆ i, φ ⁻¹ᵁ (U i).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), le_rfl⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  haveI : Finite Jᵒᵖ := Finite.of_equiv J Opposite.equivToOpposite
  haveI : ∀ T T' : Jᵒᵖ, Finite (T ⟶ T') := fun T T' ↦
    Finite.of_injective (β := T'.unop ⟶ T.unop) Quiver.Hom.unop Quiver.Hom.unop_inj
  have hb := _root_.GlobalTheory.liftSemi_pullHyp1_bijective_of_finite R R' Jᵒᵖ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')
    (fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b)
    (fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun T f hf ↦ GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h ⟨(U' T.unop, U T.unop), le_rfl⟩ rfl f hf)
  have hsq := fun c ↦ square h.w U hU U' hU' (fun _ ↦ le_rfl)
    ⟨𝟭 _, fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩,
      fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b,
      fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩⟩ (𝟙 _)
    (fun T b ↦ congrArg (GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
      (mp_id (hU.functor.op ⋙ OAff s) T b)) c
  exact (GlobalTheory.Div.BaseChangeIso.main R R' (HH1 s) (Hyp1 (hU.functor.op ⋙ OAff s)) (HH1 s')
    (Hyp1 (hU'.functor.op ⋙ OAff s')) (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op))
    (pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op)) (pullHH1 h.w) _
    (_root_.GlobalTheory.CoverHyp.restrict_bijective R X s J U hU hinf hcov) (_root_.GlobalTheory.CoverHyp.restrict_bijective R' X' s' J U' hU' hinf' hcov') hsq).2 hb

end GlobalTheory.Div.HypFlatBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfIzumiSmallValueIdealMapLeSpan
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
open GlobalTheory.Izumi

noncomputable section
namespace GlobalTheory.Izumi

theorem algebraMap_completion_injective : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A], Function.Injective (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  intro A _ _ _
  have h : IsHausdorff (maximalIdeal A) A := inferInstance
  intro a b hab
  exact AdicCompletion.of_injective (maximalIdeal A) A (by simpa [AdicCompletion.algebraMap_apply] using hab)

theorem exists_sub_algebraMap_mem_maximalIdeal_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (b : AdicCompletion (maximalIdeal A) A), ∃ a : A, b - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  intro A _ _ _ b
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) 1
  have hψ : ∀ r : A, ψ (algebraMap A (AdicCompletion (maximalIdeal A) A) r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
  refine ⟨a, ?_⟩
  by_contra hn
  have hu : IsUnit (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hn
  have h0 : ψ (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0 := by
    rw [map_sub, hψ, ha, sub_self]
  have h1 := hu.map ψ
  rw [h0] at h1
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ 1) := by
    rw [pow_one]
    exact Ideal.Quotient.nontrivial_iff.2 (maximalIdeal.isMaximal A).ne_top
  exact not_isUnit_zero h1

theorem norm_le_of_mem_iInf_map_smallIdeal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (U : M.Z.Opens) (x : M.Z) (f : Ω) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ∀ ψ : AdicCompletion (maximalIdeal (M.O x)) (M.O x) →+* PadicAlgCl p, (∀ g, ‖ψ g‖ ≤ 1) → (∀ a : M.O x, ψ (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) a) = M.val (gPt p ≫ y) a) → ∀ G ∈ ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))), ‖ψ G‖ ≤ ‖M.val (gPt p ≫ y) f‖ := by
  intro o Ω _ _ _ _ M U x f p _ y hy ψ hψ1 hψv G hG
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  have hadd : ∀ a b : M.O x, ‖M.val (gPt p ≫ y) ((a + b : M.O x) : Ω)‖ ≤
      max ‖M.val (gPt p ≫ y) (a : Ω)‖ ‖M.val (gPt p ≫ y) (b : Ω)‖ := norm_val_add_le M hy
  have hmul : ∀ c a : M.O x, ‖M.val (gPt p ≫ y) ((c * a : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (a : Ω)‖ :=
    norm_val_mul_le M hy
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (maximalIdeal (M.O x)) : (maximalIdeal (M.O x)).FG)
  set ρ : ℝ := ((S.sup fun g => ‖M.val (gPt p ≫ y) (g : Ω)‖₊ : NNReal) : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := NNReal.coe_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρdef, ← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]
    intro g hg
    have hgm : g ∈ maximalIdeal (M.O x) := hS ▸ Submodule.subset_span hg
    have h1 := (hy.norm_val_lt_one_iff g.2).2 (by simpa using hgm)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using h1
  have hρ : ∀ h ∈ maximalIdeal (M.O x), ‖M.val (gPt p ≫ y) (h : Ω)‖ ≤ ρ := by
    intro h hh
    rw [← hS] at hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      rw [hρdef, ← coe_nnnorm, NNReal.coe_le_coe]
      exact Finset.le_sup (f := fun g : M.O x => ‖M.val (gPt p ≫ y) (g : Ω)‖₊) hg
    | zero =>
      have h0 : ((0 : M.O x) : Ω) = 0 := rfl
      rw [h0, RatModel.val_zero, norm_zero]
      exact hρ0
    | add a b _ _ ha hb => exact (hadd a b).trans (max_le ha hb)
    | smul c a _ ha => exact (hmul c a).trans ha
  have hnu : ∀ h, NonUnitAt M x h → ∀ hO : h ∈ M.O x, (⟨h, hO⟩ : M.O x) ∈ maximalIdeal (M.O x) := by
    intro h hh hO
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rcases hh.2 with h0 | hinv
    · subst h0
      have : (⟨0, hO⟩ : M.O x) = 0 := rfl
      rw [this] at hu
      exact not_isUnit_zero hu
    · obtain ⟨w, hw⟩ := hu.exists_right_inv
      have e : h * (w : Ω) = 1 := congrArg Subtype.val hw
      apply hinv
      rw [← eq_inv_of_mul_eq_one_right e]
      exact w.2
  have hN : ∀ N, ∀ g ∈ (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))),
      ‖ψ g‖ ≤ max ‖M.val (gPt p ≫ y) f‖ (ρ ^ N) := by
    intro N g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      rw [hψv]
      rcases (mem_smallIdeal.1 hk) p y hy with h | ⟨h, hh, hle⟩
      · exact h.trans (le_max_left _ _)
      · refine le_max_of_le_right (hle.trans ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hρ _ (hnu h hh hh.1)) N
    | zero => rw [map_zero, norm_zero]; exact le_max_of_le_right (pow_nonneg hρ0 N)
    | add a b _ _ ha hb =>
      set_option synthInstance.maxHeartbeats 200000 in
        rw [map_add ψ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul c a _ ha =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψ1 c)).trans ha
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < ‖ψ G‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  obtain ⟨N, hNlt⟩ := exists_pow_lt_of_lt_one hpos hρ1
  have h1 := hN N G (Submodule.mem_iInf _ |>.1 hG N)
  rcases le_max_iff.1 h1 with h2 | h2
  · exact absurd h2 (not_le.2 hlt)
  · exact absurd h2 (not_le.2 hNlt)


set_option maxHeartbeats 800000 in
theorem iInf_map_smallIdeal_le_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (f : Ω) (hf : f ∈ M.O x), f ≠ 0 → ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))) ≤ Ideal.span {algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) ⟨f, hf⟩} := by
  intro o Ω _ _ _ _ M hN U hU x hx f hf hf0
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  haveI : IsIntegrallyClosed (M.O x) := RatModel.isIntegrallyClosed_O hN x
  haveI : CharZero (M.O x) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  haveI : Algebra.EssFiniteType ℤ (M.O x) := _root_.GlobalTheory.Izumi.essFiniteType_int_O o Ω M x
  haveI : Finite (ResidueField (M.O x)) := _root_.GlobalTheory.ResFin.finite_residueField_O o Ω M x hx
  set A := M.O x with hA
  set R := AdicCompletion (maximalIdeal A) A with hR
  set φ := algebraMap A R with hφ
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed A
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  have hinj : Function.Injective φ := algebraMap_completion_injective A
  intro G hG
  by_contra hGf
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding o Ω M U hU x
  obtain ⟨B, _, _, _, _, ι, hιinj, hιloc, hιres, u, hu, hfu⟩ := _root_.GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span R (φ ⟨f, hf⟩) G hGf
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hGf (Submodule.zero_mem _)
  haveI : CharZero B := ⟨fun a b h => by
    have h1 : ι (φ (a : A)) = ι (φ (b : A)) := by simpa using h
    have h2 := hinj (hιinj h1)
    exact_mod_cast h2⟩
  haveI : Finite (ResidueField B) := by
    let g : A → ResidueField B := fun a => residue B (ι (φ a))
    have hg : Function.Surjective g := by
      intro c
      obtain ⟨b, rfl⟩ := residue_surjective c
      obtain ⟨r, hr⟩ := hιres b
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal_completion A r
      refine ⟨a, ?_⟩
      have h1 : ι r - ι (φ a) ∈ maximalIdeal B := by
        rw [← map_sub]
        exact map_nonunit ι _ ha
      show residue B (ι (φ a)) = residue B b
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      have := Ideal.add_mem _ h1 hr
      have e : ι (φ a) - b = -((ι r - ι (φ a)) + (b - ι r)) := by ring
      rw [e]
      exact (Ideal.neg_mem_iff _).2 this
    have hker : ∀ a a' : A, a - a' ∈ maximalIdeal A → g a = g a' := by
      intro a a' h
      show residue B _ = residue B _
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, ← map_sub]
      refine map_nonunit ι _ (map_nonunit φ _ h)
    let g' : ResidueField A → ResidueField B := fun c => g (Classical.choose (residue_surjective c))
    refine Finite.of_surjective g' fun c => ?_
    obtain ⟨a, rfl⟩ := hg c
    refine ⟨residue A a, hker _ _ ?_⟩
    rw [← residue_eq_zero_iff, map_sub, Classical.choose_spec (residue_surjective (residue A a)), sub_self]
  have hh : ι (G * φ s) ≠ 0 := by
    rw [Ne, ← map_zero ι]
    intro h
    exact mul_ne_zero hG0 ((map_ne_zero_iff φ hinj).2 hs0) (hιinj h)
  obtain ⟨p, hp, χ, hχ1, hχm, hχh⟩ := _root_.GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero B inferInstance (ι (G * φ s)) hh
  set ψ : R →+* PadicAlgCl p := χ.comp ι with hψ
  have hψ1 : ∀ g, ‖ψ g‖ ≤ 1 := fun g => hχ1 _
  have hψG : ψ G ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hψs : ψ (φ s) ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hlt : ‖ψ (φ ⟨f, hf⟩)‖ < ‖ψ G‖ := by
    have e : ψ (φ ⟨f, hf⟩) = ψ G * χ u := by
      simp only [hψ, RingHom.comp_apply, hfu, map_mul]
    rw [e, norm_mul]
    have h1 : ‖χ u‖ < 1 := hχm u hu
    have h2 : 0 < ‖ψ G‖ := norm_pos_iff.2 hψG
    nlinarith [norm_nonneg (χ u)]
  let χ0 : A →+* OO p := (ψ.comp φ).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hψ1 _)
  have hloc : IsLocalHom χ0 := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := hna
    have h1 : ι (φ a) ∈ maximalIdeal B := map_nonunit ι _ (map_nonunit φ _ hm)
    have e : ((χ0 a : OO p) : PadicAlgCl p) = χ (ι (φ a)) := rfl
    have h2 : ‖((χ0 a : OO p) : PadicAlgCl p)‖ < 1 := by rw [e]; exact hχm _ h1
    exact (not_isUnit_OO_iff (χ0 a)).2 h2 ha
  have hχ0s : χ0 s ≠ 0 := fun h => hψs (congrArg Subtype.val h)
  obtain ⟨y, hy, hval⟩ := hs p χ0 hloc hχ0s
  have hb := norm_le_of_mem_iInf_map_smallIdeal o Ω M U x f p y hy ψ hψ1 (fun a => (hval a).symm) G hG
  have hf' := hval ⟨f, hf⟩
  simp only at hf'
  rw [hf'] at hb
  exact absurd hb (not_le.2 hlt)

end GlobalTheory.Izumi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailRest
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecsDesc

theorem assemble (hE : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) (hN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F) (hT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C
  obtain ⟨k₀, hk₀⟩ := hN R hR D C
  have hn : 1 < C.n := C.n_prime.one_lt
  have part1 : ∀ j ≥ k₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j),
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    intro j hj
    obtain ⟨Φ, hΦ⟩ := hE R hR D C j
    exact hk₀ (C.n ^ j) (hj.trans (Nat.lt_pow_self hn).le) Φ hΦ
  refine ⟨⟨k₀, part1⟩, fun F₁ => ?_⟩
  have key : ∀ k, k = C.n ^ (k₀ * 2) → ∃ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k,
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    rintro k rfl
    exact part1 _ (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨Φ, hΦ⟩ := key ((C.n ^ k₀) ^ 2) (pow_mul _ _ _).symm
  exact hT R hR D C (C.n ^ k₀) (C.n_odd.pow) Φ hΦ F₁

end GlobalTheory.Mum.SecsDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValue
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section Val

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem sec_sub_id_eq_val (E : SqExt R) {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B))
    (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (h : spMap ((E.π : E.C →+* E.B).comp (AlgHom.id R E.C : E.C →+* E.C)) ≫ y = x) (f : Z1 (O (dp0 R) s)) :
    ev f (E.secHom hx E.i E.π_i) - ev f (Thick.trivHom (hx := hy) (T := E.thick x hx) (AlgHom.id R E.C) h) =
      E.val y hy f := by
  subst h
  rfl

theorem val_congr (E : SqExt R) {y y' : Sp E.C ⟶ X} (e : y = y') (hy : y ≫ s = spMap (algebraMap R E.C))
    (hy' : y' ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) : E.val y hy f = E.val y' hy' f := by
  subst e
  rfl

end Val

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem ev_sec_sub_ev_tan_eq_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v)
    (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) :
    ev f P.sec - ev f (P.tan hv) = (SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f :=
  sec_sub_id_eq_val (SqExt.ofModule K P.B P.B) P.w (P.trx v) (P.tr v).w ((P.isTransl_trx v).red hv) f

theorem dualMap_id (B : Type) [CommRing B] : dualMap (RingHom.id B) = RingHom.id (DualNumber B) :=
  RingHom.ext fun c ↦ by ext <;> simp [dualMap]

@[reducible] def Pt.origin (A : Over (Sp K)) [GrpObj A] : GPt A where
  B := K
  x := η[A].left
  w := by
    rw [Category.comp_id, Over.w η[A]]
    exact (Cris.spMap_id K).symm

theorem isTransl_origin (v : epsR K ⟶ A) : IsTransl (algebraMap K K) η[A].left v v.left := by
  refine ⟨1, Over.homMk (spMap (dualMap (algebraMap K K)) ≫ v.left) (by
      rw [Category.assoc, Over.w v]
      change spMap _ ≫ spMap _ = spMap _
      rw [← Cris.spMap_comp, dualMap_comp_algebraMap]), rfl, rfl, ?_⟩
  rw [_root_.one_mul]
  change spMap (dualMap (RingHom.id K)) ≫ v.left = v.left
  rw [dualMap_id, Cris.spMap_id, Category.id_comp]

theorem origin_trx (v : epsR K ⟶ A) : (Pt.origin A).trx v = v.left :=
  ((Pt.origin A).isTransl_trx v).unique (isTransl_origin v)

end GlobalTheory.CechKS

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def tanFn (v : epsR K ⟶ A) (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ ((SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f).snd

theorem isNat_tanFn (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) : IsNat ⊤ (tanFn v ω.1) := by
  intro P Q φ _
  have := (SqExt.ofModule K P.B P.B).val_map (SqExt.ofModule K Q.B Q.B) (dualAlg φ.ρ) φ.ρ
    (fun c ↦ (fst_dualAlg φ.ρ c).symm) (fun b ↦ by ext <;> simp) (P.trx v) (P.tr v).w (Q.trx v) (Q.tr v).w
    (φ.tr v).pt ω
  simp only [tanFn]
  rw [this, snd_dualAlg]

theorem tanFn_eq (hA : IsAbelianScheme A) (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A) :
    tanFn v ω.1 P = algebraMap K P.B (tanVal v ω) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ ⊤) ⊤ (fun _ ↦ le_rfl)
    (le_iSup_of_le () le_rfl) (tanFn v ω.1) (fun _ ↦ isNat_tanFn v ω)
  obtain ⟨g₀, rfl⟩ := (GlobalTheory.globalFns_holds (Sp K) A hA).2 g
  have key : ∀ Q : GPt A, tanFn v ω.1 Q = algebraMap K Q.B (valR (𝟙 (Sp K)) ⊤ g₀) := by
    intro Q
    rw [hg () Q (fun _ _ ↦ trivial)]
    have e1 : valR Q.x ⊤ (A.hom.appTop.hom g₀) = valR (Q.x ≫ A.hom) ⊤ g₀ := by
      rw [GlobalTheory.Points.valR_comp Q.x A.hom ⊤ g₀]; rfl
    have e2 : Q.x ≫ A.hom = spMap (algebraMap K Q.B) ≫ 𝟙 (Sp K) :=
      (Category.comp_id (Q.x ≫ A.hom)).symm.trans ((Category.assoc _ _ _).trans (Q.w.trans (Category.comp_id _).symm))
    rw [e1, e2, GlobalTheory.Points.valR_spMap_comp _ _ _ (GlobalTheory.Points.le_preimage_top _)]
  have h0 : tanFn v ω.1 (Pt.origin A) = tanVal v ω := by
    simp only [tanFn]
    rw [tanVal_apply]
    exact congrArg TrivSqZeroExt.snd (val_congr (SqExt.dual K) (origin_trx v) _ _ ω.1)
  rw [key, ← h0, key]
  rfl

theorem ev_sec_sub_ev_tan : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A),
    ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  intro K _ A _ hA v hv ω P
  rw [ev_sec_sub_ev_tan_eq_val P hv ω.1]
  ext
  · rw [TrivSqZeroExt.fst_inr]; exact SqExt.π_val (SqExt.ofModule K P.B P.B) _ _ ω
  · exact tanFn_eq hA v ω P

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SemiAbFibre

theorem irreducibleSpace_fibre : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  intro T G _ hG Ω _ x
  have := hG.smooth
  have := hG.geomConnected
  have h : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral (pullback G.hom x : Scheme.{0}) :=
    h.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom x)
  infer_instance

end GlobalTheory.SemiAbFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExponentialOfSemiAbelianFibre_linearChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (M : Matrix (Fin g) (Fin g) ℂ), IsUnit M.det → IsHolTo Set.univ (fun z => (e z).left) → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y e → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y (fun w => e (M *ᵥ w)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec | exact GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec <;> assumption)
end

