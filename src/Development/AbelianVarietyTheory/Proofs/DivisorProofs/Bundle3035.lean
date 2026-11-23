module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomai
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GmAic

theorem pull_spMap_bijective (R : Type) [CommRing R] {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* A')) F n) := by
  have key : ∀ {B B' : Type} [CommRing B] [CommRing B'] (g : B ≃+* B') (x : H R (sp B') F n),
      pull R (spMap (g : B →+* B')) F n (pull R (spMap (g.symm : B' →+* B)) F n x) = x := by
    intro B B' _ _ g x
    rw [← pull_comp]
    have h : spMap (g : B →+* B') ≫ spMap (g.symm : B' →+* B) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Spec.map_comp]
      have h' : CommRingCat.ofHom (g.symm : B' →+* B) ≫ CommRingCat.ofHom (g : B →+* B') = 𝟙 _ := by
        ext y; simp
      rw [h', Spec.map_id, CategoryTheory.Functor.map_id]
    rw [h, pull_id]
  refine ⟨fun x y hxy => ?_, fun x => ⟨_, key e x⟩⟩
  have hx := key e.symm x
  have hy := key e.symm y
  simp only [RingEquiv.symm_symm] at hx hy
  rw [← hx, ← hy, hxy]

def laurentEquiv (hC3 : C3) (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T)
    (hq : IsUnit (q : T)) (n i : ℤ) :
    Ht q (sp (LaurentPolynomial T)) n i ≃+ Ht q (sp (LaurentPolynomial (FractionRing T))) n i := by
  haveI : IsScalarTower T (Polynomial T) (LaurentPolynomial T) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Polynomial.toLaurent_C]
      rfl
  haveI : Algebra.Etale (Polynomial T) (LaurentPolynomial T) :=
    Algebra.Etale.of_isLocalizationAway (Polynomial.X : Polynomial T)
  have h1 := hC3 q T hA hq (LaurentPolynomial T) i n
  let e : TensorProduct T (FractionRing T) (LaurentPolynomial T) ≃+* LaurentPolynomial (FractionRing T) :=
    (AddMonoidAlgebra.scalarTensorEquiv (M := ℤ) T (FractionRing T)).toRingEquiv
  exact (AddEquiv.ofBijective _ h1).trans (AddEquiv.ofBijective _ (pull_spMap_bijective _ e (tw q i) n))

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial T)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial T)) 1 i ≃+ ZMod q) := by
  intro q _ T _ _ _ hA hq n i
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by
    simpa using hq.map (algebraMap T (FractionRing T))
  obtain ⟨h2, _⟩ := GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed q (FractionRing T) hqK n i
  obtain ⟨_, ⟨e1⟩⟩ := GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed q (FractionRing T) hqK 1 i
  refine ⟨fun hn => ?_, ⟨(laurentEquiv GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq 1 i).trans e1⟩⟩
  haveI := h2 hn
  exact (laurentEquiv GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq n i).injective.subsingleton

end GlobalTheory.EtC.GmAic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanonBd

theorem prime_X {σ A : Type} [CommRing A] [IsDomain A] (i : σ) : Prime (MvPowerSeries.X i : MvPowerSeries σ A) := by
  classical
  have key : ∀ f : MvPowerSeries σ A, MvPowerSeries.X i ∣ f ↔ (1 : ℕ∞) ≤ f.weightedOrder (Pi.single i 1) := fun f => by
    have hw : ∀ d : σ →₀ ℕ, Finsupp.weight (Pi.single i 1 : σ → ℕ) d = d i := fun d => by
      rw [Finsupp.weight_single_one_apply]
    rw [MvPowerSeries.X_dvd_iff]
    refine ⟨fun h => ?_, fun h d hd => ?_⟩
    · exact MvPowerSeries.nat_le_weightedOrder _ (n := 1) fun d hd => h d (by rw [hw] at hd; omega)
    · exact MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (lt_of_lt_of_le (by rw [hw, hd]; simp) h)
  refine ⟨fun h => ?_, fun h => ?_, fun f g h => ?_⟩
  · simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  · simpa using h.map MvPowerSeries.constantCoeff
  · rw [key, MvPowerSeries.weightedOrder_mul] at h
    rw [key, key]
    by_contra hn
    simp only [not_or, not_le, Order.lt_one_iff] at hn
    simp [hn.1, hn.2] at h

theorem isRadical_span_prod_X {σ A : Type} [CommRing A] [IsDomain A] {m : ℕ} (v : Fin m → σ) (hv : Function.Injective v) :
    (Ideal.span {∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ A)}).IsRadical := by
  classical
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  refine GlobalTheory.RelParamRad.prod_dvd_of_forall_dvd m _ (fun i => prime_X (v i)) (fun i j hij => ?_) x
    fun i => (prime_X (v i)).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hn)
  by_contra hne
  have := MvPowerSeries.X_dvd_iff.1 hij (Finsupp.single (v j) 1)
    (Finsupp.single_eq_of_ne fun h => hne (hv h))
  simp [MvPowerSeries.coeff_X] at this

theorem mem_support_of_idlAlong_le {S : Scheme.{0}} (I : S.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (p : Sp R) (h : idlAlong I ξ ≤ p.asIdeal) : ξ p ∈ I.support := by
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    have eq_map {A : Type} [CommRing A] [IsLocalRing A] (ψ : Sp A ⟶ X)
        (U : X.affineOpens) (hle : ⊤ ≤ ψ ⁻¹ᵁ U.1) :
        idlAlong J ψ = (J.ideal U).map (ψ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of A)).hom).hom := by
      have hx : ψ (closedPoint A) ∈ U.1 := hle trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map χ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let lo := algebraMap R (Localization.AtPrime p.asIdeal)
  have e : (spMap lo ≫ ξ) (closedPoint (Localization.AtPrime p.asIdeal)) = ξ p := by
    change ξ (spMap lo (closedPoint _)) = ξ p
    congr 1
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  rw [← e]
  refine (mem_support_iff_stalkId I _).2 fun htop => ?_
  have h₁ : idlAlong I (spMap lo ≫ ξ) = ⊤ := by rw [idlAlong, htop, Ideal.map_top]
  rw [idlAlong_comp_local] at h₁
  have h₂ : (idlAlong I ξ).map lo ≤ maximalIdeal _ :=
    (Ideal.map_mono h).trans (Localization.AtPrime.map_eq_maximalIdeal).le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h₁ ▸ h₂))

theorem mem_range_of_away {X S : Scheme.{0}} [S.IsSeparated] (j : X ⟶ S) {R : Type} [CommRing R] [IsDomain R]
    (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ) (f : R) (yo : Sp (Localization.Away f) ⟶ X)
    (hyo : ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away f),
      g ≫ spMap (algebraMap R (Localization.Away f)) = jK R → g ≫ yo = y)
    (p : Sp R) (hp : f ∉ p.asIdeal) : ξ p ∈ Set.range j := by
  have hf : f ≠ 0 := fun h => hp (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hu : ∀ x : Submonoid.powers f, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R) (⟨x.1, hle x.2⟩ : nonZeroDivisors R)
  let lf : Localization.Away f →+* FractionRing R := IsLocalization.lift hu
  let lo := spMap (algebraMap R (Localization.Away f))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.Away f) := spMap lf
  have hκ : κ ≫ lo = jK R := by
    rw [← Spec.map_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.Away f) hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hξ : lo ≫ ξ = yo ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hyo κ hκ]
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ f]
    exact hp
  obtain ⟨q, hq⟩ := hq
  refine ⟨yo q, ?_⟩
  change (yo ≫ j) q = ξ p
  rw [← hξ, ← hq]
  rfl

theorem boundary_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧ ∃ a : Fin C.m → ℕ, (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns Z zs i OZ N d J S π j _ BD hP hS k _ m e C hT ξ hy
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    have eq_map {A : Type} [CommRing A] [IsLocalRing A] (ψ : Sp A ⟶ X)
        (U : X.affineOpens) (hle : ⊤ ≤ ψ ⁻¹ᵁ U.1) :
        idlAlong J ψ = (J.ideal U).map (ψ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of A)).hom).hom := by
      have hx : ψ (closedPoint A) ∈ U.1 := hle trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map χ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  have hEt := _root_.GlobalTheory.TautEtaleB.tautB_isEtaleCompletion Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨-, -, -, ⟨hd, hJ, -⟩, ⟨-, hproj, -, -, -, hπ, hBD, hval⟩, -⟩ := hP
  obtain ⟨hm, hs, ⟨yo, -, -, -, hyo⟩, -⟩ := hT.1
  haveI : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsProper (π ≫ zs) := by
    obtain ⟨n, lo, hlo, h⟩ := hproj
    have := isProper_str c.F n
    rw [← h]
    infer_instance
  haveI : S.IsSeparated := by
    constructor
    rw [← terminal.comp_from (π ≫ zs)]
    infer_instance

  haveI := GlobalTheory.PointStepCompare.projective_of_free E (X := C.P.D.toPre.X)
  have hF := hφ C.P.D.toPre.X C.rank
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hex : ∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i) := fun i => by
    obtain ⟨n, hn⟩ := hF.exists_nat (C.cone.mem i) (C.cone.nonneg i)
    have h0 := hF.pos _ (C.cone.mem i) (C.cone.nonneg i) (C.cone.linearIndependent.ne_zero i)
    rw [hn] at h0
    refine ⟨d * (l.M' * n), by have : 0 < n := by exact_mod_cast h0
                               positivity, ?_⟩
    rw [C.cone.evalZ_smul, hn]
    push_cast
    rfl
  choose a ha0 ha using hex
  have hprod : ∀ b : Fin C.m → ℕ, ∏ i, C.s i ^ b i = ∏ i, bdParam k m e i ^ b (Fin.cast hm.symm i) := fun b =>
    Fintype.prod_equiv (finCongr hm) _ _ fun i => by rw [hs]; rfl
  have hs0 : ∀ i, C.s i ≠ 0 := fun i => by rw [hs]; exact (prime_X _).ne_zero

  have hdiv : idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
    rw [hprod]
    refine GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR k m e _ _ fun W _ _ _ hW ψ hψ hψl => ?_
    rw [← hprod, ← idlAlong_comp_local]
    haveI : IsDiscreteValuationRing W := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible
      ((map_ne_zero_iff ψ hψ).2 (hs0 i)) hϖ
    have hκ : spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ jK _ = jK W ≫ spMap ψ :=
      (GlobalTheory.ArcPull.fracMap_sq hψ).symm.trans (Category.id_comp _)
    obtain ⟨t, tK, P, h₁, h₂, be, hbe, hmon, hev⟩ :=
      _root_.GlobalTheory.UChart.pull_trait Xo c φ _ ⟨hA, inferInstance⟩ C W hW ψ hψ hψl ϖ hϖ w hw _ hκ
    obtain ⟨n, hn, hI⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξ) _ (by rw [Category.assoc, hy, reassoc_of% hκ]) t tK h₁ h₂ P be hbe hmon
    have hn' : n = ∑ i, w i * a i := by
      apply Nat.cast_injective (R := ℝ)
      rw [hn, hev, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; ring
    rw [hI, hn', Ideal.span_singleton_eq_span_singleton, map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => by rw [map_pow, pow_mul]; exact (hw i).symm.pow_pow

  have hset : ∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal := fun p => by
    refine ⟨fun h hp => ?_, mem_range_of_away j ξ C.y hy _ yo hyo p⟩
    have h₁ : ξ p ∈ BD.idealSheaf.support := by
      refine mem_support_of_idlAlong_le _ ξ p ?_
      rw [hdiv, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_of_dvd _ (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => dvd_pow_self _ (ha0 i).ne') hp
    rw [hBD, Scheme.IdealSheafData.support_comap] at h₁
    rw [← hπ] at h
    exact hJ _ h₁ h
  refine ⟨hset, ?_, a, ha, hdiv⟩
  haveI := GlobalTheory.GenFan.essFiniteType_int_stalk c.F S (π ≫ zs) (ξ (closedPoint _))
  haveI := hA.1
  refine GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl S j.opensRange _ ξ _ ?_ (fun p => ?_)
    (GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ _ hA.2.2.2 hEt
      (GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ hEt))
  · simp only [hs]
    exact isRadical_span_prod_X (fun i => Sum.inl (Fin.cast hm i)) (Sum.inl_injective.comp (Fin.cast_injective hm))
  · rw [Scheme.Hom.coe_opensRange]
    exact hset p

end GlobalTheory.UCanonBd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∃ κ : K, ∀ p : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, DefOver k₀ (spMap ev ≫ p.left ≫ β) → ∃ c ∈ k₀,
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J =
        ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ p.left))⁻¹).val * toStk z (κ * c) := by
  first | exact @GlobalTheory.USep.EvG.ThetaVal.theta_values | exact GlobalTheory.USep.EvG.ThetaVal.theta_values | (intros; apply GlobalTheory.USep.EvG.ThetaVal.theta_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem yy_hom : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ CongMod (X₁.S.r * X₁.S.N) mu' mu)) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (GlobalTheory.TorusExt.equiv_iff hB p p').1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      exact ⟨𝔪.e₈.symm z, e'⟩
    · intro hc
      obtain ⟨w, hw⟩ := hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add (f := _)]
      rw [hw]
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add (f := _), hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.GSep.Labels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpecStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSquare_product_isFunction_on_spec : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen →
    ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    ∀ (τ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(D.c (χ + -χ)).left, (D.c χ).left, (D.c (-χ)).left, (D.c 0).left]
      ![-1, 1, 1, -1])), τ.IsGen →
    ∃ G : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b * D.c χ).left) z J ^ 2 *
          (val t r z J ^ 2 * val χt r z J ^ 2 * val D.sym (r ≫ (D.c χ).left) z J *
            (val τ r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  first | exact @GlobalTheory.IntPointFnSq.fn_of_theta_sq | exact GlobalTheory.IntPointFnSq.fn_of_theta_sq | (intros; apply GlobalTheory.IntPointFnSq.fn_of_theta_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSections_exhaust_of_generic_geometric : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (P : PolAV (Sp V)) (N : ℕ), 1 ≤ N → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → IntTerm.Exhausts P N b := by
  first | exact @GlobalTheory.Poinc.IntTerm.exhausts_of_generic | exact GlobalTheory.Poinc.IntTerm.exhausts_of_generic | (intros; apply GlobalTheory.Poinc.IntTerm.exhausts_of_generic <;> assumption)
end

