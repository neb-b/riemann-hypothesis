module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Per.SESJumps

theorem isJumpV_iff_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  intro l _ P AI hT K LL T₀ T₁ T₂ ι π hS _ h₁ _ τ a
  obtain ⟨hi, hs, -, hex, -⟩ := hS
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hex x).symm
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h₁).1
  exact ((_root_.GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv
    hi hs hrk hDR).2.2 τ a).2.2

end GlobalTheory.Per.SESJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_GLint_iff_entries_cell {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} :
    x ∈ GLint (Fin n) O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem isOpen_intAway (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E} := by
  refine RestrictedProduct.isOpen_forall_imp_mem (fun v => ?_)
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem isOpen_US (S : Finset (HeightOneSpectrum (𝓞 E))) : IsOpen (US E n S : Set (GA E n)) := by
  set A := {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E}
  have e : (US E n S : Set (GA E n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, ((fun g : GA E n => ((g : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A ∩
        (fun g : GA E n => (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A) := by
    ext g
    simp only [SetLike.mem_coe, US, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, A, Set.mem_setOf_eq, GlobalTheory.LFun.KGL, mem_GLint_iff_entries_cell, ← map_inv]
    constructor
    · intro h i j
      exact ⟨fun v hv => (h v hv).1 i j, fun v hv => (h v hv).2 i j⟩
    · intro h v hv
      exact ⟨fun i j => (h i j).1 v hv, fun i j => (h i j).2 v hv⟩
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))

theorem isOpen_adelicUnipotentTimesIntegralOutsideSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  intro E _ _ n S
  have e : C0 E n S = ⋃ u ∈ (NA E n : Set (GA E n)), (fun k => u * k) '' (US E n S : Set (GA E n)) := by
    ext g
    simp only [C0, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
  rw [e]
  exact isOpen_biUnion fun u _ => isOpenMap_mul_left u _ (isOpen_US S)

end GlobalTheory.CellDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSSRepMapOfAbsIrrDistinct
section
noncomputable section

namespace GlobalTheory.ConstituentsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

open Polynomial Formalism.ConjugateSelfDual

def BrauerNesbitt : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹

section Rep

variable {k Γ : Type} [Field k] [Group Γ]

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

variable {D i}

end Loc

end GlobalTheory.ConstituentsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrime
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
open scoped Pointwise

namespace GlobalTheory.TypeSplit

theorem main : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  intro D k w hw
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

end GlobalTheory.TypeSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfFiniteProductComponents
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.ProdStable

theorem quot_pi_bij {P : Type} [CommRing P] {n : ℕ} {Ps : Fin n → Type} [∀ i, CommRing (Ps i)]
    (g : ∀ i, P →+* Ps i) (hg : Function.Bijective fun (x : P) (i : Fin n) => g i x)
    (J : Ideal P) (Ji : ∀ i, Ideal (Ps i)) (hle : ∀ i, J ≤ (Ji i).comap (g i))
    (hJ : ∀ i, J.map (g i) = Ji i) :
    Function.Bijective fun (x : P ⧸ J) (i : Fin n) => Ideal.quotientMap (Ji i) (g i) (hle i) x := by
  classical
  have hsurj : ∀ i, Function.Surjective (g i) := fun i y => by
    obtain ⟨a, ha⟩ := hg.2 (Pi.single (M := Ps) i y)
    exact ⟨a, by simpa using congrFun ha i⟩
  choose e he0 using fun i => hg.2 (Pi.single (M := Ps) i 1)
  have he : ∀ i j, g j (e i) = Pi.single (M := Ps) i 1 j := fun i j => congrFun (he0 i) j
  let F : (P ⧸ J) →+* ∀ i, Ps i ⧸ Ji i := Pi.ringHom fun i => Ideal.quotientMap (Ji i) (g i) (hle i)
  change Function.Bijective F
  refine ⟨(injective_iff_map_eq_zero F).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hb : ∀ i, ∃ b ∈ J, g i b = g i a := fun i => by
      have := congrFun hx i
      change Ideal.Quotient.mk (Ji i) (g i a) = 0 at this
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hJ i] at this
      exact (Ideal.mem_map_iff_of_surjective _ (hsurj i)).1 this
    choose b hbJ hbg using hb
    have ha : a = ∑ i, e i * b i := hg.1 <| funext fun j => by
      change g j a = g j (∑ i, e i * b i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single j]
      · rw [map_mul, he j j, Pi.single_eq_same, one_mul, hbg]
      · intro i _ hij
        rw [map_mul, he i j, Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [ha]
    exact J.sum_mem fun i _ => J.mul_mem_left _ (hbJ i)
  · choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    obtain ⟨a, ha⟩ := hg.2 z
    refine ⟨Ideal.Quotient.mk J a, funext fun i => ?_⟩
    change Ideal.Quotient.mk (Ji i) (g i a) = y i
    rw [show g i a = z i from congrFun ha i, hz]

theorem flat_of_pi {A P : Type} [CommRing A] [CommRing P] {n : ℕ} {Ps : Fin n → Type} [∀ i, CommRing (Ps i)]
    (f : A →+* P) (g : ∀ i, P →+* Ps i) (hg : Function.Bijective fun (x : P) (i : Fin n) => g i x)
    (hf : ∀ i, ((g i).comp f).Flat) : f.Flat := by
  classical
  let e : P ≃+* ∀ i, Ps i := RingEquiv.ofBijective (Pi.ringHom g) hg
  have hpi : (Pi.ringHom fun i => (g i).comp f).Flat := by
    letI : ∀ i, Algebra A (Ps i) := fun i => ((g i).comp f).toAlgebra
    haveI : ∀ i, Module.Flat A (Ps i) := fun i => RingHom.flat_algebraMap_iff.1 (hf i)
    haveI : Module.Flat A (Π₀ i, Ps i) := inferInstance
    haveI : Module.Flat A (∀ i, Ps i) :=
      Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A) (M := Ps)).symm
    exact RingHom.flat_algebraMap_iff.2 this
  have : f = (e.symm : (∀ i, Ps i) →+* P).comp (Pi.ringHom fun i => (g i).comp f) := by
    ext a
    apply e.injective
    simp [e]
    rfl
  rw [this]
  exact hpi.comp (RingHom.Flat.of_bijective e.symm.bijective)

theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {X Y Z : Obj l R} (g : Hom Y Z) (f : Hom X Y) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem adI_pow_map {l : ℕ} {R : Type} [CommRing R] {X Y : Obj l R} (f : Hom X Y)
    (hI : X.I.map f.f = Y.I) (m : ℕ) : (adI X ^ m).map f.f = adI Y ^ m := by
  rw [Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

theorem qmap_pi_bij {l : ℕ} {R : Type} [CommRing R] {n : ℕ} {C : Fin n → Obj l R} {Q : Obj l R}
    (π : ∀ i, Hom Q (C i)) (hbij : Function.Bijective fun (x : Q.A) (i : Fin n) => (π i).f x)
    (hI : ∀ i, Q.I.map (π i).f = (C i).I) (m : ℕ) :
    Function.Bijective fun (x : Q.A ⧸ adI Q ^ m) (i : Fin n) => qmap (π i) m x :=
  quot_pi_bij (fun i => (π i).f) hbij _ _ (fun i => adI_pow_le (π i) m) fun i => adI_pow_map (π i) (hI i) m

theorem prodStable : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R),
    (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∀ (Q : Obj l R) (π : ∀ i, Hom Q (C i)),
    Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) → ∀ (B : Obj l R) (h : Hom B Q),
    (∀ i, Stable ((π i).comp h)) → Stable h := by
  intro l _ R _ n C hC Q π hbij B h hs
  have hQI : ∀ i, Q.I.map (π i).f = (C i).I := fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q (C i) (π i)
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · exact flat_of_pi (qmap h m) (fun i => qmap (π i) m) (qmap_pi_bij π hbij hQI m)
      fun i => by rw [← qmap_comp]; exact (hs i).flat m
  · choose C' k' h' hpo using fun i => (hs i).po B' k
    have hC' : ∀ i, ∃ t, (C' i).I = Ideal.span {t} := fun i => by
      obtain ⟨t, ht⟩ := hC i
      exact ⟨(k' i).f t, by rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R _ _ (k' i), ht, Ideal.map_span, Set.image_singleton]⟩
    obtain ⟨Q', π', hbij', -, huniv⟩ := _root_.GlobalTheory.Prism.finite_product_oriented l R n C' hC'
    have hQ'I : ∀ i, Q'.I.map (π' i).f = (C' i).I := fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q' (C' i) (π' i)
    obtain ⟨K, hK⟩ := huniv Q fun i => (k' i).comp (π i)
    obtain ⟨H, hH⟩ := huniv B' h'
    have hinj : ∀ {X : Obj l R} (a b : Hom X Q'), (∀ i, (π' i).comp a = (π' i).comp b) → a = b :=
      fun a b hab => Hom.ext' (RingHom.ext fun x => hbij'.1 (funext fun i => congrArg (fun c => c.f x) (hab i)))
    refine ⟨Q', K, H, ⟨hinj _ _ fun i => ?_, fun m => ?_⟩⟩
    · calc (π' i).comp (K.comp h) = ((π' i).comp K).comp h := Hom.ext' rfl
        _ = (k' i).comp ((π i).comp h) := by rw [hK i]; exact Hom.ext' rfl
        _ = (h' i).comp k := (hpo i).comm
        _ = ((π' i).comp H).comp k := by rw [hH i]
        _ = (π' i).comp (H.comp k) := Hom.ext' rfl
    · refine _root_.GlobalTheory.isPushout_of_pi_components (qmap h m) (qmap k m) (qmap K m) (qmap H m) (fun i => qmap (π i) m)
        (fun i => qmap (π' i) m) (fun i => qmap (k' i) m) (fun i => qmap (h' i) m)
        (qmap_pi_bij π hbij hQI m) (qmap_pi_bij π' hbij' hQ'I m) (fun i => ?_) (fun i => ?_) (fun i => ?_)
      · rw [← qmap_comp, ← qmap_comp, hK i]
      · rw [← qmap_comp, hH i]
      · rw [← qmap_comp]; exact (hpo i).po m

end GlobalTheory.ProdStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsToricEltOfIsLamTie
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem isToricElt_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok →
    IsLamTie X Z → IsToricElt X ∧ ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ h
  refine ⟨fun i hi => ?_, fun i hi lam => ?_⟩
  · obtain ⟨hS, ι, hι, hl⟩ := h i hi
    refine ⟨ι, hι, fun lam s hs => ?_⟩
    obtain ⟨j, a, s', ⟨-, hs', hv⟩, u, hu, hQ⟩ := hl lam
    obtain rfl : s = s' := by
      have h1 := hs.1
      have h2 := hs'.1
      omega
    have h1 : 1 ≤ s := by exact_mod_cast hs.2.1
    exact ⟨_, inferInstance, phi D.host, Z.kap j a s, cond0 D.host Z.w0, Z.lam0 (X.l i) j a, u,
      _root_.GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum D Z hZ (X.l i) j a s h1 hs.2.2, hS, hv, hu, hQ⟩
  · obtain ⟨-, ι, -, hl⟩ := h i hi
    obtain ⟨j, a, s, ⟨-, hs, -⟩, -⟩ := hl lam
    exact ⟨s, hs⟩

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobEis

theorem factorial_pow_dvd (r : ℕ) : ∀ k : ℕ, r.factorial ^ k ∣ (k * r).factorial
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, add_mul, one_mul]
    exact (Nat.mul_dvd_mul_right (factorial_pow_dvd r k) _).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem factorial_pow_mul_dvd {l : ℕ} (hl : 1 ≤ l) : l.factorial ^ l * l ∣ (l * l).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h1 : (k + 1) * (k + 1) = (k * (k + 1) + k) + 1 := by ring
  have h3 := (Nat.mul_dvd_mul_right (factorial_pow_dvd (k + 1) k) k.factorial).trans
    (Nat.factorial_mul_factorial_dvd_factorial_add (k * (k + 1)) k)
  have h4 : (k + 1).factorial ^ (k + 1) * (k + 1) =
      (k + 1).factorial ^ k * k.factorial * (k * (k + 1) + k + 1) := by
    rw [Nat.factorial_succ k, pow_succ]; ring
  rw [h1, Nat.factorial_succ (k * (k + 1) + k), h4, mul_comm (k * (k + 1) + k + 1)]
  exact Nat.mul_dvd_mul_right h3 _

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_one_add {y z : Per.Acris l} {n : ℕ} (h : y ^ n = (l : Per.Acris l) * z) : IsUnit (1 + y) := by
  have := (GlobalTheory.MemLoc.acris_torsionFree_complete l).2
  have hJ : -(-y) ^ n ∈ Ideal.jacobson (⊥ : Ideal (Per.Acris l)) := by
    refine IsAdicComplete.le_jacobson_bot (Ideal.span {((l : ℕ) : Per.Acris l)}) (Ideal.mem_span_singleton.2 ⟨-((-1) ^ n * z), ?_⟩)
    rw [neg_pow, h]; ring
  have h1 := Ideal.mem_jacobson_bot.1 hJ 1
  rw [mul_one, neg_add_eq_sub] at h1
  have h2 := mul_neg_geom_sum (-y) n
  rw [sub_neg_eq_add] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ h1)

theorem isUnit_teich_pow_add {e : ℕ} (ϖ : PiSys l e) :
    IsUnit (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich l
  obtain ⟨d₂, hd₂⟩ := ϖ.exists_dpow_teich (l * l)
  obtain ⟨m, hm⟩ := factorial_pow_mul_dvd hl.out.one_lt.le
  have hm' : ((l * l).factorial : Per.Acris l) = (l.factorial : Per.Acris l) ^ l * l * m := by
    rw [hm]; push_cast; ring
  have h3 : ((l.factorial : Per.Acris l) * d) ^ l = ainfToAcris l ϖ.teich ^ (e * (l * l)) := by
    rw [hd, ← pow_mul, mul_assoc]
  have hdl : d ^ l = l * (m * d₂) := by
    refine sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero l l.factorial_ne_zero) ?_)
    push_cast
    linear_combination h3 - hd₂ + d₂ * hm'
  have hp : ((l.factorial : ℕ) : Per.Acris l) = l * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.out.ne_zero]; push_cast; ring
  have h1 : ainfToAcris l (ϖ.teich ^ (e * l) + l) = l * (1 + ((l - 1).factorial : Per.Acris l) * d) := by
    rw [map_add (f := _), map_pow, map_natCast, ← hd, hp]; ring
  have hy : (((l - 1).factorial : Per.Acris l) * d) ^ l =
      l * (((l - 1).factorial : Per.Acris l) ^ l * (m * d₂)) := by
    rw [mul_pow, hdl]; ring
  rw [h1, map_mul, map_natCast]
  exact (GlobalTheory.MemLoc.isUnit_l_Bcris l).mul ((isUnit_one_add hy).map _)

theorem isUnit_toB_frob_eis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ϖ : PiSys l e),
    IsUnit (toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)))) := by
  intro l _ a e _ _ O _ _ _ _ ϖ
  have hE : WittVector.frobenius (ϖ.ev a (eis l a e)) = ϖ.teich ^ (e * l) + l := by
    rw [← ϖ.ev_frobS a, eis, map_add (f := _), map_pow, frobS_X, map_natCast, map_add (f := _), map_pow, map_pow, PiSys.ev_X,
      map_natCast, ← pow_mul, mul_comm l e]
  have h : toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
    rw [frobOA_tmul, hE]; rfl
  rw [h]
  exact (isUnit_teich_pow_add ϖ).map _

end GlobalTheory.BKGal.FrobEis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

theorem kummer_mem_Fq_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  intro l _ a e _ _ ϖ he k hk
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  have hr : ∀ n, ϖ.ratio k n ^ e = 1 := fun n => by
    have hmem : ϖ.seq n ^ e ∈ ϖ.Kinf := IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix _ hmem,
      div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
    rfl
  have hK : ϖ.kummer k ^ e = 1 := Perfection.ext fun n => by
    erw [map_pow, map_one]
    change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
    rw [← map_pow, hr, map_one]
  have hmem : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← he, pow_succ, hK, one_mul]
  obtain ⟨z, hz⟩ : ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k := ⟨(⟨ϖ.kummer k, hmem⟩ : ↥(resSub l a)), rfl⟩
  refine ⟨z, Fq.val_injective l a ?_, hz.symm⟩
  rw [map_pow, map_one, hz, hK]

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CycBridge

theorem locChi_epsU : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Br.G D.nbr i w hw), Br.locChi D.nbr i w hw (epsU D.nd i) g = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :=
  fun D i w hw g => Units.ext (GlobalTheory.Survey.CrystallineCharacterRatio.locChi_eps D i w hw g)

end GlobalTheory.CycBridge
end

