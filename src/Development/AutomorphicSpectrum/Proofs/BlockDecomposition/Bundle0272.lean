module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.MemVan

variable {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)

def KilledIn (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) : Prop :=
  ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf

theorem killedIn_zero (n : ℕ) : KilledIn φ n 0 := by
  unfold KilledIn KillsForm
  refine ⟨isHomogeneous_zero _ _ _, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_zero, map_zero]

variable {φ}

theorem KilledIn.add {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R} (hf : KilledIn φ n f)
    (hg : KilledIn φ n g) : KilledIn φ n (f + g) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  unfold KillsForm at hf2 hg2
  unfold KilledIn KillsForm
  refine ⟨hf1.add hg1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_add hf1 hg1, map_add (f := _), hf2 k, hg2 k, add_zero]

theorem KilledIn.mul {d m : ℕ} {a f : MvPolynomial (Fin (N + 1)) R} (ha : a.IsHomogeneous d)
    (hf : KilledIn φ m f) : KilledIn φ (d + m) (a * f) := by
  obtain ⟨hf1, hf2⟩ := hf
  unfold KillsForm at hf2
  unfold KilledIn KillsForm
  refine ⟨ha.mul hf1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_mul ha hf1, map_mul, hf2 k, mul_zero]

theorem KilledIn.sum {ι : Type*} (s : Finset ι) {n : ℕ} (g : ι → MvPolynomial (Fin (N + 1)) R)
    (hg : ∀ i ∈ s, KilledIn φ n (g i)) : KilledIn φ n (∑ i ∈ s, g i) := by
  exact Finset.sum_induction g (KilledIn φ n) (fun a b ha hb => ha.add hb) (killedIn_zero φ n) hg

theorem killedIn_component_mul_of_homog {d : ℕ} {a h : MvPolynomial (Fin (N + 1)) R}
    (ha : a.IsHomogeneous d) (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ m ∈ Finset.range (h.totalDegree + 1), a * homogeneousComponent m h := by
    rw [← Finset.mul_sum, sum_homogeneousComponent]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine KilledIn.sum _ _ fun m _ => ?_
  rw [homogeneousComponent_of_mem
    ((mem_homogeneousSubmodule _ _).2 (ha.mul (homogeneousComponent_isHomogeneous m h)))]
  split_ifs with hnm
  · subst hnm
    exact KilledIn.mul ha (hh m)
  · exact killedIn_zero φ n

theorem killedIn_component_mul (a : MvPolynomial (Fin (N + 1)) R)
    {h : MvPolynomial (Fin (N + 1)) R} (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ k ∈ Finset.range (a.totalDegree + 1), homogeneousComponent k a * h := by
    rw [← Finset.sum_mul, sum_homogeneousComponent]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  exact KilledIn.sum _ _ fun k _ =>
    killedIn_component_mul_of_homog (homogeneousComponent_isHomogeneous k a) hh n

theorem killedIn_component_of_mem {h : MvPolynomial (Fin (N + 1)) R} (hh : h ∈ vanIdeal φ) :
    ∀ n, KilledIn φ n (homogeneousComponent n h) := by
  unfold vanIdeal Ideal.span at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, hk⟩ := hx
    intro n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hm)]
    split_ifs with hnm
    · subst hnm
      exact ⟨hm, hk⟩
    · exact killedIn_zero φ n
  | zero =>
    intro n
    rw [map_zero]
    exact killedIn_zero φ n
  | add x y _ _ ihx ihy =>
    intro n
    rw [map_add (f := _)]
    exact (ihx n).add (ihy n)
  | smul a x _ ih =>
    intro n
    rw [smul_eq_mul]
    exact killedIn_component_mul a ih n

end GlobalTheory.CompanionTheory.GE.MemVan

namespace GlobalTheory.CompanionTheory.GE

theorem mem_vanIdeal_iff_killsForm {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}}
    (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  constructor
  · intro hmem
    have h1 := MemVan.killedIn_component_of_mem hmem n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf), if_pos rfl] at h1
    obtain ⟨_, hk⟩ := h1
    exact hk
  · intro hk
    refine Ideal.subset_span ?_
    exact ⟨n, hf, hk⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.Mass

theorem anisotropic_binary_one_vector_formula : Prop1 → Simil → Hasse → Cnt → E1 := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ hA T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := _root_.GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 2 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) = 0
  · rw [(_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hcm d b 1 2 _ c _ _).2.1 hc h0]
    exact (_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hcm d b 1 2 0 1 _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0 h0.1
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 := by
        by_contra hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ' hz)
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hcm d b 1 2 0 c _ _).2.2 hc'.1 hc'.2.1 (Or.inl hz)
  have h1 : c = 1 := hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm c hall
  exact h1 ▸ hc

end GlobalTheory.CompanionTheory.Mass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PadicIntMemSub
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCZp

theorem padicInt_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) (z : ℤ_[l]) :
    Lat.pk l k (algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))) ∈
      Lat.sub (Lat.fk l k) (xi0 l) l M := by
  have h1 : algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z) :=
    ((algClToBdR l).commutes (z : ℚ_[l])).trans
      (IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l z)
  rw [h1]
  exact Subring.subset_closure (Or.inl ⟨IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z, rfl⟩)

end GlobalTheory.CompanionTheory.LatCZp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.PolyTfCon

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

section Thickening

variable (T : Thick (nlFun γ 0 X q κ)) {l s : ℕ} (hT : TF l s T)


include hT in
theorem tr_facts : fil (trD T s) s = ⊥ ∧
    (∀ (r : ℕ) (x : trB T s), (l : trB T s) * x ∈ fil (trD T s) r → x ∈ fil (trD T s) r) ∧
    IsNilpotent (trJ T s) :=
  GlobalTheory.CompanionTheory.SiteTr.tr_tf T.δ l s (trD T s) (trD_spec T s).1 hT.1 hT.2

abbrev pT : Thick (nlFun γ 0 X q κ) :=
  polyTr T s ⟨fun h => absurd rfl h, fun _ => (tr_facts T hT).2.2⟩

abbrev jT : T ⟶ pT T hT := homOf _ _ _ _ _ _ _

theorem pT_tf : TF l s (pT T hT) := ⟨(tr_facts T hT).1, (tr_facts T hT).2.1⟩

abbrev xT : trB T s := Ideal.Quotient.mk (trI T s) ((pq T.B).e 1)

theorem e_mem (B : Type) [CommRing B] (J : Ideal B) : (pq B).e 1 ∈ (pq B).ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem xT_mem : xT (s := s) T ∈ trJ T s := Ideal.mem_map_of_mem _ (e_mem _ _)

theorem sum_eq (b : ℕ →₀ T.B) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) =
      Ideal.Quotient.mk (trI T s) (b.sum fun k c => algebraMap T.B (pq T.B).P c * (eta T.δ).dpow k ((pq T.B).e 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, (trD_spec T s).1.dpow_comp _ (e_mem _ _)]
  rfl

theorem toNat_sub (r : ℤ) (k : ℕ) : (r - k).toNat = r.toNat - k := by omega

theorem fil_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈ fil (trD T s) r.toNat ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) 0).1

theorem std_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) (c : R) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈
        fil (trD T s) r.toNat ⊔ Ideal.span {Ideal.Quotient.mk (trI T s) (algebraMap T.B (pq T.B).P (T.i c))} ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat ⊔ Ideal.span {T.i c} := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) (T.i c)).2

theorem univ_tr {T' : Thick (nlFun γ 0 X q κ)} (hT' : T'.pdPow s = ⊥) (φ : T ⟶ T') (x : T'.B) (hx : x ∈ T'.J) :
    ∃! ψ : pT T hT ⟶ T', jT T hT ≫ ψ = φ ∧ ψ.φ (xT (s := s) T) = x := by
  obtain ⟨F, ⟨hF1, hF2, hF3⟩, hFu⟩ := GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal T.δ T'.δ φ.φ φ.dp x hx
  have hk : trI T s ≤ RingHom.ker F := by
    intro z hz
    have h1 : F z ∈ fil T'.δ (max s 1) := FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le _ _ F hF3 _ (Ideal.mem_map_of_mem F hz)
    have h2 : fil T'.δ (max s 1) ≤ fil T'.δ s := GlobalTheory.Cris.ExpBij.dpFil_anti T'.δ (le_max_left _ _)
    have h3 : F z ∈ T'.pdPow s := h2 h1
    rw [hT'] at h3
    exact h3
  let g : trB T s →+* T'.B := Ideal.Quotient.lift (trI T s) F fun a ha => hk ha
  have hgF : g.comp (Ideal.Quotient.mk (trI T s)) = F := by
    refine RingHom.ext fun z => ?_
    exact Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha
  have hg : g.comp (trF T s) = φ.φ := by
    rw [← RingHom.comp_assoc, hgF, hF1]
  have hdp : IsDPMorphism (trD T s) T'.δ g := (trD_spec T s).2 _ _ _ g (by rw [hgF]; exact hF3)
  have hle : trJ T s ≤ T'.J.comap g := Ideal.map_le_iff_le_comap.1 hdp.1
  refine ⟨descOf φ g hg hdp hle, ⟨hom_ext hg, (Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha).trans hF2⟩, ?_⟩
  rintro ψ ⟨h1, h2⟩
  refine hom_ext ?_
  change ψ.φ = g
  have e := hFu (ψ.φ.comp (Ideal.Quotient.mk (trI T s))) ⟨?_, h2, ?_⟩
  · refine Ideal.Quotient.ringHom_ext ?_
    rw [e, hgF]
  · have := congrArg Thick.Hom.φ h1
    exact this
  · exact IsDPMorphism.comp _ ψ.dp (trD_spec T s).1

end Thickening

section Site

variable (l s : ℕ) (𝒱 : Set X.Opens)

abbrev Qc : ObjectProperty (Thick (nlFun γ 0 X q κ)) := St (TF l s) 𝒱

variable {l s 𝒱}

theorem pT_mem (T : (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱).FullSubcategory) : Qc l s 𝒱 (pT T.obj T.property.1) := by
  obtain ⟨V, hV, h⟩ := T.property.2
  exact ⟨pT_tf _ _, V, hV, inU_hom (jT T.obj T.property.1) h⟩

variable (l s 𝒱)

def polyQ : Poly (sP (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱)) where
  P T := ⟨pT T.obj T.property.1, pT_mem T⟩
  j T := ObjectProperty.homMk (jT T.obj T.property.1)
  X T := xT (s := s) T.obj
  X_mem T := xT_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_tr T.obj T.property.1 T'.property.1.1 φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (show trB T.obj s from z)
    obtain ⟨b, rfl⟩ := GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow T.obj.δ w
    exact ⟨b, (sum_eq T.obj b).symm⟩

theorem crit_fil (r : ℤ) (hr : r ≤ s) : (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (sFil _) r :=
  fun T b => fil_coeff T.obj b r hr

theorem crit_std (r : ℤ) (hr : r ≤ s) (c : R) :
    (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (fun r => stdI _ (some r) c) r :=
  fun T b => std_coeff T.obj b r hr c

end Site

theorem polyTf : KH.PolyTf := by
  intro O R _ _ I γ X q κ l s 𝒱
  exact ⟨polyQ l s 𝒱, fun r hr => ⟨crit_fil l s 𝒱 r hr, crit_std l s 𝒱 r hr⟩⟩

end GlobalTheory.CompanionTheory.PolyTfCon
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNorm
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.DeligneRibet

theorem absNorm_not_dvd_of_sup_span_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F),
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  intro F _ _ l hl 𝔟 h hdvd
  have h1 : (1 : 𝓞 F) ∈ 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  by_cases h𝔟 : 𝔟 = ⊥
  · subst h𝔟
    rw [bot_sup_eq] at h
    have hnorm := Ideal.absNorm_span_singleton (l : 𝓞 F)
    rw [h, Ideal.absNorm_top] at hnorm
    have hcast : (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hnorm
    have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp hnorm.symm with h' | h'
    · exact hl.one_lt.ne' h'
    · omega
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔟 h𝔟
    haveI := Fact.mk hl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
    have hlx : (l : 𝓞 F ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : Ideal.Quotient.mk 𝔟 a * (l : 𝓞 F ⧸ 𝔟) = 1 := by
      have key := congrArg (Ideal.Quotient.mk 𝔟) hbc
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, map_natCast,
        map_one] at key
      exact key
    have hx0 : x = 0 := by
      rw [← one_mul x, ← hunit, mul_assoc, hlx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hl.one_lt.ne hx

end GlobalTheory.CompanionTheory.DeligneRibet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

theorem algebraMap_overPre {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

theorem zeroth_cohomology_ideal_transfer : ∀ {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (G : Z.Modules), letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (J : Ideal Γ(X, V)) (x : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0), x ∈ (J • ⊤ : Submodule Γ(X, V) (Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x : Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))) ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  intro X Z φ V hV G
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro J x hx
  let L : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj G, V) :=
    { toFun := fun x => G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
        (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
          Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
      map_add' := fun x y => by
        rw [map_add (f := _)]
        exact map_add _ _ _
      map_smul' := fun b x => by
        rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
        refine (RelSerre.smul_restrict_top G (φ ⁻¹ᵁ V) _ _).trans ?_
        refine (congrArg (· • _) (algebraMap_overPre φ V hV b)).trans ?_
        exact (smul_pushforward φ G b _).symm }
  change L x ∈ _
  refine Submodule.smul_induction_on hx (p := fun x => L x ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V))) (fun b hb y _ => ?_) (fun y y' hy hy' => ?_)
  · show L (b • y) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · show L (y + y') ∈ _
    rw [map_add (f := _)]
    exact add_mem hy hy'

theorem mem_formalK_of_factor {B : Type} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {Y : Scheme.{0}} [Y.Over (Spec (.of B))] {P F : Y.Modules} (f : P ⟶ F) (k : ℕ)
    (g : P ⟶ idealPow J F (k + 1)) (hg : g ≫ idealPowι J F (k + 1) = f) (p : Γ(P, ⊤)) :
    (Sheaf.H.equiv₀ (modulesAb F) isTerminalTop).symm (f.app ⊤ p) ∈ formalK J F 0 k := by
  refine ⟨(Sheaf.H.equiv₀ (modulesAb (idealPow J F (k + 1))) isTerminalTop).symm (g.app ⊤ p), ?_⟩
  refine (Sheaf.H.equiv₀_symm_naturality (hT := isTerminalTop)
    (modulesAbMap (idealPowι J F (k + 1))) (g.app ⊤ p)).trans ?_
  congr 1
  rw [← hg]
  rfl

theorem formal_shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {G : Z.Modules}, IsCoherent G → ∀ (V : X.Opens), IsAffineOpen V → ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(G, φ ⁻¹ᵁ V)), s ∈ Set.range ((idealPowι I G (n + c)).app (φ ⁻¹ᵁ V)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from s) ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  intro A _ _ I X Z _ _ _ φ hprop hφ G hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  haveI := hG.1
  have hF : IsCoherent (G.restrict (φ ⁻¹ᵁ V).ι) := hG.restrict _
  obtain ⟨c₀, hc₀⟩ := exists_formalK_le (Ideal.map (toFunctions (A := A) V) I) hF 0
  refine ⟨c₀ + 1, fun n s hs => ?_⟩
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨g, hg⟩ := GlobalTheory.T.affine_restriction_functions_naturality I φ V hV (GlobalTheory.T.open_restriction_functions_compatible φ hφ V hV) G (n + c₀ + 1)
  let p : Γ((idealPow I G (n + c₀ + 1)).restrict (φ ⁻¹ᵁ V).ι, ⊤) :=
    (idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t
  have hx := mem_formalK_of_factor _ _ (n + c₀) g hg p
  have hx2 := hc₀ n hx
  have hx3 := zeroth_cohomology_ideal_transfer φ V hV G _ _ hx2
  rw [← Ideal.map_pow] at hx3
  convert hx3 using 1
  dsimp only
  erw [AddEquiv.apply_symm_apply]
  have nat := NatTrans.naturality_apply (idealPowι I G (n + c₀ + 1)).mapPresheaf
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t
  change _ = G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
    ((idealPowι I G (n + c₀ + 1)).mapPresheaf.app (op ((φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
      ((idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t))
  rw [nat]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [eqToHom_op, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory.CompanionTheory.GE.FormalShift
end
end

