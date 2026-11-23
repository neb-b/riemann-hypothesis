module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLift

open GlobalTheory.PointAtPlaceHom

variable {D : D7}

def prodAt (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) : GA D V :=
  (l.map fun τ => atTau θ V τ (u τ)).prod

theorem prodAt_mem (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) :
    prodAt θ V l u ∈ GinfC V := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact atTau_mem V τ _

theorem infMat_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {u : D.what₂.Tau → Mt V.rank}
    (hu : u ∈ UG (gramAt D V)) (ρ : D.what₂.Tau) (l : List D.what₂.Tau) (hl : l.Nodup) :
    infMat D.sp.cm.sig V.gram (θ ρ) (prodAt θ V l u) = if ρ ∈ l then u ρ else 1 := by
  induction l with
  | nil => rw [if_neg List.not_mem_nil]; exact infMat_one V _
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) u = atTau θ V τ (u τ) * prodAt θ V l u := List.prod_cons
    have hs := atTau_spec hθ V τ (hu τ)
    rw [List.nodup_cons] at hl
    rw [e, infMat_mul, ih hl.2]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem continuousOn_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : List D.what₂.Tau) :
    ContinuousOn (prodAt θ V l) (UG (gramAt D V)) := by
  induction l with
  | nil => exact continuousOn_const
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) = fun u => atTau θ V τ (u τ) * prodAt θ V l u := funext fun _ => List.prod_cons
    have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
    have c : ContinuousOn (fun u : D.what₂.Tau → Mt V.rank => atTau θ V τ (u τ)) (UG (gramAt D V)) :=
      (continuousOn_atTau hθ V τ).comp (continuous_apply τ).continuousOn fun u hu => hu τ
    rw [e]
    exact c.mul ih

theorem archM_mem {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    archM V (θ τ) g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ = fun ρ => θ₀ (tauE D ρ) := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ fun ρ => h₀ _
  subst e
  exact (GlobalTheory.Member.Arch.unit_iff _ _ _).1 (((GlobalTheory.Member.Arch.archM_spec D V θ₀ h₀).1 _).2.2.2.2 g)

theorem exists_real_lift : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  intro D θ V hθ
  obtain ⟨r1, -, r3, r4, -, r6, r7, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let L : (D.what₂.Tau → Mt V.rank) → GA D V := prodAt θ V Finset.univ.toList
  have hm : ∀ u, L u ∈ GinfC V := prodAt_mem θ V _
  have hL : ∀ u ∈ UG (gramAt D V), ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (L u) = u τ := fun u hu τ => by
    rw [infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  refine ⟨L, fun u hu => ⟨hm u, hL u hu⟩, fun u hu u' hu' => ?_, continuousOn_prodAt hθ V _,
    fun g τ => archM_mem hθ V g τ, fun u hu => ?_, fun τ g hg => ?_, r7, fun a ha u hu => (r6 u hu a ha).symm,
    fun τ => ⟨(r1 τ).1, (r1 τ).2.ne_zero⟩⟩
  · refine r3 _ (hm _) _ (mul_mem (hm _) (hm _)) fun τ => ?_
    rw [r4, hL u hu, hL u' hu', hL (u * u') fun ρ => mul_mem_UH (hu ρ) (hu' ρ)]
    rfl
  · exact r3 _ (hm _) _ hu fun τ => hL _ (fun ρ => archM_mem hθ V u ρ) τ
  · have hs := atTau_spec hθ V τ hg
    have hu : (Pi.mulSingle τ g : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun ρ => by
      by_cases c : ρ = τ
      · subst c
        rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne c]
        exact one_mem_UH _
    refine r3 _ hs.1 _ (hm _) fun ρ => ?_
    rw [hL _ hu]
    by_cases c : ρ = τ
    · subst c
      rw [Pi.mulSingle_eq_same, hs.2.1]
    · rw [Pi.mulSingle_eq_of_ne c, hs.2.2 ρ c]

end GlobalTheory.RealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseFieldGeneratorLocalDifferentInertPlace
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.InertDifferentGen

theorem exists_mul_valuation_eq_one {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ δ ∈ J⁻¹, ∃ z ∈ J, w.valuation E (δ * z) = 1 := by
  by_contra h
  push Not at h
  have h1 : J⁻¹ * J = 1 := inv_mul_cancel₀ hJ
  have hone : (1 : E) ∈ J⁻¹ * J := by rw [h1]; exact FractionalIdeal.one_mem_one _
  have key : w.valuation E (1 : E) < 1 := by
    refine FractionalIdeal.mul_induction_on (C := fun x => w.valuation E x < 1) hone ?_ ?_
    · intro a ha b hb
      have hm : a * b ∈ J⁻¹ * J := FractionalIdeal.mul_mem_mul ha hb
      rw [h1, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨x, hx⟩ := hm
      refine lt_of_le_of_ne ?_ (h a ha b hb)
      rw [← hx]
      exact w.valuation_le_one x
    · intro x y hx hy
      exact Valuation.map_add_lt _ hx hy
  simp at key

theorem mem_dual_one_iff {E : Type} [Field E] [NumberField E] (e : E) :
    e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e)) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 E)⁰ E))]
  constructor
  · intro h o
    obtain ⟨k, hk⟩ := h (o : E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at hk
    rw [← hk]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm]
    exact hk

theorem exists_generator_different_of_isInertAt :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  intro F E _ _ _ _ _ v w hin
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  obtain ⟨δ, hδ, z, hz, hδz⟩ := exists_mul_valuation_eq_one w _ hJ
  obtain ⟨t, ht⟩ := v.valuation_surjective F (w.valuation E δ)
  rw [← GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hin] at ht
  have hδ0 : w.valuation E δ ≠ 0 := by
    intro h0
    rw [map_mul, h0, zero_mul] at hδz
    exact zero_ne_one hδz
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht
    exact hδ0 ht.symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htE (map_zero _)
  refine ⟨t, ht0, δ / algebraMap F E t, algebraMap F E t * z, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, ht, div_self hδ0]
  · rw [map_mul, ht, ← map_mul, hδz]
  · intro e he
    rw [div_mul_cancel₀ _ htE]
    have hm := FractionalIdeal.mul_mem_mul hδ ((mem_dual_one_iff e).2 he)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at hm
    exact hm
  · rw [mul_comm (algebraMap F E t) z, mul_inv_cancel_right₀ htE]
    exact (mem_dual_one_iff z).1 hz

end GlobalTheory.InertDifferentGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

namespace GlobalTheory.CoverDeg

theorem exists_goodCover_of_coords_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  intro k _ X Y p π D δ x U₁ U₂ hU₁ hx₁ ⟨t, ht⟩ hU₂ hx₂ hV₂ he hf hfr
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU₁ hU₂ x ⟨hx₁, hx₂⟩
  have hxU : x ∈ X.basicOpen g := hfg ▸ hxf
  refine ⟨X.basicOpen g, hxU, ?_⟩
  have hUU₁ : X.basicOpen g ≤ U₁ := hfg ▸ X.basicOpen_le f
  have hUU₂ : X.basicOpen g ≤ U₂ := X.basicOpen_le g
  have hUa : IsAffineOpen (X.basicOpen g) := hU₂.basicOpen g
  have hpre : π ⁻¹ᵁ X.basicOpen g = Y.basicOpen (π.app U₂ g) := Scheme.preimage_basicOpen π g
  have hVa : IsAffineOpen (π ⁻¹ᵁ X.basicOpen g) := hpre ▸ hV₂.basicOpen _
  have hVV₂ : π ⁻¹ᵁ X.basicOpen g ≤ π ⁻¹ᵁ U₂ := fun _ h => hUU₂ h
  refine ⟨hUa, hVa, ?_, ?_⟩
  · refine ⟨fun i => resG X hUU₁ (t i), ?_⟩
    have e : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen g)) (fun i => resG X hUU₁ (t i)) =
        (resG X hUU₁).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG X hUU₁).Etale := by
      letI : Algebra Γ(X, U₁) Γ(X, X.basicOpen g) := (resG X hUU₁).toAlgebra
      haveI : IsLocalization.Away f Γ(X, X.basicOpen g) :=
        hU₁.isLocalization_of_eq_basicOpen f (homOfLE hUU₁) hfg.symm
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ ht hR
  · letI i1 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := (π.app U₂).hom.toAlgebra
    letI i2 : Algebra Γ(X, U₂) Γ(X, X.basicOpen g) := (resG X hUU₂).toAlgebra
    letI i3 : Algebra Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (resG Y hVV₂).toAlgebra
    letI i4 : Algebra Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (π.app (X.basicOpen g)).hom.toAlgebra
    letI i5 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      ((π.app (X.basicOpen g)).hom.comp (resG X hUU₂)).toAlgebra
    have hnat : (π.app (X.basicOpen g)).hom.comp (resG X hUU₂) = (resG Y hVV₂).comp (π.app U₂).hom := by
      ext a
      exact congr($(π.naturality (homOfLE hUU₂).op) a)
    haveI : IsScalarTower Γ(X, U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' hnat
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) :=
      hU₂.isLocalization_of_eq_basicOpen g (homOfLE hUU₂) rfl
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g))
        Γ(Y, π ⁻¹ᵁ X.basicOpen g) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact hV₂.isLocalization_of_eq_basicOpen (π.app U₂ g) (homOfLE hVV₂) hpre
    haveI hpo : Algebra.IsPushout Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Algebra.isPushout_of_isLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ U₂)
        Γ(Y, π ⁻¹ᵁ X.basicOpen g)
    have het : (algebraMap Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g)).Etale :=
      RingHom.Etale.isStableUnderBaseChange _ _ _ _ he
    haveI : Module.Finite Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := hf
    haveI hfin : Module.Finite Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Module.Finite.of_isLocalization Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g)
    refine ⟨het, hfin, ?_⟩
    obtain ⟨hfree, hrk⟩ := hfr
    haveI : Nontrivial Γ(X, X.basicOpen g) := (X.presheaf.germ _ x hxU).hom.domain_nontrivial
    haveI : Nontrivial Γ(X, U₂) := (X.presheaf.germ _ x hx₂).hom.domain_nontrivial
    let b := Module.Free.chooseBasis Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂)
    let b' := hpo.symm.out.basis b
    refine ⟨Module.Free.of_basis b', ?_⟩
    rw [Module.finrank_eq_card_basis b', ← hrk, Module.finrank_eq_card_basis b]

end GlobalTheory.CoverDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_isChowFormInt_of_ringKrullDim_eq (K : Type) [Field K] (N D : ℕ)
    (P : Ideal (MvPolynomial (Fin N) K)) (hP : P.IsPrime)
    (hh : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  classical
  have hI : P.IsHomogeneous (homogeneousSubmodule (Fin N) K) := by
    intro n g hg
    have h1 : (DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K) =
        homogeneousComponent n g := MvPolynomial.decomposition.decompose'_apply g n
    rw [h1]
    exact hh g hg n
  have hX : ∃ j, X j ∉ P := by
    by_contra hc
    push Not at hc
    have h0 := GlobalTheory.ringKrullDim_quotient_le_zero_of_forall_X_mem hc
    rw [hdim] at h0
    have h1 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h0
    have h2 : D + 1 ≤ 0 := by exact_mod_cast h1
    omega
  have hdim' : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (Fintype.card (Fin (D + 1)) : ℕ) := by
    rw [Fintype.card_fin]; exact hdim
  have hprime : (GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P).IsPrime := GlobalTheory.Chow.isPrime_elimIdeal hX
  have hne : GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P ≠ ⊥ := GlobalTheory.Chow.elimIdeal_ne_bot hI hX hdim'.le
  obtain ⟨f, hf⟩ := (GlobalTheory.Chow.isPrincipal_elimIdeal hdim').principal
  have hf' : GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P = Ideal.span {f} := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne (by rw [hf', Ideal.span_singleton_eq_bot])
  have hfmem : f ∈ GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P := hf' ▸ Ideal.subset_span rfl
  have hfp : Prime f := (Ideal.span_singleton_prime hf0).1 (hf' ▸ hprime)
  obtain ⟨a, ha⟩ := GlobalTheory.Chow.exists_isWeightedHomogeneous_of_dvd
    (GlobalTheory.Chow.blockWeight : Fin (D + 1) × Fin N → Fin (D + 1) → ℕ) (f := f) (fun a => by
      rw [← Ideal.mem_span_singleton, ← hf']
      exact GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal hfmem a)
  have ha' : GlobalTheory.Chow.IsBlockHomogeneous f a := ha
  have hconst : ∀ i, a i = a 0 := by
    intro i
    have h1 := GlobalTheory.Chow.map_rename_elimIdeal (Equiv.swap i 0) P
    rw [hf', Ideal.map_span, Set.image_singleton] at h1
    obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq h1
    have h2 : GlobalTheory.Chow.IsBlockHomogeneous f (a ∘ (Equiv.swap i 0).symm) := by
      rw [hcf]
      exact IsWeightedHomogeneous.C_mul (ha'.rename (Equiv.swap i 0)) c
    have h3 := congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique hf0 ha' h2) i
    simpa using h3
  refine ⟨a 0, f, ?_, hfp.irreducible, fun u => ?_⟩
  · rw [isMultiHomogeneous_iff_block, ← (funext hconst : a = fun _ => a 0)]
    exact ha'
  · rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u, hf']
    refine ⟨fun hu p hp => ?_, fun hu => hu f (Ideal.subset_span rfl)⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    rw [map_mul, hu, mul_zero]

end GlobalTheory.ChowHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjModelExt
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExt

open GlobalTheory.ConjDS GlobalTheory.LowTypeDetermined

section Gen

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realMap (T : H ≃ₗᵢ⋆[ℂ] H') : H →L[ℝ] H' where
  toFun := T
  map_add' := map_add T
  map_smul' r x := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
  cont := T.continuous

theorem smoothVec_map (T : H ≃ₗᵢ⋆[ℂ] H') (h : ∀ g v, T (σ g v) = σ' g (T v)) {L : Set (Matrix (Fin n) (Fin n) ℂ)}
    {w : H} (hw : SmoothVec L σ w) : SmoothVec L σ' (T w) := by
  intro k Xs hX
  simp only [← h]
  exact (realMap T).contDiff.comp (hw k Xs hX)

theorem lowKSub_stab {lam : Fin n → ℝ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) {w : H}
    (hw : w ∈ lowKSub ε lam σ) : σ g w ∈ lowKSub ε lam σ := by
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => (le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS) (hS.2.1 g hg x hx)
  exact this hw

theorem lowKSub_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {lam : Fin n → ℝ} {w : H} (hw : w ∈ lowKSub ε lam σ) : T.symm w ∈ lowKSub ε' (nr lam) σ' := by
  have : lowKSub ε lam σ ≤ (lowKSub ε' (nr lam) σ').comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
    refine sSup_le fun S hS x hx => ?_
    have h1 := ktype_transfer (sg_symm he) T.symm (symm_inter T h) hS
    rw [← lowK_rev he] at h1
    refine (le_sSup (s := {S | IsKTypeOf ε' σ' (Formalism.QuantumDeterminants.lowK ε' (nr lam)) S}) h1) ?_
    show T (T.symm x) ∈ S
    simpa using hx
  exact this hw

def prm (ε ε' : Fin n → Bool) : Equiv.Perm (Fin n) :=
  ((Fin.revPerm.trans (revNeg ε')).trans Fin.revPerm).trans (revNeg ε).symm

theorem revNeg_prm (a : Fin n) : revNeg ε (prm ε ε' a) = (revNeg ε' a.rev).rev := by
  simp [prm]

theorem eps_prm (he : ∀ a, ε' a = ε a.rev) (a : Fin n) : ε (prm ε ε' a) = ε a := by
  rw [← eps_revNeg ε (prm ε ε' a), revNeg_prm, ← he (revNeg ε' a.rev), eps_revNeg ε' a.rev, he, Fin.rev_rev]

theorem ext_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    (hU : IsURepOn (UJset ε) σ) {lam : Fin n → ℝ} {w : H}
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w) :
    IsWtOn (Formalism.REAL.Kset ε') σ' (fun a => Formalism.QuantumDeterminants.lowK ε' (nr lam) (revNeg ε' a))
      (T.symm (σ (pM (prm ε ε')) w)) := by
  have h1 := wt_transfer (sg_symm he) T.symm (symm_inter T h) (isWtOn_perm hU (prm ε ε') (eps_prm he) hw)
  convert h1 using 1
  funext a
  rw [lowK_rev he]
  simp [nr, revNeg_prm]

end Gen

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem conj_rep (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : (conjModel M).H τ) :
    cj (M.H τ) ((conjModel M).rep τ g w) = M.rep τ g (cj (M.H τ) w) := by
  have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
    rw [inv_submatrix_equiv]
    have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (M.fr τ * g * (M.fr τ)⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  show M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj _ w) = M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj _ w)
  rw [e]

theorem smooth_translate (M : DSModel V S) (τ : D.what₂.Tau) (u : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ g u) := by
  obtain ⟨_, -, hσ, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  have hu' : (u : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ u.2
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact translate_mem (isUnit_gram hP h) (isURepOn_conj hσ hP h) (conj_inv_mem hP h hg) hu'

theorem exists_conjModel_ext : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v : M.Vec), IsExtVec M v → ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  intro D V S M v hv
  have he : ∀ τ a, (conjModel M).ε τ a = M.ε τ a.rev := fun _ _ => rfl
  have hK := fun τ => pM_mem (prm (M.ε τ) ((conjModel M).ε τ)) (eps_prm (he τ))
  have hU : ∀ τ, IsURepOn (UJset (M.ε τ)) (M.σ τ) := fun τ => (M.ds τ).2.2.1
  let c : ∀ τ, (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := fun τ => cj (M.H τ)
  have hc : ∀ τ g y, c τ ((conjModel M).σ τ g y) = M.σ τ (rv g) (c τ y) := fun _ _ _ => rfl
  have hr : ∀ τ g y, (c τ).symm (M.rep τ g y) = (conjModel M).rep τ g ((c τ).symm y) := fun τ g y => by
    apply (c τ).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (conj_rep M τ g _).symm
  refine ⟨conjModel M, c, fun τ => ⟨(c τ).symm (M.σ τ (pM (prm (M.ε τ) ((conjModel M).ε τ))) (v τ)),
    Submodule.subset_span (smoothVec_map (c τ).symm (hr τ) (smooth_translate M τ (v τ) (kset_uj (hK τ))))⟩,
    fun τ g _ y => conj_rep M τ g y, fun τ => ⟨?_, ?_, ?_⟩⟩
  · rw [LinearIsometryEquiv.norm_map, (hU τ).2.1 _ (kset_uj (hK τ)), (hv τ).1]
  · exact lowKSub_transfer (he τ) (c τ) (hc τ) (lowKSub_stab (hK τ) (hv τ).2.1)
  · exact ext_transfer (he τ) (c τ) (hc τ) (hU τ) (hv τ).2.2

end GlobalTheory.ConjExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqIteratePrimeCharP
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem derivation_iterate_leibniz {R : Type} [CommRing R] (D : Derivation ℤ R R) (a b : R) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : R) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : R) = (n.choose ij.1 : R) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

end GlobalTheory
end

