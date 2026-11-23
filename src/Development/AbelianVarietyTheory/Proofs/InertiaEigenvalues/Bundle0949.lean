module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0916
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedLiftUnipotentTypeBaseLevelForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0863
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0944
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatDatumRootOfUnity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

namespace GlobalTheory.ConjTwist.FlatSeries

theorem scale {X B : Type} (J : B → X → ℂ) (τ : ℂ ≃+* ℂ) (ζ η C C' : ℂ) (Φ Φ' : X → ℂ)
    (h1 : ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, Φ g = ∑ k, a k * J (f k) g)
    (h2 : ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, Φ g = ∑ k, a k * J (f k) g) →
      ∀ g, Φ' g = ∑ k, ζ * τ (a k) * J (f k) g)
    (hC : C' = η * τ C) :
    (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, C * Φ g = ∑ k, a k * J (f k) g) ∧
      ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, C * Φ g = ∑ k, a k * J (f k) g) →
        ∀ g, C' * Φ' g = ∑ k, ζ * η * τ (a k) * J (f k) g := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, a, f, h⟩ := h1
    refine ⟨n, fun k => C * a k, f, fun g => ?_⟩
    rw [h g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro n a f ha g
    by_cases hC0 : C = 0
    · subst hC0
      obtain ⟨n₀, b, e, hb⟩ := h1
      have hC' : C' = 0 := by simp [hC]
      have hz : ∀ g, ∑ k, a k * J (f k) g = 0 := fun g => by simpa using (ha g).symm
      have hcat : ∀ g, Φ g = ∑ k, (Fin.append b a) k * J ((Fin.append e f) k) g := fun g => by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [hz g, add_zero, hb g]
      have e1 := h2 _ _ _ hcat g
      have e2 := h2 _ _ _ hb g
      rw [Fin.sum_univ_add] at e1
      simp only [Fin.append_left, Fin.append_right] at e1
      rw [e2] at e1
      have e3 : ∑ k, ζ * τ (a k) * J (f k) g = 0 := by simpa using e1.symm
      have e4 : ∑ k, ζ * η * τ (a k) * J (f k) g = η * ∑ k, ζ * τ (a k) * J (f k) g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4, e3, hC']
      simp
    · have hτ : τ C ≠ 0 := fun h => hC0 ((map_eq_zero_iff τ τ.injective).1 h)
      have hexp : ∀ g, Φ g = ∑ k, (C⁻¹ * a k) * J (f k) g := fun g => by
        have : Φ g = C⁻¹ * (C * Φ g) := by field_simp
        rw [this, ha g, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h2 _ _ _ hexp g, hC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_inv₀]
      field_simp

end GlobalTheory.ConjTwist.FlatSeries

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {ζ η C C' : ℂ}
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') (hC : C' = η * τ C) :
    ConjFun O κ τ (ζ * η) (fun g => C * Φ g) (fun g => C' * Φ' g) := by
  have key := GlobalTheory.ConjTwist.FlatSeries.scale
    (fun (b : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) (g : GA D (Wc D i)) =>
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (b : T.toCore.R ((i : ℕ) + 1)) g))
    τ ζ η C C' Φ Φ' h.1 (fun n a f ha g => h.2 n a f ha g) hC
  exact ⟨key.1, fun n a f ha g => key.2 n a f ha g⟩
end


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.ConjTwist.FlatSeries.conj_flat_series : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  obtain ⟨ζ0, hζ0, hser⟩ := _root_.GlobalTheory.ConjTwist.conjFun_ser hCI D G Pl0 T0 A T R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  refine ⟨ζ0, hζ0, fun t t' hConj f f' hf hf' => ?_⟩
  obtain ⟨s, hs⟩ := hser t t' hConj
  obtain ⟨z, C, C', s₂, hz, rfl, rfl, hC⟩ :=
    _root_.GlobalTheory.FlatConj.flat_conj D G Pl0 T0 A T R F κ v₀ hCore hQ i τ t t' hPins.2.lift.std hFix hConj f f' hf hf'
  refine ⟨s * s₂, fun h hh x x' hx => ?_⟩
  have hzG : z ∈ GfC (Vc D i) := hz.2.1
  have base := hs (h * z) ((GfC (Vc D i)).mul_mem hh hzG) x x' hx
  have sc := GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O i) (κ i) τ base hC
  have e1 : (fun g => ph i * ser R i t (C • R.ωP i t (z, 1) (R.vP i t)) u h (cc x) g) =
      fun g => C * (ph i * ser R i t (R.vP i t) u (h * z) (cc x) g) := funext fun g => by
    rw [_root_.GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t z C hzG u h (cc x) g]
    ring
  have e2 : (fun g => ph i * ser R i t' (C' • R.ωP i t' (z, 1) (R.vP i t')) u h (cc x') g) =
      fun g => C' * (ph i * ser R i t' (R.vP i t') u (h * z) (cc x') g) := funext fun g => by
    rw [_root_.GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t' z C' hzG u h (cc x') g]
    ring
  rw [e1, e2]
  have e3 : ζ0 * ((R.xi t' (s * s₂) : Circle) : ℂ) = ζ0 * ((R.xi t' s : Circle) : ℂ) * ((R.xi t' s₂ : Circle) : ℂ) := by
    rw [map_mul, Circle.coe_mul, mul_assoc]
  rw [e3]
  exact sc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevel
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem not_mem_of_coprime {a b : ℕ} (h : Nat.Coprime a b) {PP : Formalism.L2.DIV.Pl D.host.E}
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hb => by
  have h1 : IsCoprime ((a : ℤ) : 𝓞 D.host.E) ((b : ℤ) : 𝓞 D.host.E) :=
    (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 D.host.E))
  obtain ⟨u, v, huv⟩ := h1
  push_cast at huv
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem exists_flip_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  have hfin : {PP : Formalism.L2.DIV.Pl D.host.E | ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal}.Finite := by
    have h0 : Ideal.span {((M₀ : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM₀
    refine (Ideal.finite_factors h0).subset fun PP hPP => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hPP)
  choose zOf hzG hzOne hzFlip using fun T : Finset (Formalism.L2.DIV.Pl D.host.E) =>
    _root_.GlobalTheory.LevelSeries.exists_central_flip_step D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T M₀
  choose cOf hcOf using fun T => _root_.GlobalTheory.LevelSeries.flipScal_pow_mem D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀ T
  refine ⟨hfin.toFinset.powerset.image zOf, hfin.toFinset.powerset.sup cOf, ?_, ?_⟩
  · intro z hz
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hz
    exact hzG T
  intro H l₂ pd hM hc1 hc2 hbad k _ _ σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  have hoddM : Odd (M₀ * pd) := hM ▸ l₂.odd
  have hoddM₀ : Odd M₀ := (Nat.odd_mul.1 hoddM).1
  have hoddpd : Odd pd := (Nat.odd_mul.1 hoddM).2
  set T₀ := P.filter fun PP => ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₀
  set T₁ := P.filter fun PP => ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₁
  set P₁ := (P \ T₀) ∪ T₀.image Formalism.L2.DIV.conjPl with hP₁
  have hT₁P₁ : T₁ ⊆ P₁ := fun PP hPP => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hPP
    refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h1, fun h3 => ?_⟩)
    exact not_mem_of_coprime hc1 h2 (Finset.mem_filter.1 h3).2.1
  obtain ⟨⟨eT₀, heT₀⟩, e₁, he₁⟩ := _root_.GlobalTheory.IdemFlip.idemSum_sub_and_flip D e P T₀ he (Finset.filter_subset _ _)
  obtain ⟨⟨eT₁, heT₁⟩, e₃, he₃⟩ := _root_.GlobalTheory.IdemFlip.idemSum_sub_and_flip D e₁ P₁ T₁ he₁ hT₁P₁
  have hT₀S : T₀ ∈ hfin.toFinset.powerset :=
    Finset.mem_powerset.2 fun PP hPP => hfin.mem_toFinset.2 (Finset.mem_filter.1 hPP).2.1
  obtain ⟨x₂, hx₂, hstep₂⟩ := hzFlip T₀ eT₀ heT₀ hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  obtain ⟨z₁, hz₁G, hz₁One, hz₁F⟩ := _root_.GlobalTheory.LevelSeries.exists_central_flip_step D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T₁ pd
  obtain ⟨x₁, hx₁, hstep₁⟩ := hz₁F eT₁ heT₁ hoddpd (Nat.Coprime.coprime_mul_left (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  have hsub := _root_.GlobalTheory.LevelSeries.trSp_le_of_subhalf D H l₂ e₂ e₃ _ he₂ he₃ (fun PP hPP => by
    rcases Finset.mem_union.1 hPP with h1 | h1
    · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 h1
      rcases Finset.mem_union.1 h2 with h4 | h4
      · obtain ⟨h5, h6⟩ := Finset.mem_sdiff.1 h4
        by_contra h7
        have h8 := hPM PP h5
        rw [hM, Nat.cast_mul] at h8
        rcases PP.isPrime.mem_or_mem h8 with h9 | h9
        · exact h6 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
        · exact h3 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h4
        obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
        exact _root_.GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le D H l₂ Q (hPM Q hQ1) hQ2
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
      exact _root_.GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le D H l₂ Q (hPM Q hQ1) hQ2) ψ V W ΛV ΛW f₀ l₂.M O
  have hlO : ((l : ℕ) : ℂ) ∈ O := natCast_mem O l
  have ha : (l : ℂ) ^ (hfin.toFinset.powerset.sup cOf) * flipScal χW V W T₀ M₀ x₂ ∈ O := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cOf) hT₀S)
    rw [hd, pow_add, mul_assoc]
    exact mul_mem (pow_mem hlO _) (hcOf T₀ eT₀ x₂ heT₀ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₂ k σ la O hla hO
      hconj hval hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)))
  have hb : flipScal χW V W T₁ pd x₁ ∈ O :=
    _root_.GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l pd hχ hl hc1 hc2 (Nat.Coprime.coprime_mul_left (hM ▸ hbad))
      k σ la O hla hO hconj hval T₁ eT₁ x₁ heT₁ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₁
  refine ⟨zOf T₀, Finset.mem_image_of_mem _ hT₀S, z₁, hz₁G,
    hz₁One l (fun PP hPP => not_mem_of_coprime hc2 (Finset.mem_filter.1 hPP).2.1), fun f hf => ?_⟩
  obtain ⟨F₁, hF₁, hF₁eq⟩ := hstep₂ l₂.M pd e e₁ P O hM
    (fun PP hPP => not_mem_of_coprime (Nat.Coprime.symm hc1) (Finset.mem_filter.1 hPP).2.1) he (Finset.filter_subset _ _) he₁ hz f hf
  obtain ⟨F₂, hF₂, hF₂eq⟩ := hstep₁ l₂.M M₀ e₁ e₃ P₁ O (by rw [hM, mul_comm])
    (fun PP hPP => not_mem_of_coprime hc1 (Finset.mem_filter.1 hPP).2.1) he₁ hT₁P₁ he₃ hz F₁ hF₁
  set c := hfin.toFinset.powerset.sup cOf
  refine ⟨(⟨_, mul_mem ha hb⟩ : O) • F₂, Submodule.smul_mem _ _ (hsub hF₂), fun BW Q s g => ?_⟩
  have hom : om (zOf T₀ * z₁, 1) ((⟨_, mul_mem ha hb⟩ : O) • F₂) = ((l : ℂ) ^ c) • f := by
    have e1 : ((zOf T₀ * z₁, 1) : GA D V × GA D W) = (zOf T₀, 1) * (z₁, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply, Subring.smul_def]
    change om (zOf T₀, 1) (om (z₁, 1) (((l : ℂ) ^ c * flipScal χW V W T₀ M₀ x₂ * flipScal χW V W T₁ pd x₁) • F₂)) = _
    rw [← smul_smul, map_smul, hF₂eq, ← smul_smul, map_smul, hF₁eq]
  have := _root_.GlobalTheory.LevelSeries.thetaKO_flip D ψ θ V W χV χW om ΛV ΛW sW f₀ hP (zOf T₀ * z₁) (mul_mem (hzG T₀) hz₁G) e e₂ l₂.M O f _ _ hf
    (Submodule.smul_mem _ _ (hsub hF₂)) hom BW Q s g
  rw [← mul_assoc] at this
  exact this

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeClassSum


set_option maxHeartbeats 1600000 in
theorem goodModel_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) →
    ∀ i, BaseTup Y i → ∀ (j : Fin D.R.m) (b : Bool), ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g) →
      ∃ F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  intro D X E Y hG i hB j b w hw hty
  obtain ⟨t, hxi, hQ⟩ : ∃ t : X.T, X.R.xi t = (Y.Z.ρ.B i j b).de.chi ∧
      X.R.Q t = (Y.Z.ρ.B i j b).de.Q := hB j b
  obtain ⟨y0, rfl⟩ : w ∈ LinearMap.range (X.R.thG j t) := by
    rw [hG j t]; exact hw
  obtain ⟨y, hlaw, heq⟩ := _root_.GlobalTheory.AvgLevel.avg_level D X E Y i j b t hxi hQ y0 hty
  obtain ⟨F, hF, hsum⟩ := _root_.GlobalTheory.LiftClassSum.exists_projected_thetaLift_eq_sum D X E Y i j b t hxi hQ y hlaw
  exact ⟨F, _root_.GlobalTheory.BaseSpan.formsC_le_span_mt D X E Y i j b F hF, heq.symm.trans hsum⟩

end GlobalTheory.TypeClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

open GlobalTheory.TwInputs GlobalTheory.RealGeo Formalism.L2.Pj Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


set_option maxHeartbeats 8000000 in
theorem exists_framed (hP : GlobalTheory.Published.CuspRapidDecay) (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X) :
    ∃ (X' : RealSide D) (Y' : SerSide X' E), FieldOk X' ∧
      (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X'.core X'.R.toRealDat j X'.core.σ₀ hV) ∧
      (∀ i j b, RatRow Y'.YS X'.geo.v₀ Y'.Z.good i j b → RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧
      (XiBdd Y'.Z.rd → XiBdd Y.Z.rd) := by
  have hC : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.thP⟩
  obtain ⟨c', w, hw, hfr, B, hB⟩ := exists_framed_half hP X.size hC X.geo X.unif X.inGeo
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := X.F) (realDatMovedReadingsKeepScalars X.R w)
  have hch : (fullHeckeRealDatMovedReadings X.R w kap lam).Char3 X.F := heckeCharacterisation_transfer_movedReadings X.char hs
  obtain ⟨B', -, hB', -⟩ := @geoHalf_upd D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (moveR X.R.toRealDat w) _ kap X.R.lam
    X.R.err0 B
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B'
  obtain rfl : v₀ = X.geo.v₀ := (eq_of_heq hB').trans hB
  let g : @GeoHalf D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat fun _ => 1 :=
    @GeoHalf.mk D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _
      κ X.geo.v₀ fw bar O pins rho eqa ct phase
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev
      ((X.geo.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  obtain ⟨hI, hU, hInt⟩ := @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg
    (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _ g
    ⟨hch.lev, hch.grp.red_R, hch.grp.red_L, hch.grp.record, hch.fam, hch.models, hch.chain, hch.thP⟩ hch.grp.chiW hpb X.size
  have hst : ∀ i, (X.R.FW i).MKStable := fun i => (X.integral i).2.2
  let X' : RealSide D := @RealSide.mk D X.Γ X.grp X.fin X.Pl0 X.I0 X.T X.A3 (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam) X.F X.cG g
    hch X.phs X.guard X.valKs X.idem hU hInt hI X.finT X.host X.std X.size
  let Y' : SerSide X' E :=
    { S := moveS w Y.YS
      YS := moveYS kap lam Y.YS hw hst
      sup := Y.sup
      H := moveH kap lam Y.YS hw hst Y.H
      reads := reads_move kap lam Y.YS hw hst Y.reads
      del := Y.del
      Z := moveZ kap lam hw hst Y.Z
      U_eq := Y.U_eq
      psi_eq := Y.psi_eq
      low := Y.low
      Sb := Y.Sb
      B_range := Y.B_range
      hk_emb := Y.hk_emb
      hk_split := Y.hk_split
      off := Y.off
      all := Y.all }
  refine ⟨X', Y', ⟨hF.galois, hF.star, hF.vals, hF.ray, hF.roots, hF.split⟩, hfr,
    fun i j b => (ratRow_move kap lam Y.YS hw hst X.geo.v₀ Y.Z.good i j b).1, fun h => ?_⟩
  rw [← rd_move kap lam hw hst Y.Z]
  exact h

end GlobalTheory.Unframe

section

open GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf

theorem GlobalTheory.Unframe.rat_and_xiBdd : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  intro hP hA hR hS D X E Y hF
  obtain ⟨X', Y', hF', hfr, h1, h2⟩ := GlobalTheory.Unframe.exists_framed hP X Y hF
  exact ⟨fun i hi j b => h1 i j b (_root_.GlobalTheory.RatBundles.rat_bundles hA hR D X' E Y' hF' hfr i hi j b), h2 (_root_.GlobalTheory.XiBound.main hA hR hS D X' E Y' hF' hfr)⟩

end
end
end

