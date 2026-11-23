module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisSeriesTermsMemPrimePowStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_series_terms_mem_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ c : ℤ → Acris l, (∀ n : ℤ, (l : Acris l) ^ n.natAbs ∣ c n) ∧ ∀ n : ℤ, (l : Acris l) ^ n.toNat * c n = (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
  first | exact @GlobalTheory.PSer.terms_mem | exact GlobalTheory.PSer.terms_mem | (intros; apply GlobalTheory.PSer.terms_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActVdRMemTensorDeRhamFiltrationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a → actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  first | exact @GlobalTheory.FilStable.actVdR_mem_FilV | exact GlobalTheory.FilStable.actVdR_mem_FilV | (intros; apply GlobalTheory.FilStable.actVdR_mem_FilV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParamsOfRoomy
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem admissible_params_of_roomy {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (h : Roomy L 100) :
    (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧
      (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧
      L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hm : (0 : ℝ) ≤ (D.host.Lw : ℝ) * L.sc.b' := mul_nonneg hL hb
  have h6 : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  refine ⟨⟨by linarith, h3, h6, h4, P.t_le_eta⟩, by linarith⟩

theorem admissible_params_large : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧ (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧ L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.HTW.roomy_of_large eps 100 A heps le_rfl
  exact ⟨x0, fun D L P h1 h2 h3 => admissible_params_of_roomy L P (hx0 D L P h1 h2 h3)⟩

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclaration
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Per.AmbFil

theorem filCount_at (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {n : ℕ}
    (M : Br.G D.nbr i w hw →* Matrix (Fin n) (Fin n) ↥C.LL.1) :
    EmbeddingTypes.FilCount (Br.PD D.loc D.nbr i w hw) (matRep M) := by
  intro τ J hJ
  exact GlobalTheory.Per.FilCount.fil_count (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL _ (matRep M) τ J hJ

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  intro D i r ρ π dc
  exact ⟨fun w hw _ C x => filCount_at D i w hw C _,
    fun _ => ⟨fun w hw _ C => filCount_at D i w hw C _, fun w hw _ C => filCount_at D i w hw C _⟩⟩

end GlobalTheory.Per.AmbFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicInteger
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem approx_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  intro l _ r S x a h
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hδ : (0 : ℝ) < ((l : ℝ)⁻¹) ^ r := by positivity
  obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x hδ
  have hdiff : ∀ σ : GQ l, (l : ℤ_[l]) ^ r ∣ a σ - (((a σ).appr r : ℕ) : ℤ_[l]) := by
    intro σ
    exact Ideal.mem_span_singleton.1 (PadicInt.appr_spec r (a σ))
  refine ⟨y, fun σ => (((a σ).appr r : ℕ) : ℤ), ?_, ?_⟩
  · intro σ hσ
    have hY : ‖(y : ℂ_[l]) - x‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← dist_eq_norm, dist_comm]; exact hy.le
    have hAB : ‖algebraMap ℚ_[l] ℂ_[l] ((a σ - (((a σ).appr r : ℕ) : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
      obtain ⟨c, hc⟩ := hdiff σ
      rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
      have := PadicInt.norm_le_one c
      have h0 : (0:ℝ) ≤ ((l : ℝ)⁻¹) ^ r := hδ.le
      calc ((l : ℝ)⁻¹) ^ r * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := mul_one _
    have key : (((σ y - y - ((((((a σ).appr r : ℕ) : ℤ)) : Om l))) : PadicAlgCl l) : ℂ_[l]) =
        (Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])) +
        (Formalism.Per.σC σ ((y : ℂ_[l]) - x) - ((y : ℂ_[l]) - x)) +
        (algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])) := by
      have h1 : ((σ y : PadicAlgCl l) : ℂ_[l]) = Formalism.Per.σC σ (y : ℂ_[l]) := (GlobalTheory.RingBasics.σC_coe σ y).symm
      generalize algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) = A
      rw [map_sub]
      push_cast
      rw [h1]
      ring
    have hAB' : ‖algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      simpa only [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast] using hAB
    rw [← PadicComplex.norm_extends, key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h σ hσ) ?_)) hAB')
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC]; exact hY
    · rw [norm_neg]; exact hY
  · intro σ _
    have : (a σ) = (a σ - (((a σ).appr r : ℕ) : ℤ_[l])) + (((a σ).appr r : ℕ) : ℤ_[l]) := by ring
    rw [this]
    refine dvd_add (hdiff σ) ?_
    have := map_dvd (Int.castRingHom ℤ_[l]) (by assumption : (l : ℤ) ^ r ∣ (((a σ).appr r : ℕ) : ℤ))
    simpa using this

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.AwayT

theorem away_of_injective {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    (hu : IsUnit (algebraMap R S t))
    (hs : ∀ b : S, ∃ (r : ℕ) (x : R), b * algebraMap R S t ^ r = algebraMap R S x)
    (hi : Function.Injective (algebraMap R S)) : IsLocalization.Away t S :=
  IsLocalization.Away.mk t hu hs fun _ _ h => ⟨0, by rw [hi h]⟩

theorem lift_injective {R P S : Type} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] (x : R)
    [IsLocalization.Away x P] (f : R →+* S) (g : P →+* S) (hg : ∀ a, g (algebraMap R P a) = f a)
    (hf : Function.Injective f) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj x z
  have h1 : f a = 0 := by rw [← hg, ← ha, map_mul, hz, zero_mul]
  have h2 : a = 0 := hf (h1.trans (map_zero f).symm)
  rw [h2, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := P) x).pow n).mul_left_eq_zero.1 ha

variable {l : ℕ} [Fact l.Prime]

theorem plusInj (C : Core l) : C.PlusInj :=
  lift_injective ((l : ℕ) : Per.Acris l) C.j C.jP C.jP_alg (crisP_injective l C.j C.j_cris)

theorem plusToB_injective (C : Core l) : Function.Injective (plusToB l) := fun x y h =>
  plusInj C ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_plusToB, ← C.ι_plusToB, h]))

theorem acris_injective (C : Core l) : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) :=
  fun x y h => crisP_injective l C.j C.j_cris
    ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_j, ← C.ι_j, h]))

theorem awayT (C : Core l) : C.AwayT :=
  away_of_injective C.t (core_t_unit_fil l C).1 (GlobalTheory.T.bcris_eq_acris_localization_periodT l C) (acris_injective C)

theorem plusAwayT (C : Core l) : C.PlusAwayT := by
  letI := (plusToB l).toAlgebra
  have e : ∀ x : Per.Acris l, algebraMap (BcrisP l) (Per.Bcris l) (algebraMap _ _ x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := plusToB_alg
  refine away_of_injective _ ?_ (fun b => ?_) (plusToB_injective C)
  · rw [e]
    exact (core_t_unit_fil l C).1
  · obtain ⟨r, x, h⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
    exact ⟨r, algebraMap _ _ x, by rw [e, e]; exact h⟩

theorem away_and_inj (l : ℕ) [Fact l.Prime] (C : Core l) : C.AwayT ∧ C.PlusAwayT ∧ C.PlusInj :=
  ⟨awayT C, plusAwayT C, plusInj C⟩

end GlobalTheory.MemLoc.AwayT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.OneSubPhi

theorem one_sub_mul_onto (p : ℕ) {A : Type} [CommRing A] (φ : A →+* A)
    (hA : IsAdicComplete (Ideal.span {(p : A)}) A) (x : A) : ∃ y : A, y - (p : A) * φ y = x := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) A := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := A), Ideal.map_span, Set.image_singleton, map_natCast]
    exact hA
  let f : A →ₗ[ℤ] A :=
    LinearMap.id - ((AddMonoidHom.mulLeft (p : A)).comp φ.toAddMonoidHom).toIntLinearMap
  have hf : ∀ y, f y = y - (p : A) * φ y := fun _ => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    refine ⟨g, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have : g - (p : A) * φ g - g = (p : ℤ) • (-φ g) := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨y, hy⟩ := hs x
  exact ⟨y, (hf y).symm.trans hy⟩

theorem onto_of_denom (p : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (φ : A →+* A)
    (ψ : B →+* B) (hψ : ∀ x, ψ (f x) = f (φ x)) (t : A) (ht : φ t = (p : A) * t)
    (hT : IsUnit (f t)) (hp : IsUnit (p : B))
    (h0 : ∀ x : A, ∃ y : A, y - (p : A) * φ y = x)
    (h1 : ∀ (r : ℕ) (x : A), ∃ β z : A, (p : A) * φ x = (p : A) * (φ β - (p : A) ^ r * β) + t * z)
    (r : ℕ) : ∀ (x : A) (b : B), b * f t ^ r = f x * f t → ∃ y : B, y - ψ y = b := by
  have hψT : ψ (f t) = (p : B) * f t := by rw [hψ, ht, map_mul, map_natCast]
  induction r with
  | zero =>
    intro x b hb
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨f y * f t, ?_⟩
    have e := congrArg f hy
    rw [map_sub, map_mul, map_natCast] at e
    rw [map_mul, hψT, hψ]
    linear_combination f t * e - hb
  | succ r ih =>
    intro x b hb
    have hb' : b * f t ^ r = f x := hT.mul_right_cancel (by rw [← hb]; ring)
    obtain ⟨β, z, hz⟩ := h1 r x
    obtain ⟨s, hs⟩ := (hT.pow r).exists_left_inv
    obtain ⟨q, hq⟩ := (hp.pow (r + 1)).exists_left_inv
    have hψq : ψ q * (p : B) ^ (r + 1) = 1 := by
      have := congrArg ψ hq
      rwa [map_mul, map_pow, map_natCast, map_one] at this
    have eq : ψ q = q := by linear_combination q * hψq - ψ q * hq
    have hψs : ψ s * ((p : B) ^ r * f t ^ r) = 1 := by
      have := congrArg ψ hs
      rwa [map_mul, map_pow, hψT, map_one, mul_pow] at this
    obtain ⟨y, hy⟩ := ih z (f z * f t * s) (by rw [mul_assoc, hs, mul_one])
    have e1 := congrArg ψ hb'
    rw [map_mul, map_pow, hψT, hψ, mul_pow] at e1
    have e2 := congrArg f hz
    simp only [map_mul, map_add (f := _), map_sub, map_pow, map_natCast] at e2
    refine ⟨b - f β * s + q * y, ?_⟩
    rw [map_add (f := _), map_sub, map_mul, map_mul, eq, hψ]
    apply ((hp.pow (r + 1)).mul (hT.pow r)).mul_left_cancel
    linear_combination -(p : B) * e1 - e2 - (p : B) ^ (r + 1) * f β * hs + (p : B) * f (φ β) * hψs
      + f t ^ r * (y - ψ y) * hq + f t ^ r * hy + f z * f t * hs

variable {l : ℕ} [Fact l.Prime]

theorem ainf_onto (r : ℕ) (a : Per.Ainf l) : ∃ β : Per.Ainf l, Per.φA l β - (l : Per.Ainf l) ^ r * β = a := by
  obtain ⟨β, hβ⟩ := (ArtinSchreierWitt.main l).2.2 ((l : Per.Ainf l) ^ r) a
  exact ⟨β, by rw [GlobalTheory.RingBasics.φA_apply]; exact hβ⟩

theorem phiA_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := exists_mu_pow_div l e he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow, ← TFil.alg_factor] at hw1
  exact ⟨_, hw1⟩

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem mul_phi_mem (C : Core l) (x : Per.Acris l) : ∃ (a : Per.Ainf l) (z : Per.Acris l),
    (l : Per.Acris l) * phiA l x = (l : Per.Acris l) * algebraMap (Per.Ainf l) (Per.Acris l) a + C.t * z := by
  have he := core_isEps l C
  obtain ⟨t, u, ht, hu, htu⟩ := exists_isLogA l C.ε he.1
  have e1 : t = C.t := (LogFun.log_fun l C.ε C.t he.1 C.t_log).1 t ht
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨w, hw⟩ := exists_w C.ε he.1
  obtain ⟨a, z, hz⟩ := phiA_mem_ainf_add l C.ε he w hw x
  have h2 : l - 1 = l - 2 + 1 := by
    have := (Fact.out : l.Prime).two_le
    omega
  rw [h2, pow_succ] at hw
  generalize algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) = m at hw htu
  refine ⟨a, v * m ^ (l - 2) * z, ?_⟩
  rw [hz, ← e1, htu]
  linear_combination z * hw - m * m ^ (l - 2) * z * hv

end GlobalTheory.MemLoc.OneSubPhi

namespace GlobalTheory.MemLoc

theorem one_sub_phi_onto (l : ℕ) [Fact l.Prime] (C : Core l) : C.OneSubPhiOnto := by
  intro b
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨hT, -, -, hl⟩ := core_t_unit_fil l C
  refine OneSubPhi.onto_of_denom l (algebraMap (Per.Acris l) (Per.Bcris l)) (phiA l) (Per.φB l)
    (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 C.t (TPhi.t_phi l C) hT hl
    (OneSubPhi.one_sub_mul_onto l (phiA l) (acris_basic l).1) (fun s y => ?_) (r + 1) x b
    (by rw [pow_succ, ← mul_assoc, hx])
  obtain ⟨a, z, hz⟩ := OneSubPhi.mul_phi_mem C y
  obtain ⟨β, hβ⟩ := OneSubPhi.ainf_onto s a
  refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) β, z, ?_⟩
  rw [hz, ← hβ, OneSubPhi.phiA_alg, map_sub, map_mul, map_pow, map_natCast]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRham
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PMon.extCoc_dies_in_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  intro l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m
  obtain ⟨Q, hQm⟩ := hQ m
  obtain ⟨R, hRm⟩ := hR m
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l m)
  let σ : ↥(GK K) → P.R.BdR →+* P.R.BdR := fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)

  let A : ↥(GK K) → Matrix a a P.R.BdR := fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f
  let C : ↥(GK K) → Matrix a b P.R.BdR := fun g => (c g).map f
  let D : ↥(GK K) → Matrix b b P.R.BdR := fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  let Di : ↥(GK K) → Matrix b b P.R.BdR := fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  have hDDi : ∀ g, D g * Di g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hDiD : ∀ g, Di g * D g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g) := fun g => by
    show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _
    rw [hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  let Qa : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
  let Qb : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
  have hb : ∀ g, D g * Qb.map (σ g) = Qb := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inr i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ] using h
  have ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inl i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ] using h
  have hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R := fun g => hRm g
  let S : Matrix b b P.R.BdR := ((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)
  have hSR : S * R = 1 := by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRS : (R : Matrix b b P.R.BdR) * S = 1 := by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgS : ∀ g, S.map (σ g) = S * D g := fun g => by
    calc S.map (σ g) = (S * (D g * (R : Matrix b b P.R.BdR).map (σ g))) * S.map (σ g) := by
          rw [hRg g, hSR, Matrix.one_mul]
      _ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by
          simp only [Matrix.mul_assoc]
      _ = S * D g := by rw [hgRS g, Matrix.mul_one]
  have hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R := fun g => by
    symm
    conv_lhs => rw [← hRg g]
    rw [← Matrix.mul_assoc, hDiD g, Matrix.one_mul]
  obtain ⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb := ⟨_, rfl⟩
  have hκ : ∀ g, κ.map (σ g) = κ := fun g => by
    rw [hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]
  let Y : Matrix (a ⊕ b) b P.R.BdR :=
    (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)
  have hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Qb] using h
  have hY : κ * Y = 1 := by
    simp only [Y]
    rw [hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]
  obtain ⟨Λ, hκΛ, hΛ⟩ := _root_.GlobalTheory.invariant_right_inverse_of_right_inverse P.R.BdR (_root_.GlobalTheory.PMon.bdR_tied l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ
  have hQbR : Qb = (R : Matrix b b P.R.BdR) * κ := by
    rw [hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ := fun g => by
    conv_lhs => rw [hQbR]
    rw [Matrix.map_mul, hκ g]
  let Z : Matrix a b P.R.BdR := Qa * Λ
  have hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g) := fun g => by
    have e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ) := by
      rw [← hgQb g]
      exact eq_sub_of_add_eq (ha g)
    simp only [Z]
    rw [Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g),
      Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]
  refine ⟨vecM (-(Z * S)), fun g => ?_⟩
  have hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g) := by
    show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _
    rw [Matrix.map_mul]
  have hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) =
      vecM (A g * (-(Z * S)).map (σ g) * Di g) := by
    show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec
      (vecM ((-(Z * S)).map (σ g))) = _
    rw [homUnit_mulVec]
  rw [hL, hR']
  have hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y) := fun _ _ => rfl
  rw [hsub]
  congr 1
  have hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g)) := by
    rw [Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]
  rw [hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]
  abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeIndexMulCardMapInf
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_index_mul_card_map_inf (G H : Type) [Group G] [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G) (I : Subgroup H) (hf : Function.Surjective f)
    (hN : N.index ≠ 0) : Nat.card ↥I ≤ N.index * Nat.card ↥(N.map f ⊓ I) := by
  have h1 : (N.map f).relIndex I * Nat.card ↥(N.map f ⊓ I) = Nat.card I := by
    rw [Subgroup.relIndex, mul_comm, ← Subgroup.card_mul_index ((N.map f).subgroupOf I)]
    congr 1
    rw [← Subgroup.inf_subgroupOf_right]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h2 : (N.map f).relIndex I ≤ (N.map f).index := by
    rw [← Subgroup.relIndex_top_right]
    apply Subgroup.relIndex_le_of_le_right le_top
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : (N.map f).index ≤ N.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Subgroup.index_map_dvd N hf)
  rw [← h1]
  exact Nat.mul_le_mul_right _ (h2.trans h3)

end GlobalTheory.PMon.Ram
end

