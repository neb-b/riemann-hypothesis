module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.FrameRingGlRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
section
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.CoefChangeCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing TensorProduct

section Algebra

variable {K K' : Type} [Field K] [Field K'] [CharZero K] [Algebra K K']

theorem exists_testRing_ext (p : TRing K) :
    ∃ (q : TRing K') (α : p.R →+* q.R), (∀ a, α (algebraMap K p.R a) = algebraMap K' q.R (algebraMap K K' a)) ∧
      (∀ (S : Type) [CommRing S] [Algebra K' S] (φ : p.R →+* S),
        (∀ a, φ (algebraMap K p.R a) = algebraMap K' S (algebraMap K K' a)) →
        ∃ β : q.R →ₐ[K'] S, ∀ v, β (α v) = φ v) ∧
      ∀ (m : ℕ) (b : Fin m → K') (v : Fin m → p.R), ∑ i, algebraMap K' q.R (b i) * α (v i) = 0 →
        ∀ lam : K' →ₗ[K] K, ∑ i, lam (b i) • v i = 0 := by
  obtain ⟨hft, hred⟩ := (GlobalTheory.reduced_finiteType_iff_testRing K).2 p
  have hred' : IsReduced (K' ⊗[K] p.R) := GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  obtain ⟨q, ⟨e⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing K').1 (K' ⊗[K] p.R) inferInstance hred'
  refine ⟨q, e.symm.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := p.R)).toRingHom,
    fun a => ?_, fun S _ _ φ hφ => ?_, fun m b v hv lam => ?_⟩
  · show e.symm (Algebra.TensorProduct.includeRight (algebraMap K p.R a)) = _
    rw [AlgHom.commutes, ← e.symm.commutes]
    rfl
  · letI : Algebra K S := ((algebraMap K' S).comp (algebraMap K K')).toAlgebra
    haveI : IsScalarTower K K' S := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ' : p.R →ₐ[K] S := { φ with commutes' := hφ }
    refine ⟨(Algebra.TensorProduct.lift (Algebra.ofId K' S) φ' (fun _ _ => Commute.all _ _)).comp e.toAlgHom,
      fun v => ?_⟩
    show Algebra.TensorProduct.lift (Algebra.ofId K' S) φ' (fun _ _ => Commute.all _ _)
      (e (e.symm ((1 : K') ⊗ₜ[K] v))) = _
    rw [e.apply_symm_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have h1 : ∑ i, b i ⊗ₜ[K] v i = (0 : K' ⊗[K] p.R) := by
      have h2 := congrArg e hv
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, map_sum] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = e (algebraMap K' q.R (b i) * e.symm ((1 : K') ⊗ₜ[K] v i))
      rw [map_mul, e.commutes, e.apply_symm_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp
    have h3 := congrArg (fun w => TensorProduct.lid K p.R (lam.rTensor p.R w)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using h3

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l}

section First

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD

variable (c c') (hle : c.F ≤ c'.F)

abbrev inclF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def Compat (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (inclF c c' hle a) = algebraMap c.F S a

variable {c c'}

variable {r : ℕ}

end First

abbrev Natural (c : Coeff l) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f

abbrev FromT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y


variable (Xo c) in
abbrev ValueWD : Prop := EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)


variable (Xo c) in
abbrev HasBC : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z

theorem map_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w :=
  frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h₁ h₂

theorem hasBC_of (hS : Out.SecBaseChangeSt) : HasBC Xo c :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c

theorem evR_spec {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (hy : FromT y) :
    ∃ (p : TRing c.F) (φ : p.R →ₐ[c.F] S) (y₀ : FrPt Xo c p.R), FrMap φ y₀ y ∧
      ∀ f : Rul Xo c, evR Xo c f y = φ (f p y₀) :=
  ⟨_, _, _, hy.choose_spec.choose_spec.choose_spec, fun f => by unfold evR evalAt; rw [dite_eq_left hy]⟩

theorem evR_not {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (hy : ¬ FromT y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt; rw [dite_eq_right hy]

theorem evR_test {f : Rul Xo c} (hf : Natural c f) (p : TRing c.F) (y : FrPt Xo c p.R) : evR Xo c f y = f p y := by
  obtain ⟨q, φ, y₀, h, e⟩ := evR_spec (y := y) ⟨p, AlgHom.id _ _, y, GlobalTheory.Frames.frMapUniq_refl y⟩
  rw [e, hf q p φ y₀ y h]

theorem evR_of_map (hWD : ValueWD Xo c) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S] [Algebra c.F S]
    {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y₀ : FrPt Xo c p.R} {y : FrPt Xo c S} (h : FrMap φ y₀ y) :
    evR Xo c f y = φ (f p y₀) := by
  obtain ⟨q, ψ, y₁, h₁, e⟩ := evR_spec (y := y) ⟨p, φ, y₀, h⟩
  rw [e]
  exact hWD f hf S q p ψ φ y₁ y₀ y h₁ h

theorem evR_map (hWD : ValueWD Xo c) {f : Rul Xo c} (hf : Natural c f) {S T : Type} [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y)
    (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, ψ, y₀, h₀, e⟩ := evR_spec hy
  rw [e, evR_of_map hWD hf (map_trans ψ φ h₀ h)]
  rfl

theorem map_cancel (hBC : HasBC Xo c) {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {α : R →ₐ[c.F] S} {β : S →ₐ[c.F] T} {φ : R →ₐ[c.F] T} (hc : β.comp α = φ)
    {y : FrPt Xo c R} {z : FrPt Xo c S} {w : FrPt Xo c T} (h₁ : FrMap α y z) (h₂ : FrMap φ y w) : FrMap β z w := by
  obtain ⟨w', hw'⟩ := hBC S T β z
  have h₃ : FrMap φ y w' := hc ▸ map_trans α β h₁ hw'
  rwa [(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c R T φ y).1 w w' h₂ h₃]

theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hb : FrBor t y y') (h : FrMap φ y z)
    (h' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, g1, g2, hg⟩ := (GlobalTheory.Frames.Model.frBor_iff t y y').1 hb
  refine (GlobalTheory.Frames.Model.frBor_iff _ z z').2 ⟨fun τ => (g τ).map φ, fun τ i => ?_, fun τ i j hij => ?_, ?_⟩
  · simp [g1]
  · simp [g2 τ i j hij]
  · exact (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg h).1 h'

variable (hle : c.F ≤ c'.F)

def resHom {S T : Type} [CommRing S] [Algebra c'.F S] [CommRing T] [Algebra c'.F T] (φ : S →ₐ[c'.F] T) :
    Res hle S →ₐ[c.F] Res hle T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (incl hle a) }

theorem frMap_down {S T : Type} [CommRing S] [Algebra c'.F S] [CommRing T] [Algebra c'.F T] (φ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (resHom hle φ) (ptDown hle y) (ptDown hle z) ↔ FrMap φ y z := Iff.rfl

theorem finite_incl : letI := (incl hle).toAlgebra; Module.Finite c.F c'.F := by
  letI := (incl hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  exact Module.Finite.of_restrictScalars_finite ℚ c.F c'.F

theorem exists_testRing_res (q : TRing c'.F) : ∃ p : TRing c.F, Nonempty (p.R ≃ₐ[c.F] Res hle q.R) := by
  obtain ⟨hft, hred⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c'.F).2 q
  letI := (incl hle).toAlgebra
  haveI := finite_incl hle
  letI : Algebra c'.F (Res hle q.R) := inferInstanceAs (Algebra c'.F q.R)
  haveI : IsScalarTower c.F c'.F (Res hle q.R) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType c'.F (Res hle q.R) := hft
  exact (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 _ (Algebra.FiniteType.trans (S := c'.F) inferInstance this) hred

theorem fromT_down_test (hBC : HasBC Xo c) (q : TRing c'.F) (y : FrPt Xo c' q.R) : FromT (ptDown hle y) := by
  obtain ⟨p, ⟨e⟩⟩ := exists_testRing_res hle q
  obtain ⟨z, hz⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y)
  exact ⟨p, e, z, map_cancel hBC (by ext; simp) hz (GlobalTheory.Frames.frMapUniq_refl _)⟩

theorem fromT_down_iff (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FromT (ptDown hle y) ↔ FromT y := by
  constructor
  · rintro ⟨p, φ, y₀, h⟩
    letI := (incl hle).toAlgebra
    obtain ⟨q, α, hα, hu, -⟩ := exists_testRing_ext (K' := c'.F) p
    obtain ⟨β, hβ⟩ := hu S φ.toRingHom φ.commutes
    let α' : p.R →ₐ[c.F] Res hle q.R := { α with commutes' := hα }
    obtain ⟨z, hz⟩ := hBC _ _ α' y₀
    exact ⟨q, β, ptUp hle z, map_cancel hBC (β := resHom hle β) (AlgHom.ext hβ) hz h⟩
  · rintro ⟨q, φ, y₀, h⟩
    obtain ⟨p, ψ, z, hz⟩ := fromT_down_test hle hBC q y₀
    exact ⟨p, _, z, map_trans ψ (resHom hle φ) hz h⟩

theorem evR_ruleUp (hWD : ValueWD Xo c) (hBC : HasBC Xo c) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S]
    [Algebra c'.F S] (y : FrPt Xo c' S) : evR Xo c' (ruleUp hle f) y = unRes (evR Xo c f (ptDown hle y)) := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, h, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_down_test hle hBC q y₀) ((frMap_down hle φ y₀ y).2 h)]
    rfl
  · rw [evR_not hy, evR_not (fun h => hy ((fromT_down_iff hle hBC y).1 h)), map_zero]

theorem ruleUp_mem_sec (hWD : ValueWD Xo c) (hBC : HasBC Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : ruleUp hle f ∈ sec Xo c' a n := by
  refine ⟨fun p q φ y z h => ?_, fun q t y y' h => ?_⟩
  · exact evR_map hWD hf.1 (fromT_down_test hle hBC p y) ((frMap_down hle φ y z).2 h)
  · obtain ⟨p, ⟨e⟩⟩ := exists_testRing_res hle q
    obtain ⟨z, hz⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y)
    obtain ⟨z', hz'⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y')
    have he : (e : p.R →ₐ[c.F] Res hle q.R).comp (e.symm : Res hle q.R →ₐ[c.F] p.R) = AlgHom.id _ _ := by
      ext; simp
    have hb : FrBor (c := c) (S := Res hle q.R) t (ptDown hle y) (ptDown hle y') := h
    have hw := hf.2 p _ z z' (frBor_map hb hz hz')
    have e1 := evR_of_map hWD hf.1 (map_cancel hBC he hz (GlobalTheory.Frames.frMapUniq_refl _))
    have e2 := evR_of_map hWD hf.1 (map_cancel hBC he hz' (GlobalTheory.Frames.frMapUniq_refl _))
    have e3 : evR Xo c f (ptDown hle y') = wchar (S := Res hle q.R) (ex Dw a n) t * evR Xo c f (ptDown hle y) := by
      rw [e1, e2, hw, map_mul]
      congr 1
      unfold wchar
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow]
      exact congrArg (· ^ _) (e.apply_symm_apply _)
    exact e3

variable {r : ℕ}

end GlobalTheory.CoefChangeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.RankOneDatum

theorem selfDual_of_perfect {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Submodule (𝓞 E) E) (ξ : E)
    (hfg : A.FG) (hne : A ≠ ⊥)
    (h : ∀ x : E, (∀ a ∈ A, ∀ b ∈ A, ∃ z : ℤ,
      Algebra.trace ℚ E (ξ * x * a * IsCMField.complexConj E b) = z) ↔ IsIntegral ℤ x) (x : E) :
    (∀ y ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ A := by
  constructor
  · intro hx
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨A, FractionalIdeal.isFractional_of_fg hfg⟩
    have hI : I ≠ 0 := fun h0 => hne (FractionalIdeal.coeToSubmodule_eq_bot.2 h0)
    have hc : ∀ c ∈ I⁻¹, IsIntegral ℤ (x * c) := fun c hc => (h _).1 fun a ha b hb => by
      have h1 : c * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hc ha
      rw [inv_mul_cancel₀ hI, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨u, hu⟩ := h1
      obtain ⟨n, hn⟩ := hx _ (A.smul_mem (IsCMField.ringOfIntegersComplexConj E u) hb)
      refine ⟨n, ?_⟩
      rw [← hn, Algebra.smul_def]
      congr 1
      have e : algebraMap (𝓞 E) E (IsCMField.ringOfIntegersComplexConj E u) = IsCMField.complexConj E (c * a) := by
        rw [← hu]; rfl
      rw [e, map_mul (IsCMField.complexConj E) _ b, IsCMField.complexConj_apply_apply]
      ring
    have h1 : (1 : E) ∈ I⁻¹ * I := by
      rw [inv_mul_cancel₀ hI]
      exact FractionalIdeal.one_mem_one _
    have h2 : x * 1 ∈ A := by
      refine FractionalIdeal.mul_induction_on (C := fun w => x * w ∈ A) h1 (fun c hc' a ha => ?_)
        (fun u v hu hv => ?_)
      · rw [← mul_assoc]
        exact A.smul_mem (⟨x * c, hc c hc'⟩ : 𝓞 E) ha
      · rw [mul_add]
        exact A.add_mem hu hv
    rwa [mul_one] at h2
  · intro hx y hy
    simpa using (h 1).2 isIntegral_one x hx y hy


set_option maxHeartbeats 1000000 in
theorem exists_datum_of_rt (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD) :
    ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 := by
  obtain ⟨A, hfg, hne, h⟩ := GlobalTheory.principalDatum_trace_perfect D
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hc : IsCMField.complexConj D.host.E D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hφ]
    simp
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
  have hd : (0 : ℝ) < Real.sqrt D.host.d := by
    rw [Real.sqrt_pos, Nat.cast_pos, Nat.pos_iff_ne_zero]
    intro h0
    have h1 := H.sqrt_neg_disc_sq
    rw [hrt0, hφ, h0] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨D₁, -, hp, hq, -⟩ := GlobalTheory.CM.SelfDualDatum.exists_datum D.host.E H A (-D.host.xi0) hfg hne
    (by
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hc, map_neg, map_one, map_natCast, mul_neg, div_neg])
    (fun τ hτ => by
      rw [hrt, hrt0, hφ] at hτ
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hτ, map_neg, map_one, map_natCast]
      generalize Ideal.absNorm D.host.ccK = N at hN ⊢
      generalize Real.sqrt D.host.d = s at hd ⊢
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have e : -(-1 / ((N : ℂ) * (Complex.I * (s : ℂ)))) = ((-(1 / (N * s)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        field_simp
        simp
      rw [e, Complex.mul_I_im, Complex.ofReal_re, neg_lt_zero]
      positivity)
    (fun x => by
      rw [← selfDual_of_perfect A D.host.xi0 hfg hne h x]
      refine forall₂_congr fun y _ => ?_
      rw [neg_mul, neg_mul, map_neg]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, hn]⟩)
  exact ⟨D₁, hp, hq⟩

theorem exists_datum_rank_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 :=
  fun D H _ _ _ h _ => exists_datum_of_rt D H h.rt h.rt0

end GlobalTheory.RankOneDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isProjBy :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ L : LB A.left, L.IsLB → ∃ t : LB.Gen (Theta A L), t.IsGen := by
  intro k _ _ A _ hA hP L hL
  have := hA.comm
  have := hA.geomConnected
  have gi : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have conn : ConnectedSpace A.left := by
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have x : (Sp k : Scheme.{0}) := (default : PrimeSpectrum k)
    have h := A.hom.isConnected_preimage_singleton x
    have e : A.hom ⁻¹' {x} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [e] at h
    exact connectedSpace_iff_univ.2 h
  have face : ∀ {Z : Over (Sp k)} (r : Z ⟶ G3 A) (i : Fin 3), r ≫ x3 A i = toUnit Z ≫ η[A] →
      Triv ((Theta A L).pull r.left) := fun {Z} r i h =>
    (CubeGen.triv_pull_iff L (thφ A (x3 A)) thε r.left).2
      (CubeGen.trivAt_of_formal hL _ (CubeGen.prod_face _ i (toUnit Z).left (congrArg (fun q => q.left) h)))
  exact _root_.GlobalTheory.CubeGlue.triv_of_triv_faces k A A A η[A] η[A] η[A] hA.smooth hA.smooth hA.proper hA.proper hP hP gi gi conn
    (Theta A L) (DVR.linComb_isLB _ hL _ _) (face _ 0 (by simp [x3])) (face _ 1 (by simp [x3]))
    (face _ 2 (by simp [x3]))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbelianNoTorsion

theorem finite_points_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  intro k _ _ A _ hA n hn hnk htor
  obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  have hpk : (p : k) ≠ 0 := fun h => hnk (by rw [Nat.cast_mul, h, zero_mul])
  have hfin : Finite (⊤ : Subgroup (𝟙_ (Over (Sp k)) ⟶ A)) :=
    GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.abMulN_holds k A p hA hp hpk ⊤ Set.univ
      isClosed_univ (fun x => ⟨fun _ => Set.subset_univ _, fun _ => Subgroup.mem_top x⟩)
      (fun x _ hx => htor x (by rw [pow_mul, hx, one_pow]))
  exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv

end GlobalTheory.AbelianNoTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
section
namespace GlobalTheory.IntegralFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem intAll : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.IntAll Xo c := by
  intro hI hA hB hT E _ _ _ H Dw l Xo c hpq hg
  exact Formalism.L2.PjFree.intAll_of' (_root_.GlobalTheory.Exist.intFrExt_of_good hI hA hB hT E H Dw l Xo c hpq hg)
    (fun S S' _ _ _ _ φ y => _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S S' φ y)
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw')
    (_root_.GlobalTheory.IntRebase.intRebase hB E H Dw l Xo c)

end GlobalTheory.IntegralFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralAlgebraicFramedPointExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem integralAlgebraicFramedPoint_exists : PartI → N1ab → N1c → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrNe Xo c (Formalism.L2.PjFree.algCls Xo c) :=
  fun hP hab hc hB hT E _ _ _ H Dw l Xo c hpq hg =>
    intFrNe_of (_root_.GlobalTheory.algPtLa_moduli hc E H Dw l Xo c hpq) (_root_.GlobalTheory.Exist.intFrExt_of_good hP hab hB hT E H Dw l Xo c hpq hg)

end GlobalTheory
end

