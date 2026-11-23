module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FubiniFourierHermitianIntegral
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Abstract

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem fubini_unimod {dy : Measure Y} {dx : Measure X} [SFinite dy] [SFinite dx] {f : Y → ℂ} {g : X → ℂ}
    (hf : Integrable f dy) (hg : Integrable g dx) {u : Y → X → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (dy.prod dx)) (hn : ∀ y x, ‖u y x‖ = 1) :
    ∫ y, f y * ∫ x, g x * u y x ∂dx ∂dy = ∫ x, g x * ∫ y, f y * u y x ∂dy ∂dx := by
  have h0 : Integrable (fun z : Y × X => f z.1 * g z.2) (dy.prod dx) := hf.mul_prod hg
  have hint : Integrable (Function.uncurry fun y x => f y * (g x * u y x)) (dy.prod dx) := by
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine (h0.aestronglyMeasurable.mul hu).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hn, mul_one, le_refl]
  have hL : ∀ y, f y * ∫ x, g x * u y x ∂dx = ∫ x, f y * (g x * u y x) ∂dx := fun y =>
    (integral_const_mul _ _).symm
  have hR : ∀ x, g x * ∫ y, f y * u y x ∂dy = ∫ y, f y * (g x * u y x) ∂dy := fun x => by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hint

end Abstract

section Pair

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem pairHerm_sub (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S A B : HermR R σ n) :
    pairHerm R σ n S (A - B) = pairHerm R σ n S A - pairHerm R σ n S B := by
  simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]

theorem half_trace_mul_eq_pairHerm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem half_trace_mul_eq_pairHerm' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  rw [Matrix.trace_mul_comm]
  exact half_trace_mul_eq_pairHerm R σ S G

theorem continuous_pairHerm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module.Finite F E] (σ : E →ₐ[F] E) (n : ℕ) :
    Continuous fun z : HermR R σ n × HermR R σ n => pairHerm R σ n z.1 z.2 := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing R
  unfold pairHerm
  refine continuous_const.mul ((GlobalTheory.CompanionTheory.SW.TopK.continuous_trace R).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem b a)

end Pair

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_pairHerm_gramH_sub (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hg : Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) (c : HermR R σ n) :
    Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2 - c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp := continuous_pairHerm (F := F) (E := E) R σ n
  have hgH : Continuous fun x : Fin n → Fin M → R ⊗[F] E => gramH hCM hJ R x :=
    Continuous.subtype_mk hg _
  have m1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, gramH hCM hJ R z.2) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst (hgH.comp continuous_snd)
  have m2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, c) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst continuous_const
  have h1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2) := by
    have h := hp.comp m1
    exact h
  have h2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) => pairHerm R σ n z.1 c := by
    have h := hp.comp m2
    exact h
  have := h1.sub h2
  refine this.congr fun z => ?_
  exact (pairHerm_sub R σ z.1 _ c).symm

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chiT_eq (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c) (y : HermR (AF F) σ n) :
    chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := by
  rw [← half_trace_mul_eq_pairHerm' (AF F) σ y (hermOf (AF F) σ T hT)]
  rfl

theorem psi_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x))) * chiT σ ψ T y =
    ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) := by
  have h2 : algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) :=
    half_trace_mul_eq_pairHerm (AF F) σ y (gramH hCM hJ (AF F) x)
  rw [h2, chiT_eq σ ψ T hT, ← AddChar.map_add_eq_mul, pairHerm_sub, sub_eq_add_neg]

theorem starN_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) :
    GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y =
      ∫ x, Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := by
  rw [GlobalTheory.CompanionTheory.SiegelND.starN, ← integral_mul_const]
  congr 1
  funext x
  rw [mul_assoc, psi_mul_chiT hCM hJ ψ T hT]

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN_fouH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ M J hJ n hCM ψ hψ dx db _ _ Φ hΦ τ hTh hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hψc, hψn, -⟩ := hψ
  have hpc := continuous_pairHerm_gramH_sub (AF F) hCM hJ (hg n M J) (hermOf (AF F) σ T hT)
  refine ⟨?_, ?_⟩
  · have hp := continuous_pairHerm (F := F) (E := E) (AF F) σ n
    have m : Continuous fun y : HermR (AF F) σ n =>
        ((y, hermOf (AF F) σ T hT) : HermR (AF F) σ n × HermR (AF F) σ n) :=
      Continuous.prodMk continuous_id continuous_const
    have h1 := (hp.comp m).neg
    have h2 := hψc.comp h1
    have : GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T =
        fun y => ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := funext (chiT_eq σ ψ T hT)
    rw [this]
    exact h2
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (y : HermR (AF F) σ n)
        (x : Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT))) (db.prod dx) :=
      (hψc.comp hpc).aestronglyMeasurable
    have key := fubini_unimod hTh hΦ hmeas (fun y x => hψn _)
    have hL : ∀ y, fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) =
        fouH σ ψ db τ y * ∫ x, Φ x *
          ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := fun y => by
      rw [starN_mul_chiT hCM hJ ψ dx Φ T hT y]
    have hR : ∀ x, ∫ y, fouH σ ψ db τ y *
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂db =
        τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) := fun x => by
      rw [hinv, neg_sub]
    simp_rw [hL]
    rw [key]
    simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainSplitCentreProduct
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
abbrev splitFd : Set (GA E a) :=
  (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
    (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)

theorem coe_rationalGLOne_mem_latticeGL (δ : rationalGLOne (K := E) (n := a)) :
    ((δ : normOneGL (K := E) (n := a)) : GA E a) ∈ latticeGL E a := by
  obtain ⟨γ, hγ⟩ : ((δ : normOneGL (K := E) (n := a)) : GA E a) ∈ AdelicGLn.rationalGL E a := δ.2
  rw [← hγ]
  exact ratGL_mem_latticeGL γ

theorem splitCentre_mul_mul_swap (s t : ℝ) (d x : GA E a) :
    splitCentre E a s * splitCentre E a t * (d * x) = d * splitCentre E a s * (splitCentre E a t * x) := by
  simp only [mul_assoc]
  rw [← mul_assoc (splitCentre E a t) d x, splitCentre_comm t d, mul_assoc d, ← mul_assoc (splitCentre E a s) d,
    splitCentre_comm s d, mul_assoc]

theorem exists_lattice_smul_mem_splitFd (ha : 0 < a) (g : GA E a) :
    ∃ l : latticeGL E a, l • g ∈ splitFd E a := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨⟨x, t⟩, rfl⟩ := e.surjective g
  rw [he]
  obtain ⟨δ, hδ, -⟩ := RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne (K := E) (n := a)) x
  have hn : splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) ∈ latticeGL E a := by
    rw [splitCentre_intCast]
    exact zpow_mem_latticeGL _
  refine ⟨⟨((δ : normOneGL (K := E) (n := a)) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ),
    mul_mem (coe_rationalGLOne_mem_latticeGL δ) hn⟩, ⟨δ • x, Int.fract t⟩,
    ⟨hδ, Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
  change splitCentre E a (Int.fract t) * (((δ : normOneGL (K := E) (n := a)) : GA E a) * (x : GA E a)) =
    ((δ : normOneGL (K := E) (n := a)) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) * (splitCentre E a t * (x : GA E a))
  have hf : Int.fract t = ((-⌊t⌋ : ℤ) : ℝ) + t := by
    rw [Int.fract]
    push_cast
    ring
  rw [hf, splitCentre_add, splitCentre_mul_mul_swap]

theorem eq_one_of_mul_mem_splitFd (ha : 0 < a) {l g : GA E a} (hl : l ∈ latticeGL E a) (hg : g ∈ splitFd E a)
    (h : l * g ∈ splitFd E a) : l = 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨γ, m, rfl⟩ := mem_latticeGL_iff.1 hl
  obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩ := hg
  obtain ⟨⟨y, u⟩, ⟨hy, hu⟩, hyu⟩ := h
  dsimp only at hx hs hy hu hyu
  have hγ : ratGL E a γ ∈ normOneGL (K := E) (n := a) := rationalGL_le_normOneGL ⟨γ, rfl⟩
  have key : e (y, u) = e (⟨ratGL E a γ, hγ⟩ * x, (m : ℝ) + s) := by
    rw [he, he, hyu, splitCentre_add, ← splitCentre_intCast]
    exact (splitCentre_mul_mul_swap (m : ℝ) s (ratGL E a γ) (x : GA E a)).symm
  obtain ⟨h1, h2⟩ := Prod.mk.inj (e.injective key)
  have hm : m = 0 := by
    have h3 : (m : ℝ) < 1 := by linarith [hs.1, hu.2]
    have h4 : (-1 : ℝ) < m := by linarith [hs.2, hu.1]
    have h5 : m < 1 := by exact_mod_cast h3
    have h6 : -1 < m := by exact_mod_cast h4
    omega
  subst hm
  let δ : rationalGLOne (K := E) (n := a) := ⟨⟨ratGL E a γ, hγ⟩, ⟨γ, rfl⟩⟩
  have h7 : δ = 1 := (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne (K := E) (n := a)) x).unique
    (show δ • x ∈ _ from by
      change ((⟨ratGL E a γ, hγ⟩ : normOneGL (K := E) (n := a)) * x) ∈ _
      rw [← h1]
      exact hy) (by simpa using hx)
  have h8 : ratGL E a γ = 1 := congrArg (fun d : rationalGLOne (K := E) (n := a) => ((d : normOneGL (K := E) (n := a)) : GA E a)) h7
  rw [h8, zpow_zero, mul_one]

theorem measurableSet_splitFd (ha : 0 < a) : MeasurableSet (splitFd E a) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have h : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e :=
    funext fun p => (he p.1 p.2).symm
  rw [splitFd, h]
  exact e.isClosedEmbedding.measurableEmbedding.measurableSet_image.2
    ((RightCosetSpace.measurableSet_fundamentalDomain _).prod measurableSet_Ico)

theorem isFundamentalDomain_splitFd : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a)
      ((fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
        (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  intro E _ _ _ a ha μ _
  refine IsFundamentalDomain.mk' (measurableSet_splitFd ha).nullMeasurableSet fun g => ?_
  obtain ⟨l, hl⟩ := exists_lattice_smul_mem_splitFd ha g
  refine ⟨l, hl, fun l' hl' => ?_⟩
  have h1 : ((l' : GA E a) * (l : GA E a)⁻¹) * ((l : GA E a) * g) ∈ splitFd E a := by
    have e0 : (l' : GA E a) * (l : GA E a)⁻¹ * ((l : GA E a) * g) = (l' : GA E a) * g := by group
    rw [e0]
    exact hl'
  have h2 := eq_one_of_mul_mem_splitFd ha (mul_mem l'.2 (inv_mem l.2)) hl h1
  exact Subtype.ext (mul_inv_eq_one.1 h2)

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesOfPoitouTate
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles.Assembly

theorem arith {a s p1 b h1 lam p2 h2 h0' q0 h0 m arch : ℕ}
    (h4 : a * s * p1 = b * h1 * lam) (h5 : s * p2 = h2 * h0') (h6 : p1 = q0 * p2 * m)
    (h7 : h0 * h2 * m = h1 * arch) (hh1 : 0 < h1) :
    a * h0' * q0 * arch = b * h0 * lam := by
  apply Nat.eq_of_mul_eq_mul_right hh1
  calc a * h0' * q0 * arch * h1 = a * h0' * q0 * (h1 * arch) := by ring
    _ = a * h0' * q0 * (h0 * h2 * m) := by rw [h7]
    _ = h0 * (a * (h2 * h0') * q0 * m) := by ring
    _ = h0 * (a * (s * p2) * q0 * m) := by rw [h5]
    _ = h0 * (a * s * (q0 * p2 * m)) := by ring
    _ = h0 * (a * s * p1) := by rw [h6]
    _ = h0 * (b * h1 * lam) := by rw [h4]
    _ = b * h0 * lam * h1 := by ring

theorem card_pi_submodule {R ι : Type} [Semiring R] [Fintype ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)] (L : ∀ i, Submodule R (X i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
      invFun := fun y => ⟨fun i => (y i).1, fun i _ => (y i).2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem greenbergWiles_of_poitouTate : PoitouTateNormalised → GlobalEulerChar → LocalTateDuality →
    LocalEulerChar → LocalFiniteness → GreenbergWiles := by
  intro hPT hGEC hLTD hLEC hLF
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hl hS hρ μ hμ Av hAv c hc L
  classical
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfinD : Finite (TDual (ZMod (l ^ r)) M) := GlobalTheory.CompanionTheory.DualFin.finite_dual_all (ZMod (l ^ r)) M
  obtain ⟨inv, hinv, hnine, hsha⟩ :=
    GlobalTheory.CompanionTheory.GreenbergWiles.poitouTate_instance F Ω l r M S Av μ ρ hρ hμ hPT hl hr hS hAv
  have hρ' : ContAction (twDual μ ρ) := _root_.GlobalTheory.CompanionTheory.GalDual.contAction_twDual F Ω l r M S Av μ ρ hρ hμ
  have hj : ∀ v, Function.Injective (invAt S Av μ hμ inv v) := fun v =>
    ((hinv _ _ (hAv v)).comp (toMuLoc_bijective S Av μ hμ v)).injective
  have hlf := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hLF hr hAv
  have hlf' := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r (TDual (ZMod (l ^ r)) M)
    S Av μ (twDual μ ρ) hρ' hLF hr hAv
  haveI : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v => (hlf v).2.1
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S Av v))) := fun v => (hlf v).2.2
  haveI : ∀ v : S, Finite (H1 ((twDual μ ρ).comp (locFam S Av v))) := fun v => (hlf' v).2.1
  obtain ⟨hH0, hH1, hH2, hH0', hH1'⟩ := _root_.GlobalTheory.CompanionTheory.GaloisCoh.global_finite_of_poitouTate F Ω l r M S Av μ ρ hρ
    (invAt S Av μ hμ inv) hμ hfinD hLF hr hAv hnine hsha
  have hloc := GlobalTheory.T.galois_cohomology_localization_exact F Ω l r M S Av μ ρ hρ hμ hLTD hr inv hinv hAv
  have hB := GlobalTheory.CompanionTheory.Pairing.sum_perfect (ZMod (l ^ r)) S (fun v => H1 (ρ.comp (locFam S Av v)))
    (fun v => H1 ((twDual μ ρ).comp (locFam S Av v)))
    (fun v => (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂
      (invAt S Av μ hμ inv v)) (fun v => (hloc v).1) (fun v => (hloc v).2)
  have hBi : Function.Injective (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ) := by
    unfold sumPair; rw [LinearMap.coe_sum]; exact hB.1
  have hBf : Function.Injective (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ).flip := by
    unfold sumPair; exact hB.2
  have hrange := GlobalTheory.T.tate_shafarevich_duality_h1 F Ω l r M S Av μ ρ hρ (invAt S Av μ hμ inv) hnine
  have count := GlobalTheory.CompanionTheory.Counting.card_comap_mul_card_ker_mul_card_eq (l ^ r) (H1 ρ)
    (H1 (twDual μ ρ)) (∀ v : S, H1 (ρ.comp (locFam S Av v)))
    (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v)))
    (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ) hBi hBf (loc1 S Av ρ) (loc1 S Av (twDual μ ρ))
    hrange (Submodule.pi Set.univ L)
  have hsel := GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ
  have hsel' := GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r (TDual (ZMod (l ^ r)) M) S Av μ
    (twDual μ ρ) hρ'
  rw [← GlobalTheory.CompanionTheory.Duality.pi_perpCond_eq_annihilator_sumPair F Ω l r M S Av μ ρ hρ _ hj L,
    ← hsel.1 L, ← hsel'.1, ← hsel'.2.1, card_pi_submodule L, hsha.1.2.2.2] at count
  have h5 := _root_.GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2 F Ω l r M S Av μ ρ hρ (invAt S Av μ hμ inv) hLF hr hAv hnine hH2 hH0'
  have h7 := hGEC F Ω l r M S ρ hr hS hρ c hc
  have hdeg : ∑ v : S, (if ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then locDeg v.1 else 0) =
      Module.finrank ℚ F := by
    rw [← _root_.GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank F l (S.filter fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
      (fun v => by rw [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hS v h, h⟩⟩),
      Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0)
  have hle := GlobalTheory.CompanionTheory.Gal.localEuler_places F Ω l r M S Av μ ρ hρ hLEC hr hAv
  have h6 : Nat.card (∀ v : S, H1 (ρ.comp (locFam S Av v))) =
      (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) *
        Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) * Nat.card M ^ Module.finrank ℚ F := by
    have hv : ∀ v : S, Nat.card (H1 (ρ.comp (locFam S Av v))) =
        Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v))) *
          Nat.card M ^ (if ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then locDeg v.1 else 0) := by
      intro v
      split_ifs with h
      · exact (hle v).1 h
      · rw [pow_zero, mul_one]; exact (hle v).2 h
    rw [Nat.card_pi, Nat.card_pi, Finset.prod_congr rfl (fun v _ => hv v),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  exact arith count h5 h6 h7 Nat.card_pos

end GlobalTheory.CompanionTheory.GreenbergWiles.Assembly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedImageOfSobolevLower
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob

namespace GlobalTheory.CompanionTheory.SmoothClosed

theorem smoothVec_sub {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {u v : H}
    (hu : SmoothVec Lie σ u) (hv : SmoothVec Lie σ v) : SmoothVec Lie σ (u - v) := by
  intro k Xs hX
  simpa only [map_sub] using (hu k Xs hX).sub (hv k Xs hX)

theorem tendsto_seminorm_sub {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {q : Seminorm ℂ E} (hq : Continuous q) {u : ℕ → E} {y : E} (hu : Filter.Tendsto u Filter.atTop (nhds y)) :
    Filter.Tendsto (fun k => q (u k - y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k => u k - y) Filter.atTop (nhds (y - y)) := hu.sub_const y
  rw [sub_self] at h
  simpa [Function.comp_def, map_zero] using (hq.tendsto 0).comp h

theorem isClosed_image_of_sobolev_lower : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ → ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w)) → IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hmod T hT hlow
  haveI : FirstCountableTopology E := hmod.withSeminorms.firstCountableTopology
  refine IsSeqClosed.isClosed ?_
  intro x y hx hxy
  choose w hw hTw using hx
  have hcauchy : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ := by
    intro S hS δ hδ
    obtain ⟨q, hq, hqb⟩ := hlow S hS
    have ht := tendsto_seminorm_sub hq hxy
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hδ)))
    refine ⟨K, fun k hk m hm => ?_⟩
    calc sobNorm σ S (w k - w m) ≤ q (T (w k - w m)) := hqb _ (smoothVec_sub (hw k) (hw m))
      _ = q ((x k - y) - (x m - y)) := by rw [T.map_sub, hTw, hTw, sub_sub_sub_cancel_right]
      _ ≤ q (x k - y) + q (x m - y) := map_sub_le_add q _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hK k hk) (hK m hm)
      _ = δ := add_halves δ
  obtain ⟨w0, hw0, hconv⟩ := GlobalTheory.CompanionTheory.SobComplete.smoothVec_complete n ε H σ hU hI w hw hcauchy
  refine ⟨w0, hw0, ?_⟩
  obtain ⟨-, hT2⟩ := hT
  have hT' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds (T w0)) := by
    refine (hmod.withSeminorms.tendsto_nhds _ _).2 ?_
    intro i δ hδ
    obtain ⟨S, C, hS, hb⟩ := hT2 i
    have hC : Filter.Tendsto (fun k => C * sobNorm σ S (w k - w0)) Filter.atTop (nhds 0) := by
      simpa using (hconv S hS).const_mul C
    filter_upwards [hC.eventually (gt_mem_nhds hδ)] with k hk
    calc p i (T (w k) - T w0) = p i (T (w k - w0)) := by rw [T.map_sub]
      _ ≤ C * sobNorm σ S (w k - w0) := hb _ (smoothVec_sub (hw k) hw0)
      _ < δ := hk
  have hx' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds y) := by
    simp only [hTw]
    exact hxy
  exact tendsto_nhds_unique hT' hx'

end GlobalTheory.CompanionTheory.SmoothClosed

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundCompactStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_points_height_bound_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω := by
  exact @GlobalTheory.CompanionTheory.RedCov.MahlerU.mahler_unitary_set
end

