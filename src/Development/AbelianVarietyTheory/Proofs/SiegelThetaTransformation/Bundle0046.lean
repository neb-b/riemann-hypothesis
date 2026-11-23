module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
section
namespace GlobalTheory.Ker.Mov

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.SW
open scoped TensorProduct Matrix nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def Into (F : Type) [Field F] [NumberField F] [Algebra F E] (m : Matrix (Fin n) (Fin n) (RA F E))
    (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ z ∈ hat F (L : Set (Fin n → E)), m *ᵥ z ∈ hat F (L' : Set (Fin n → E))

def Onto (F : Type) [Field F] [NumberField F] [Algebra F E] (m : Matrix (Fin n) (Fin n) (RA F E))
    (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ u, u ∈ hat F (L' : Set (Fin n → E)) ↔ ∃ u₀ ∈ hat F (L : Set (Fin n → E)), u = m *ᵥ u₀

theorem into_of_fv {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ x ∈ L, m *ᵥ fv F x ∈ hat F (L' : Set (Fin n → E))) : Into F m L L' :=
  fun _ hz => mulVec_mem_hat (L := L') (fun x hx => h x hx) hz

theorem onto_iff {m m' : Matrix (Fin n) (Fin n) (RA F E)} (h : m * m' = 1)
    {L L' : Submodule (𝓞 E) (Fin n → E)} : Onto F m L L' ↔ Into F m L L' ∧ Into F m' L' L := by
  have h' : m' * m = 1 := mul_eq_one_comm.1 h
  constructor
  · intro H
    refine ⟨fun z hz => (H _).2 ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    obtain ⟨u, hu, rfl⟩ := (H _).1 hz
    rwa [Matrix.mulVec_mulVec, h', Matrix.one_mulVec]
  · rintro ⟨H, H'⟩ u
    constructor
    · intro hu
      exact ⟨m' *ᵥ u, H' u hu, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, rfl⟩
      exact H u hu

omit [NumberField E] in
theorem map_mulVec_fv (P : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (P.map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *ᵥ fv F x = fv F (P *ᵥ x) := by
  funext i
  simp [fv, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

omit [NumberField E] in
theorem fv_eq_zero {x : Fin n → E} (h : fv F x = 0) : x = 0 := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    exact zero_ne_one h2
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective
  funext i
  apply hinj
  rw [Pi.zero_apply, map_zero]
  exact congrFun h i

theorem onto_mapL (g : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Onto F ((g : Matrix (Fin n) (Fin n) E).map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E))
      L (mapL g L) := by
  have hm : ((g : Matrix (Fin n) (Fin n) E).map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *
      (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
        fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) = 1 := by
    have := Matrix.map_mul (L := (g : Matrix (Fin n) (Fin n) E))
      (M := ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom)
    rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  refine (onto_iff hm).2 ⟨into_of_fv fun x hx => ?_, into_of_fv ?_⟩
  · rw [map_mulVec_fv]
    exact fv_mem_hat ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [map_mulVec_fv]
    refine fv_mem_hat ?_
    change ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ L
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem span_eq_top_of_into {m m' : Matrix (Fin n) (Fin n) (RA F E)} (h : m * m' = 1)
    {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (H : Into F m L L') : Submodule.span E (L' : Set (Fin n → E)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨-, -, -, h4⟩ := hat_rational_points_and_approx F E n L hL hs
  let P : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (LinearMap.pi fun _ => φ)
  have hP : ∀ x, P *ᵥ x = fun _ => φ x := fun x => by
    simp only [P, LinearMap.toMatrix'_mulVec]; rfl
  have hz : ∀ z ∈ hat F (L' : Set (Fin n → E)),
      (P.map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *ᵥ z = 0 := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, x, hx, rfl⟩ := hz
      have hx0 : φ x = 0 := hφ (Submodule.subset_span hx)
      rw [gen_eq, Matrix.mulVec_smul, map_mulVec_fv, hP, hx0]
      exact (congrArg _ fv_zero).trans (smul_zero _)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | neg x _ hx => rw [Matrix.mulVec_neg, hx, neg_zero]
  apply hφ0
  have key : ∀ x, (fun _ : Fin n => φ x) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := h4 (m' *ᵥ fv F x)
    have h1 := hz _ (H _ hdx)
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec (fv F x) m m', h, Matrix.one_mulVec,
      map_mulVec_fv, hP] at h1
    exact fv_eq_zero (F := F) (nsmul_cancel hd (h1.trans (smul_zero d).symm))
  refine (Pi.basisFun E (Fin n)).ext fun i => ?_
  exact congrFun (key _) i

theorem into_smul {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (H : Into F m L L') (𝔞 : Ideal (𝓞 E)) : Into F m (𝔞 • L) (𝔞 • L') := by
  have : 𝔞 • L ≤ pre m (𝔞 • L') := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    rw [mem_pre, show a • x = (a : E) • x from rfl, fv_smul, Matrix.mulVec_smul]
    exact Scale.smul_mem_hat (fun y hy => Submodule.smul_mem_smul ha hy) (H _ (fv_mem_hat hx))
  exact into_of_fv this

theorem into_idq {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (H : Into F m L L') (𝔞 𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥) : Into F m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') := by
  refine into_of_fv fun v hv => ?_
  have hI : ((𝔟 : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hb
  have key : ∀ c ∈ (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔟 : FractionalIdeal (𝓞 E)⁰ E)⁻¹,
      m *ᵥ fv F (c • v) ∈ hat F (idq 𝔞 𝔟 L' : Set (Fin n → E)) := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc ?_ ?_
    · intro a ha c hc
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      rw [mul_comm, mul_smul, fv_smul, Matrix.mulVec_smul]
      refine Scale.smul_mem_hat ?_ (into_smul H 𝔞 _ (fv_mem_hat (hv b hb)))
      intro y hy b' hb'
      have hbc : algebraMap (𝓞 E) E b' * c ∈
          (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔟 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :=
        FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b', hb', rfl⟩) hc
      rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hbc
      obtain ⟨r, hr⟩ := hbc
      have : b' • c • y = r • y := by
        change algebraMap (𝓞 E) E b' • c • y = algebraMap (𝓞 E) E r • y
        rw [smul_smul, hr]
      rw [this]
      exact Submodule.smul_mem _ r hy
    · intro x y hx hy
      rw [add_smul, fv_add, Matrix.mulVec_add]
      exact add_mem hx hy
  have := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  rwa [one_smul] at this

theorem idq_fg {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (𝔞 𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥) :
    (idq 𝔞 𝔟 L).FG := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hb' : algebraMap (𝓞 E) E b ≠ 0 := fun h => hb0 (RingOfIntegers.coe_injective (by simpa using h))
  have hinj : Function.Injective (b • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
    intro x y hxy
    exact smul_right_injective _ hb' hxy
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hle : (idq 𝔞 𝔟 L).map (b • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_le_right (hx b hb)
  have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
  exact (isNoetherian_submodule.1 this) _ hle

theorem idq_span {L : Submodule (𝓞 E) (Fin n → E)} (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (𝔞 𝔟 : Ideal (𝓞 E)) (ha : 𝔞 ≠ ⊥) : Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E)) = ⊤ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  have ha' : algebraMap (𝓞 E) E a ≠ 0 := fun h => ha0 (RingOfIntegers.coe_injective (by simpa using h))
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  have h1 : algebraMap (𝓞 E) E a • x ∈ idq 𝔞 𝔟 L := fun b _ =>
    Submodule.smul_mem _ b (Submodule.smul_mem_smul ha hx)
  have := (Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E))).smul_mem (algebraMap (𝓞 E) E a)⁻¹
    (Submodule.subset_span h1)
  rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at this

theorem onto_laws (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (m m' : Matrix (Fin n) (Fin n) (RA F E)) (h : m * m' = 1) :
    (∃ L' : Submodule (𝓞 E) (Fin n → E), (L'.FG ∧ Submodule.span E (L' : Set (Fin n → E)) = ⊤) ∧ Onto F m L L') ∧
    ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → Onto F m L L' →
      Submodule.span E (L' : Set (Fin n → E)) = ⊤ ∧ Onto F m' L' L ∧
      (∀ L'' : Submodule (𝓞 E) (Fin n → E), L''.FG → Onto F m L L'' → L'' = L') ∧
      (∀ m₂ (L'' : Submodule (𝓞 E) (Fin n → E)), Onto F m₂ L' L'' → Onto F (m₂ * m) L L'') ∧
      ∀ 𝔞 𝔟 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Onto F m (𝔞 • L) (𝔞 • L') ∧
        Onto F m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧
        Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E)) = ⊤ := by
  have h' : m' * m = 1 := mul_eq_one_comm.1 h
  constructor
  · obtain ⟨Λ, -, h2, h3, h4⟩ := exists_lattice_latOf F E n L ⟨m, m', h, h'⟩ hL hs
    refine ⟨Λ, ⟨h2, h3⟩, fun u => ?_⟩
    rw [← SetLike.mem_coe, h4]
    exact ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩
  · intro L' hL' H
    obtain ⟨H1, H2⟩ := (onto_iff h).1 H
    have hs' := span_eq_top_of_into h hL hs H1
    refine ⟨hs', (onto_iff h').2 ⟨H2, H1⟩, fun L'' hL'' K => ?_, fun m₂ L'' K u => ?_,
      fun 𝔞 𝔟 ha hb => ⟨(onto_iff h).2 ⟨into_smul H1 𝔞, into_smul H2 𝔞⟩,
        (onto_iff h).2 ⟨into_idq H1 𝔞 𝔟 hb, into_idq H2 𝔞 𝔟 hb⟩, idq_fg hL 𝔞 𝔟 hb, idq_span hs 𝔞 𝔟 ha⟩⟩
    · have hs'' := span_eq_top_of_into h hL hs ((onto_iff h).1 K).1
      ext v
      rw [← (hat_rational_points_and_approx F E n L'' hL'' hs'').1,
        ← (hat_rational_points_and_approx F E n L' hL' hs').1, K, H]
    · rw [K]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨z, hz, rfl⟩ := (H w).1 hw
        exact ⟨z, hz, Matrix.mulVec_mulVec _ _ _⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨m *ᵥ z, H1 z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩

end GlobalTheory.Ker.Mov

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Ker.isMov_laws : ∀ (D : D7) (k : ℕ) (L : Lt D.host.E k), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) → (∀ v, toAf v ∈ hatV L ↔ v ∈ L) ∧ IsMov 1 L L ∧ (∀ ga : GL (Fin k) D.host.E, IsMov ((ga : Matrix (Fin k) (Fin k) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) L (mapL ga L)) ∧ ∀ m m' : Matrix (Fin k) (Fin k) (AfE D), m * m' = 1 → (∃ L' : Lt D.host.E k, (L'.FG ∧ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤) ∧ IsMov m L L') ∧ ∀ L' : Lt D.host.E k, L'.FG → IsMov m L L' → Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤ ∧ IsMov m' L' L ∧ (∀ L'' : Lt D.host.E k, L''.FG → IsMov m L L'' → L'' = L') ∧ (∀ m₂ (L'' : Lt D.host.E k), IsMov m₂ L' L'' → IsMov (m₂ * m) L L'') ∧ ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsMov m (𝔞 • L) (𝔞 • L') ∧ IsMov m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧ Submodule.span D.host.E (idq 𝔞 𝔟 L : Set (Fin k → D.host.E)) = ⊤ := by
  rintro D k L ⟨hL, hs⟩
  refine ⟨(GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E k L hL hs).1, fun u => ?_,
    fun ga => GlobalTheory.Ker.Mov.onto_mapL (F := D.host.F) ga L,
    fun m m' h => GlobalTheory.Ker.Mov.onto_laws (F := D.host.F) L hL hs m m' h⟩
  simp only [Matrix.one_mulVec, exists_eq_right']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussRMulFactor
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.RealHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [GlobalTheory.Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem contDiff_gaussR : ContDiff ℝ (⊤ : ℕ∞) (gaussR X bas idx x : (Fin n → Fin g → ℂ) → ℂ) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => star z) := Complex.conjCLE.contDiff
  have h1 : ∀ (k : Fin n) (i : Fin g), ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => (hMat X bas idx x *ᵥ z k) i := by
    intro k i
    simp only [mulVec, dotProduct]
    fun_prop
  have h2 : ∀ k : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => hx X bas idx x (z k) (z k) := by
    intro k
    change ContDiff ℝ _ fun z : Fin n → Fin g → ℂ => ∑ i, (hMat X bas idx x *ᵥ z k) i *
      ∑ j, imInv X bas idx x i j * star ((hMat X bas idx x *ᵥ z k) j)
    exact ContDiff.sum fun i _ => (h1 k i).mul
      (ContDiff.sum fun j _ => contDiff_const.mul (hc.comp (h1 k j)))
  exact (contDiff_const.mul (ContDiff.sum fun k _ => h2 k)).neg.cexp

theorem gaussR_mul_factor (hsym : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (z a : Fin n → Fin g → ℂ) :
    gaussR X bas idx x z * cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • a k) (a k))) =
      cexp (-(π * I * ((∑ k, hx X bas idx x (z k) (a k)).im : ℝ))) * gaussR X bas idx x (z + a) := by
  have h1 : ∑ k, hx X bas idx x (a k) (z k) = conj (∑ k, hx X bas idx x (z k) (a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsym _ _
  simp only [gaussR, ← Complex.exp_add, Pi.add_apply, hx_add_left, hx_add_right, hx_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1]
  congr 1
  generalize ∑ k, hx X bas idx x (z k) (a k) = S
  have h2 := Complex.sub_conj S
  push_cast at h2
  linear_combination (-(π : ℂ) / 2) * h2

end GlobalTheory.Ker.RealHeis

namespace GlobalTheory.Ker

theorem thR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, IsSB φ → ContDiff ℝ (⊤ : ℕ∞) (thR X bas idx φ x : WR X n → ℂ) ∧ (∀ (y : Matrix (Fin n) (Fin r) E) (v : WR X n), thR X bas idx (heisG X bas y φ) x v = cexp (-(π * I * (EFR X v (embR X y) : ℝ))) * thR X bas idx φ x (v + embR X y)) ∧ (∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, thR X bas idx (wG X bas idx γ φ) (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = thR X bas idx φ x v) ∧ (∀ ψ, IsSB ψ → (thR X bas idx φ x = (thR X bas idx ψ x : WR X n → ℂ) → φ = ψ) ∧ thR X bas idx (φ + ψ) x = (thR X bas idx φ x + thR X bas idx ψ x : WR X n → ℂ)) ∧ ∀ a : ℂ, thR X bas idx (a • φ) x = (a • thR X bas idx φ x : WR X n → ℂ) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hxd φ hφ
  obtain ⟨⟨L, hL⟩, him, -, -, hinv⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x hxd
  obtain ⟨hsym, -, -, -, -, -, -, hga⟩ := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd
  have hLf : zR X idx x = (L : WR X n → Fin n → Fin g → ℂ) := funext fun v => (hL v).symm
  refine ⟨?_, fun y v => ?_, fun γ hγ v => ?_, fun ψ hψ => ⟨fun h => ?_, ?_⟩, fun a => ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (thA X bas idx φ x) :=
      (AnalyticOnNhd.contDiff (𝕜 := ℂ) (SCV.analyticOnNhd_of_differentiable
        (ThetaHol.differentiable_thA idx hs hφ hxd) _)).restrict_scalars ℝ
    have h2 := ((RealHeis.contDiff_gaussR X bas idx x).mul h1).comp L.contDiff
    rw [← hLf] at h2
    exact h2
  · have h1 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hxd (zR X idx x v)
    have h2 : zR X idx x (v + embR X y) = zR X idx x v + zR X idx x (embR X y) := by
      rw [hLf, map_add (f := _)]
    have h3 := RealHeis.gaussR_mul_factor X bas idx x hsym (zR X idx x v) (zR X idx x (embR X y))
    rw [him] at h3
    rw [thR, thR, h1, h2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← h3]
    rfl
  · rw [thR, thR, hinv γ hγ v, (wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hxd]
    simp only [gaussR, (hga γ hγ).2.2.2]
  · have hone : IsUn X (1 : GL (Fin r) E) := fun u w => by simp
    refine ((wG_laws E r X g bas idx n hs hn 1 hone φ hφ).2.2.1 ψ hψ).2.2 x hxd ?_
    funext z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 := congrFun h v
    rw [thR, thR, ← hL] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  · funext v
    simp only [thR, UnAct.thA_add idx hs hxd hφ hψ, Pi.add_apply, mul_add]
  · funext v
    simp only [thR, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LatTens

noncomputable def gen {D : D7} (S T : HSp D) (α : Af D.host.F) :
    Matrix (Fin S.rank) (Fin T.rank) D.host.E →+ WO S T :=
  AddMonoidHom.mk' (fun y => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a)
    fun y y' => Matrix.ext fun a k => TensorProduct.tmul_add _ (y k a) (y' k a)

def vmv {E : Type} [Field E] {n r : ℕ} (v : Fin n → E) : (Fin r → E) →+ Matrix (Fin n) (Fin r) E :=
  AddMonoidHom.mk' (fun u => vecMulVec v u)
    fun u u' => Matrix.ext fun k a => mul_add (v k) (u a) (u' a)

theorem gen_eq {D : D7} (S T : HSp D) (hS : S.gram = 1) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T)
      = gen S T α (vecMulVec (star s) (a • t)) := by
  refine Matrix.ext fun i j => ?_
  simp only [gen, AddMonoidHom.mk'_apply, Matrix.of_apply]
  congr 1
  rw [hS]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem latO_eq_hatA : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (LS Λ : Lt D.host.E S.rank) (LT L : Lt D.host.E T.rank), (∀ v, v ∈ Λ ↔ star v ∈ LS) → IsAA L LT → latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = hatA S T (tens Λ L) := by
  intro D S T C LS Λ LT L hΛ hL
  have hS : S.gram = 1 := C.m.gS

  have hmem : ∀ α : Af D.host.F, α ∈ intAf D.host.F → ∀ a : D.host.E, a ∈ D.host.AA →
      ∀ v : Fin S.rank → D.host.E, v ∈ Λ → ∀ t : Fin T.rank → D.host.E, t ∈ LT →
      gen S T α (vecMulVec v (a • t)) ∈ latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro α hα a ha v hv t ht
    unfold latO
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, fun _ h => absurd trivial h, a, ha, star v, (hΛ v).1 hv, t, ht, ?_⟩
    rw [gen_eq S T hS α a (star v) t, star_star]
  apply le_antisymm
  · unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    rw [gen_eq S T hS α a s t]
    unfold hatA
    apply AddSubgroup.subset_closure
    have hsΛ : star s ∈ Λ := (hΛ (star s)).2 (by rw [star_star]; exact hs)
    have htL : a • t ∈ L := (hL (a • t)).2 (AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩)
    exact ⟨α, hα, vecMulVec (star s) (a • t),
      AddSubgroup.subset_closure ⟨star s, hsΛ, a • t, htL, rfl⟩, rfl⟩
  · unfold hatA
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, y, hy, rfl⟩

    have hT : tens Λ L ≤ (latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap (gen S T α) := by
      unfold tens
      rw [AddSubgroup.closure_le]
      rintro _ ⟨v, hv, u, hu, rfl⟩
      have hL' : AddSubgroup.closure {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ LT, u = a • t} ≤
          (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
            (fun _ => True)).comap ((gen S T α).comp (vmv v)) := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨a, ha, t, ht, rfl⟩
        exact hmem α hα a ha v hv t ht
      exact hL' ((hL u).1 hu)
    exact hT hy

end GlobalTheory.Ker.LatTens
end

