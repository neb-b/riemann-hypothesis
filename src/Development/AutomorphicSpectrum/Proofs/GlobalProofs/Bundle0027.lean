module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

section U
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPiU (ι : Type) (u : Rˣ) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := Units.mulLeft u
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem mulPiU_apply (ι : Type) (u : Rˣ) (x : ι → R) (i : ι) :
    mulPiU R ι u x i = (u : R) * x i := rfl

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι u) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => (u : R) * y) (continuous_const.mul continuous_id).measurable c h

theorem coordK_map_unit (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (GlobalTheory.CompanionTheory.SW.coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) (u : R) * y) =
      (c ^ d) • GlobalTheory.CompanionTheory.SW.coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPiU (ι := Fin d) R lam u c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPiU R (Fin d) u) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPiU_apply, ← Algebra.smul_def, map_smul]
    rfl

end U

theorem coordW_map_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  intro F E _ _ _ _ _ σ hσ M d b lam hlam t ht c h
  obtain ⟨j1, j2, j3, j4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  obtain ⟨u, rfl⟩ := ht
  set f : Ainf F ⊗[F] E → Ainf F ⊗[F] E := fun y => algebraMap (Ainf F) (Ainf F ⊗[F] E) (u : Ainf F) * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map_unit (Ainf F) σ hσ b lam u c h
  have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one, ← pow_mul] at hk2
  exact hk2

end GlobalTheory.CompanionTheory.SW.Dil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

section Abstract

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

theorem integral_indicator_char_of_trivial (μ : Measure G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : G → ℂ) (h1 : ∀ x ∈ H, χ x = 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = ((μ (H : Set G)).toReal : ℂ) := by
  rw [integral_indicator hH, setIntegral_congr_fun hH (g := fun _ => (1 : ℂ)) (fun x hx => h1 x hx)]
  simp [Measure.real]

theorem integral_indicator_char_of_ne (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {h : G} (hh : h ∈ H) (hne : χ h ≠ 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = 0 := by
  have key : ∀ x, (H : Set G).indicator χ (x + h) = (H : Set G).indicator χ x * χ h := by
    intro x
    by_cases hx : x ∈ H
    · have hxh : x + h ∈ H := H.add_mem hx hh
      rw [Set.indicator_of_mem (by exact hxh), Set.indicator_of_mem (by exact hx), hχ]
    · have hxh : x + h ∉ H := fun hc => hx (by simpa using H.sub_mem hc hh)
      rw [Set.indicator_of_notMem (by exact hxh), Set.indicator_of_notMem (by exact hx), zero_mul]
  have h2 := integral_add_right_eq_self (μ := μ) ((H : Set G).indicator χ) h
  simp only [key] at h2
  rw [integral_mul_const] at h2
  have h3 : (∫ x, (H : Set G).indicator χ x ∂μ) * (χ h - 1) = 0 := by
    rw [mul_sub, h2, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)

end Abstract

variable {F : Type} [Field F] [NumberField F]

def psiF (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def annV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) : Set (Fv F v) :=
  {t | ∀ s ∈ U, psiV F ψ v (s * t) = 1}

def annF (ψ : AddChar (AF F) ℂ) (B : Set (Af F)) : Set (Af F) :=
  {b | ∀ y ∈ B, psiF ψ (y * b) = 1}

def fouInf (ψ : AddChar (AF F) ℂ) (lam : Measure (Ainf F)) (ρ : Ainf F → ℝ) (t : Ainf F) : ℂ :=
  ∫ x, (ρ x : ℂ) * psiInf F ψ (x * t) ∂lam

theorem psiF_add (ψ : AddChar (AF F) ℂ) (x y : Af F) : psiF ψ (x + y) = psiF ψ x * psiF ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiF, h, AddChar.map_add_eq_mul]
  rfl

theorem psiF_zero (ψ : AddChar (AF F) ℂ) : psiF ψ 0 = 1 := by
  have h : pairA F 0 (0 : Af F) = 0 := rfl
  rw [psiF, h, AddChar.map_zero_eq_one]

theorem psiF_singleV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiF ψ (singleV F v s) = psiV F ψ v s := rfl

theorem psi_pairA (ψ : AddChar (AF F) ℂ) (x : Ainf F) (y : Af F) :
    ψ (pairA F x y) = psiInf F ψ x * psiF ψ y := by
  have h : pairA F x y = pairA F x 0 + pairA F 0 y :=
    Prod.ext (add_zero x).symm (zero_add y).symm
  rw [h, AddChar.map_add_eq_mul]
  rfl

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  classical
  have h : singleV F v (0 : Fv F v) = 0 := RestrictedProduct.single_zero _ v
  rw [← psiF_singleV, h, psiF_zero]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y :=
  GlobalTheory.CompanionTheory.SW.PiV.psiV_add ψ v x y

theorem psiV_neg_of_eq_one (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {x : Fv F v}
    (hx : psiV F ψ v x = 1) : psiV F ψ v (-x) = 1 := by
  have h := psiV_add ψ v (-x) x
  rw [neg_add_cancel, psiV_zero, hx, mul_one] at h
  exact h.symm

def annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    AddSubgroup (Fv F v) where
  carrier := annV ψ v U
  add_mem' := by
    intro a b ha hb s hs
    rw [mul_add, psiV_add, ha s hs, hb s hs, one_mul]
  zero_mem' := by
    intro s _
    rw [mul_zero, psiV_zero]
  neg_mem' := by
    intro a ha s hs
    rw [mul_neg]
    exact psiV_neg_of_eq_one ψ v (ha s hs)

theorem coe_annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    (annS ψ v U : Set (Fv F v)) = annV ψ v U := rfl

def boxS (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    AddSubgroup (Af F) where
  carrier := Coef.boxA S fun v => (U v : Set (Fv F v))
  add_mem' := by
    intro a b ha hb
    exact ⟨fun v hv => (U v).add_mem (ha.1 v hv) (hb.1 v hv),
      fun v hv => add_mem (ha.2 v hv) (hb.2 v hv)⟩
  zero_mem' := ⟨fun v _ => (U v).zero_mem, fun v _ => zero_mem _⟩
  neg_mem' := by
    intro a ha
    exact ⟨fun v hv => (U v).neg_mem (ha.1 v hv),
      fun v hv => neg_mem (ha.2 v hv)⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

theorem placesCountable (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PureCIsSchwartzBruhat
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : R ⊗[F] E ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem repr_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

end Coord

section Box

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_box (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v, IsCompact (C v))
    (hS : ∀ v, v ∉ S → C v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    IsCompact {y : Af F | ∀ v, y v ∈ C v} := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hF : Filter.cofinite ≤ Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hF
  have hcoe := RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)
  let K : Set (RestrictedProduct R A (Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ))) :=
    {x | ∀ v, x v ∈ C v}
  have hK : IsCompact K := by
    rw [hcoe.isCompact_iff]
    have : (DFunLike.coe '' K : Set (∀ v, R v)) = Set.pi Set.univ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hx
        refine ⟨⟨x, Filter.eventually_principal.2 fun v hv => hS v hv (hx v (Set.mem_univ v))⟩,
          fun v => hx v (Set.mem_univ v), rfl⟩
    rw [this]
    exact isCompact_univ_pi hC
  have himg := hK.image hemb.continuous
  have hset : {y : Af F | ∀ v, y v ∈ C v} = RestrictedProduct.inclusion R A hF '' K := by
    ext y
    constructor
    · intro hy
      have hy' : ∀ᶠ v in Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), y v ∈ A v :=
        Filter.eventually_principal.2 fun v hv => hS v hv (hy v)
      exact ⟨⟨y, hy'⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩ v
      exact hx v
  rw [hset]
  exact himg

end Box

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E))


end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

