module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProduct
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem pi_const_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (κ : Measure X) [SigmaFinite κ] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • κ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => κ) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem subst_row_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (u : Rˣ) (w : (Fin n → R ⊗[F] E) → HermR R σ n), Measurable w → ∀ f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞, Measurable f → ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D u w hw f hf
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ D.hCM R d b lam D.hlam
  haveI := hK
  haveI := hH n
  have hVU : ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) : R ⊗[F] E) *
      ((u : R) ⊗ₜ[F] (algebraMap F E t)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, inv_mul_cancel₀ D.ht, map_one, Units.inv_mul]
    rfl
  have hTm : Measurable (fun (r : Fin n → R ⊗[F] E) (j : Fin n) =>
      ((u : R) ⊗ₜ[F] (algebraMap F E t)) * r j) :=
    Measurable.of_eval fun j => (measurable_pi_apply j).const_mul _
  have hDm : Measurable (fun (r : Fin n → R ⊗[F] E) (j : Fin n) =>
      (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) :=
    Measurable.of_eval fun j => (measurable_pi_apply j).const_mul _
  have hmap : (Measure.pi fun _ : Fin n => coordK R b lam).map
      (fun (r : Fin n → R ⊗[F] E) (j : Fin n) => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * r j) =
      ((cm u : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => coordK R b lam := by
    have hm : ∀ _ : Fin n, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        cm u • coordK R b lam := fun _ => D.hmod u
    have hsf : ∀ _ : Fin n, SigmaFinite ((coordK R b lam).map
        (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y)) := fun i => by
      rw [hm i]; infer_instance
    have h1 := Measure.pi_map_pi (X := fun _ : Fin n => R ⊗[F] E) (Y := fun _ : Fin n => R ⊗[F] E)
      (hμ := hsf) (μ := fun _ : Fin n => coordK R b lam)
      (f := fun _ y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y)
      (fun _ => (measurable_const_mul _).aemeasurable)
    rw [h1]
    simp only [D.hmod u]
    rw [pi_const_smul, Fintype.card_fin]
  have hh : Measurable (fun r : Fin n → R ⊗[F] E => ∫⁻ S'', f (fun j =>
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n)) := by
    refine Measurable.lintegral_prod_right' (f := fun p : (Fin n → R ⊗[F] E) × HermR R σ n =>
      f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * p.1 j), p.2 - w p.1)) ?_
    exact hf.comp ((hDm.comp measurable_fst).prodMk (measurable_snd.sub (hw.comp measurable_fst)))
  have hsm : ∀ g : (Fin n → R ⊗[F] E) → ℝ≥0∞, ((cm u : ℝ≥0∞) ^ n) * ∫⁻ r, g r ∂(Measure.pi fun _ : Fin n => coordK R b lam) =
      ∫⁻ r, g r ∂(((cm u : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => coordK R b lam) := fun g => by
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [hsm, ← hmap, lintegral_map hh hTm]
  refine lintegral_congr fun c => ?_
  have hc : (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) *
      (((u : R) ⊗ₜ[F] (algebraMap F E t)) * c j))) = c := by
    funext j
    rw [← mul_assoc, hVU, one_mul]
  rw [hc]
  exact (lintegral_sub_right_eq_self (fun S' => f (c, S')) _).symm

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem gramFib_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFib R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → IsOpen (Unt σ R n) ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧ (∀ S, S ∉ Unt σ R n → m S = 0) ∧ (∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → IsCompact D → D ⊆ Unt σ R n → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM N n J₂ hJ R _ _ _ _ _ hR d b lam hlam m hm
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n N
  obtain ⟨hLC, hSC, hT2, hB, hg⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R n
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB
  obtain ⟨g, gc, hgg⟩ := hg N J₂ hJ
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  haveI := hW n N
  haveI := hH n
  have hopen : IsOpen (Unt σ R n) := by
    have hu : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (_root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hu.preimage hc
  have hset : {X | IsUnit (gramR R σ J₂ X).det} = g ⁻¹' (Unt σ R n) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hgg X]
  have hm' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam n N) (gramR R σ J₂) Subtype.val
      (g ⁻¹' (Unt σ R n)) (coordHerm R σ b lam n) (Unt σ R n) m := by
    rw [← hset]
    exact hm
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ (coordW R b lam n N)
    (coordHerm R σ b lam n) (gramR R σ J₂) g Subtype.val Subtype.val_injective gc hgg (Unt σ R n) hopen m hm'
  refine ⟨hopen, h1, h2, h3, h4, fun S => ?_⟩
  have h0 := hm'.1 S
  have : ∀ᵐ X ∂(m S), X ∈ gramR R σ J₂ ⁻¹' {((S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩ g ⁻¹' (Unt σ R n) :=
    mem_ae_iff.2 h0
  filter_upwards [this] with X hX
  exact hX.1

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtension
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TupFubini

variable {T : Type} [MeasurableSpace T]

theorem measurable_cons_tail {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) :
    Measurable (fun Y : Fin n → A => (Fin.cons x Y : Fin (n + 1) → A)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using measurable_pi_apply j

theorem piFinSuccAbove_symm_apply {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) (Y : Fin n → A) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).symm (x, Y) = Fin.cons x Y := by
  apply (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).injective
  rw [MeasurableEquiv.apply_symm_apply]
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

theorem lintegral_tuple_succ (m : Measure T) [SigmaFinite m] (n N : ℕ)
    (ψ : (Fin (n + 1) → Fin N → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ X, ψ X ∂(Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin N => m) =
      ∫⁻ y : Fin 1 → Fin N → T, ∫⁻ Y : Fin n → Fin N → T, ψ (Fin.cons (y 0) Y)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin N => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin N => m) := by
  set P : Measure (Fin N → T) := Measure.pi fun _ : Fin N => m with hP
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  have h2 := measurePreserving_funUnique P (Fin 1)
  have hg : Measurable fun p : (Fin N → T) × (Fin n → Fin N → T) =>
      ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin N → T) 0).symm p) :=
    hψ.comp (MeasurableEquiv.measurable _)
  rw [← h1.symm.lintegral_comp hψ, lintegral_prod _ hg.aemeasurable,
    ← h2.lintegral_comp hg.lintegral_prod_right']
  refine lintegral_congr fun y => lintegral_congr fun Y => ?_
  rw [piFinSuccAbove_symm_apply]
  rfl

theorem lintegral_tuple_first_coord (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 1) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) =
      ∫⁻ c : Fin n → T, ∫⁻ X : Fin n → Fin M → T, ψ (fun a => Fin.cons (c a) (X a))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin n => m) := by
  let e₁ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => T) 0
  have h₁ : MeasurePreserving e₁ (Measure.pi fun _ : Fin (M + 1) => m)
      (m.prod (Measure.pi fun _ : Fin M => m)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => m) 0
  have h₂ := measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
    (fun _ : Fin n => m.prod (Measure.pi fun _ : Fin M => m)) (f := fun _ => e₁) (fun _ => h₁)
  have h₃ := measurePreserving_arrowProdEquivProdArrow T (Fin M → T) (Fin n) (fun _ => m)
    (fun _ => Measure.pi fun _ : Fin M => m)
  have h₄ := h₃.comp h₂
  let g : (Fin n → T) × (Fin n → Fin M → T) → Fin n → Fin (M + 1) → T :=
    fun p a => e₁.symm (p.1 a, p.2 a)
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun a => e₁.symm.measurable.comp ?_
    exact ((measurable_pi_apply a).comp measurable_fst).prodMk
      ((measurable_pi_apply a).comp measurable_snd)
  have hgi : ∀ Y, g ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
      fun Y a => e₁ (Y a)) Y) = Y := by
    intro Y
    funext a
    exact e₁.symm_apply_apply (Y a)
  have hψg : Measurable (ψ ∘ g) := hψ.comp hg
  calc ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
      = ∫⁻ Y, (ψ ∘ g) ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
          fun Y a => e₁ (Y a)) Y) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) :=
        lintegral_congr fun Y => by simp only [Function.comp_apply (f := ψ), hgi]
    _ = _ := h₄.lintegral_comp hψg
    _ = _ := lintegral_prod _ hψg.aemeasurable
    _ = _ := by
      refine lintegral_congr fun c => lintegral_congr fun X => ?_
      simp only [Function.comp_apply, g]
      congr 1
      funext a
      exact piFinSuccAbove_symm_apply (c a) (X a)

end GlobalTheory.CompanionTheory.SW.TupFubini

namespace GlobalTheory.CompanionTheory.SW

theorem lintegral_tuple_moving_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR d b lam hlam n s _ φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨hK, hW, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hact : ∀ h : HA R σ J, Measurable (actW R σ J h :
      (Fin n → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin (M + 1) → R ⊗[F] E) := by
    intro h
    have := hBorel n (M + 1)
    have hc := ((_root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM (M + 1) J hJ R).2.2.2.2.2 n).1
    exact (hc.comp (Continuous.prodMk_right h)).measurable
  have key : ∀ y : Fin 1 → Fin (M + 1) → R ⊗[F] E,
      ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1)) =
      ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a))))
        ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) := by
    intro y
    have hinv := _root_.GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq F E σ hCM (M + 1) J hJ R hR n (coordW R b lam n (M + 1)) (hW n (M + 1)) (s y)
    have hf : Measurable fun Y : Fin n → Fin (M + 1) → R ⊗[F] E =>
        φ (Fin.cons (y 0) Y) := hφ.comp (TupFubini.measurable_cons_tail (y 0))
    calc ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1))
        = ∫⁻ Y, φ (Fin.cons (y 0) Y) ∂((coordW R b lam n (M + 1)).map (actW R σ J (s y))) := by
          rw [hinv]
      _ = ∫⁻ Y, φ (Fin.cons (y 0) (actW R σ J (s y) Y)) ∂(coordW R b lam n (M + 1)) :=
          lintegral_map hf (hact (s y))
      _ = _ := TupFubini.lintegral_tuple_first_coord (coordK R b lam) n M _ (hf.comp (hact (s y)))
  calc ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y)
          ∂(coordW R b lam n (M + 1)) ∂(coordW R b lam 1 (M + 1)) :=
        TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 1) φ hφ
    _ = _ := lintegral_congr key

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivity
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramDensity

theorem isContDensityOn_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ → IsContDensityOn μ (gramR R σ J) Subtype.val ν {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ (fun S => ∫ X, φ X ∂(m S)) ∧ ∀ S, Integrable φ (m S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hfib φ hφ hφc
  have hunits : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := _root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  have := iB n M
  have := iTR
  have := iLC
  have := iSC
  have := iT2
  obtain ⟨jLC, jSC, jT2, jB, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  have := jLC
  have := jSC
  have := jT2
  have := jB
  obtain ⟨g, hg, hgram⟩ := hlift M J hJ
  have hB : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have hset : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [IsUnit]
    rw [hset]
    exact hunits.isOpen_range.preimage hdet
  have hpre : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp [hgram X]
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hpre]
    exact hfib
  exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hg hgram _ hB m hfib' φ hφ hφc

end GlobalTheory.CompanionTheory.SW.GramDensity
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAe
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramFib

theorem fibre_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ m', IsGramFib R σ J n μ ν m' → ∀ S, m S = m' S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm m' hm' S
  have hU := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hL, hS2, hT, hB, hg⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hL
  haveI := hS2
  haveI := hT
  haveI := hB
  obtain ⟨g, hgc, hgf⟩ := hg M J hJ
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have h1 : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have h2 : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [B, IsUnit]
    rw [h2]
    exact hU.isOpen_range.preimage h1
  have hUB : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' B := by
    ext X
    simp [B, hgf X]
  have hι : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m := by
    rw [← hUB]; exact hm
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m' := by
    rw [← hUB]; exact hm'
  by_cases hS : S ∈ B
  · exact (GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B B hBo hBo subset_rfl m' m h2 h1 S hS)
  · have a := (GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B hBo m h1).2.1 S hS
    have b := (GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B hBo m' h2).2.1 S hS
    rw [a, b]

end GlobalTheory.CompanionTheory.SW.GramFib
end

