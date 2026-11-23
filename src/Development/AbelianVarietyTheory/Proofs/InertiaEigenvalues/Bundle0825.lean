module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatIso

open MvPolynomial

theorem mem_localization_comap_iff {R R' W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R' W'] (φ : R ≃+* R') (f : W → W') (hf : ∀ (r : R) x, f (r • x) = φ r • f x)
    (p : Ideal R') [p.IsPrime] (L : Submodule R W) (L' : Submodule R' W') (hL : ∀ x, f x ∈ L' ↔ x ∈ L) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ (p.comap (φ : R →+* R')) L ↔ f x ∈ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  show (∃ s ∈ (p.comap (φ : R →+* R')).primeCompl, s • x ∈ L) ↔ ∃ s ∈ p.primeCompl, s • f x ∈ L'
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨φ s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      exact hs
    · rw [← hf]; exact (hL _).2 h
  · rintro ⟨s, hs, h⟩
    refine ⟨φ.symm s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      rw [Ideal.mem_comap]
      simpa using hs
    · rw [← hL, hf, RingEquiv.apply_symm_apply]; exact h

section Fields

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K' ≃+* K)

abbrev vmE (n : ℕ) : (Fin n → K') ≃+ (Fin n → K) := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vmE_apply (n : ℕ) (x : Fin n → K') (a : Fin n) : vmE e n x a = e (x a) := rfl

theorem vmE_smul (n : ℕ) (r : 𝓞 K') (x : Fin n → K') :
    vmE e n (r • x) = RingOfIntegers.mapRingEquiv e r • vmE e n x :=
  funext fun i => GlobalTheory.IdealTransport.map_smul_int e r (x i)

theorem mem_span_vmE_iff {n : ℕ} (S : Set (Fin n → K')) (x : Fin n → K') :
    vmE e n x ∈ Submodule.span (𝓞 K) (vmE e n '' S) ↔ x ∈ Submodule.span (𝓞 K') S := by
  rw [← GlobalTheory.IdealTransport.span_image_span (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    GlobalTheory.IdealTransport.mem_span_image (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    AddEquiv.symm_apply_apply]

theorem mem_tauLat_iff {E : Type} [Field E] [NumberField E] {ι : Type} {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → K') :
    vmE e n x ∈ tauLat emb2 τ M ↔ x ∈ tauLat emb τ M := by
  have h2 : tauLat emb2 τ M =
      Submodule.span (𝓞 K) (vmE e n '' ((fun (y : Fin n → E) (a : Fin n) => emb τ (y a)) '' (M : Set (Fin n → E)))) := by
    rw [Set.image_image]
    unfold tauLat
    congr 1
    refine Set.image_congr fun y _ => funext fun a => ?_
    rw [h]; rfl
  rw [h2, mem_span_vmE_iff]
  rfl

theorem mem_dualFr' {F : Type} [Field F] [NumberField F] {n : ℕ} (L : Submodule (𝓞 F) (Fin n → F)) (y : Fin n → F) :
    y ∈ dualFr L ↔ ∀ x ∈ L, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 F) F) := Iff.rfl

theorem map_mem_one_iff (a : K') : e a ∈ (1 : Submodule (𝓞 K) K) ↔ a ∈ (1 : Submodule (𝓞 K') K') := by
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(RingOfIntegers.mapRingEquiv e).symm r, e.injective ?_⟩
    rw [← hr]
    change e (e.symm (r : K)) = (r : K)
    exact e.apply_symm_apply _
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem mem_dualFr_iff {n : ℕ} (L : Submodule (𝓞 K') (Fin n → K')) (L2 : Submodule (𝓞 K) (Fin n → K))
    (hL : ∀ x, vmE e n x ∈ L2 ↔ x ∈ L) (y : Fin n → K') : vmE e n y ∈ dualFr L2 ↔ y ∈ dualFr L := by
  have hd : ∀ x : Fin n → K', vmE e n y ⬝ᵥ vmE e n x = e (y ⬝ᵥ x) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul, vmE_apply]
  rw [mem_dualFr', mem_dualFr']
  constructor
  · intro hy x hx
    rw [← map_mem_one_iff e, ← hd]
    exact hy _ ((hL x).2 hx)
  · intro hy x2 hx2
    obtain ⟨x, rfl⟩ := (vmE e n).surjective x2
    rw [hd, map_mem_one_iff]
    exact hy x ((hL x).1 hx2)

theorem mem_colLat_iff {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K') :
    vmE e n x ∈ colLat B ↔ x ∈ colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  have h : colLat B = Submodule.span (𝓞 K) (vmE e n '' Set.range fun j : Fin n => fun a : Fin n =>
      ((Matrix.GeneralLinearGroup.map e.symm.toRingHom B : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') a j) := by
    unfold colLat
    rw [← Set.range_comp]
    congr 1
    congr 1
    funext j a
    simp only [Function.comp_apply, vmE_apply]
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact (e.apply_symm_apply _).symm
  rw [h, mem_span_vmE_iff]
  unfold colLat
  rfl

theorem isBasisAt_transport {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K') (Fin n → K'))
    (M2 : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x, vmE e n x ∈ M2 ↔ x ∈ M) (B : GL (Fin n) K) (hB : IsBasisAt w M2 B) :
    IsBasisAt (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) M
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  unfold IsBasisAt at hB ⊢
  ext x
  have h1 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal M M2 hM x
  have h2 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal
    (colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B)) (colLat B) (mem_colLat_iff e B) x
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [hB]

theorem map_smul_int' {σ : Type} (r : 𝓞 K') (P : MvPolynomial σ K') :
    map e.toRingHom (r • P) = RingOfIntegers.mapRingEquiv e r • map e.toRingHom P :=
  GlobalTheory.IoExtend.map_smul_alg e.toRingHom (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (fun _ => rfl) r P

theorem map_symm_map {σ : Type} (P : MvPolynomial σ K') : map e.symm.toRingHom (map e.toRingHom P) = P := by
  rw [map_map]
  convert map_id P
  ext a
  simp

theorem mem_nabStd_iff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K' ι n) :
    map e.toRingHom F ∈ nabStd K lam ↔ F ∈ nabStd K' lam := by
  constructor
  · intro h
    have := GlobalTheory.IoExtend.map_mem_nabStd e.symm.toRingHom lam h
    rwa [map_symm_map] at this
  · intro h
    exact GlobalTheory.IoExtend.map_mem_nabStd e.toRingHom lam h

theorem map_mem_nabP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K') (Fin n → K')) (M2 : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ x, vmE e n x ∈ M2 τ ↔ x ∈ M τ) {F : Pol K' ι n} (hF : F ∈ nabP lam M) :
    map e.toRingHom F ∈ nabP lam M2 := by
  unfold nabP transLat at hF ⊢
  simp only [Submodule.mem_iInf] at hF ⊢
  intro w B hB
  let B' : ι → GL (Fin n) K' := fun τ => Matrix.GeneralLinearGroup.map e.symm.toRingHom (B τ)
  have h1 := hF (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) B'
    (fun τ => isBasisAt_transport e w (M τ) (M2 τ) (hM τ) (B τ) (hB τ))
  rw [Submodule.mem_comap] at h1 ⊢
  have hinv : ∀ t, ((B⁻¹ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B'⁻¹ t : GL (Fin n) K') : Matrix (Fin n) (Fin n) K').map e.toRingHom := by
    intro t
    have : B'⁻¹ t = Matrix.GeneralLinearGroup.map e.symm.toRingHom ((B t)⁻¹) := by
      simp only [Pi.inv_apply, B', map_inv]
    rw [this]
    ext a b
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  have hact := GlobalTheory.IoExtend.polyAction_map e.toRingHom lam B'⁻¹ B⁻¹ hinv F
  have h2 := (mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (map e.toRingHom) (map_smul_int' e) w.asIdeal
    (nabStd K' lam) (nabStd K lam) (mem_nabStd_iff e lam) _).1 h1
  change actP lam B⁻¹ (map e.toRingHom F) ∈ _
  rw [hact]
  exact h2

theorem map_mem_nabAtr {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (lam : ι → DomWeight n)
    (M : Submodule (𝓞 E) (Fin n → E)) {F : VV K' lam} (hF : F ∈ nabAtr emb lam M) :
    (⟨map e.toRingHom F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ lam _ F.2⟩ : VV K lam) ∈ nabAtr emb2 lam M := by
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  exact map_mem_nabP e lam _ _ (fun τ x => mem_dualFr_iff e _ _ (fun y => mem_tauLat_iff e emb emb2 h τ M y) x) hF

end Fields

theorem coefLatFn_ringEquiv (D : D7) (n : ℕ) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K' ≃+* K) (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K')) (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn (σ.comp e.toRingHom) emb O lam M = coefLatFn σ (fun τ => e.toRingHom.comp (emb τ)) O lam M := by
  have hc : ∀ (P : Pol K' D.what₂.Tau n) (x : GLR D n),
      coefFn σ lam (map e.toRingHom P) x = coefFn (σ.comp e.toRingHom) lam P x := by
    intro P x
    unfold coefFn
    rw [MvPolynomial.eval₂Hom_map_hom]
  apply le_antisymm
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨_, map_mem_nabAtr e emb _ (fun _ => rfl) lam M hF, funext fun x => (hc F.1 x).symm⟩
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨G, hG, rfl⟩
    have hG' := map_mem_nabAtr e.symm (fun τ => e.toRingHom.comp (emb τ)) emb
      (fun τ => by ext a; simp) lam M hG
    refine Submodule.subset_span ⟨_, hG', funext fun x => ?_⟩
    refine Eq.trans ?_ (hc _ x)
    change coefFn σ lam G.1 x = coefFn σ lam (map e.toRingHom (map e.symm.toRingHom G.1)) x
    rw [map_map]
    congr 2
    convert (map_id G.1).symm
    ext a
    simp

end GlobalTheory.CoefLatIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZUnfWt

open GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem lastRow_mul_of_mem {h : GA E (m + 1)} (hh : h ∈ mirU (Ad E) (m + 1) m) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [(mem_mirU_last.1 hh) (Fin.last m), if_pos rfl, one_mul]
  · intro l _ hl
    rw [(mem_mirU_last.1 hh) l, if_neg hl, zero_mul]
  · simp


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem det_blkU {R : Type} [CommRing R] {a k : ℕ} (y : UnipotentBlockColumnIndex a k k → R) : (blkU y : GL (Fin a) R).val.det = 1 := by
  have h := mem_mirU_zero.1 (blkU_mem_mirU 0 y)
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_blkU (x : ℝ) {k : ℕ} (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) : detPow E (m + 1) x (blkU y) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (blkU y : GA E (m + 1)) = 1 := Units.ext (det_blkU y)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp


omit [_root_.NumberField.IsTotallyComplex E] in
theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  have e : natLat E N = (fun z => (N : Af E) * z) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [e]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_yFin : Continuous (yFin (E := E) (m := m)) :=
  continuous_pi fun i => (continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp
    ((Units.continuous_val : Continuous fun g : GA E (m + 1) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem
      (Fin.last m) i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_detPow (x : ℝ) : Continuous (detPow E (m + 1) x) :=
  continuous_norm.comp (Units.continuous_val.comp
    ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_wt (N : ℕ) (x : ℝ) : Measurable (wt (E := E) (m := m) N x) := by
  let S : Set (Fin (m + 1) → Af E) := {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N}
  have hS : IsClosed S := by
    have e : S = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [S]
    rw [e]
    exact isClosed_iInter fun i => (isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const)
  have hm : MeasurableSet {g : GA E (m + 1) | yFin g ∈ S} := (hS.preimage continuous_yFin).measurableSet
  have hind : Measurable fun g : GA E (m + 1) => indN N (yFin g) := by
    unfold indN
    exact Measurable.ite hm measurable_const measurable_const
  exact ((Complex.measurable_re.comp hind).mul (continuous_detPow x).measurable).real_toNNReal

theorem wt_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  intro E _ _ _ m N x
  refine ⟨measurable_wt N x, fun γ hγ g => ?_, fun k y g => ?_⟩
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (map_mem_mirU _ hγ) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (blkU_mem_mirU m y) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_blkU, one_mul]

end GlobalTheory.ZUnfWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section
open scoped ContDiff

namespace GlobalTheory.SmoothClosure

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_apply (F : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a)
    (hd : DifferentiableAt ℝ (chart F g) x) (Z : Lie E a) :
    fderiv ℝ (chart F g) x Z = chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Z)) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL u.val)).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  change Z = u.val * ((Matrix.of (toL u.val))⁻¹ * Matrix.of Z)
  have : (Matrix.of (toL u.val))⁻¹ = (↑(u⁻¹) : Matrix (Fin a) (Fin a) (Cinf E)) := by
    change (u.val)⁻¹ = _
    rw [Matrix.coe_units_inv]
  rw [this, ← mul_assoc, Units.mul_inv, one_mul]
  rfl

theorem chart_lieD_basis {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (F : GA E a → ℂ) (g : GA E a)
    {x : Lie E a} (hx : x ∈ invSet E a) (W : Lie E a) :
    chart (lieD W F) g x = ∑ k, b.repr W k • chart (lieD (b k) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  simp only [chart_val, lieD]
  conv_lhs => rw [← b.sum_repr W]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

theorem le_Sm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (GA E a → ℂ)),
    (∀ F ∈ S, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a)) →
    (∀ F ∈ S, ∀ X : Lie E a, lieD X F ∈ S) → S ≤ Sm E a := by
  intro E _ _ _ a S hdiff hlie
  let b := Module.finBasis ℝ (Lie E a)
  have key : ∀ n : ℕ, ∀ F ∈ S, ∀ g : GA E a, ContDiffOn ℝ n (chart F g) (invSet E a) := by
    intro n
    induction n with
    | zero =>
      intro F hF g
      exact contDiffOn_zero.2 (hdiff F hF g).continuousOn
    | succ n ih =>
      intro F hF g
      rw [Nat.cast_succ]
      refine contDiffOn_succ_of_fderiv_apply (hdiff F hF g) (by simp) fun Z => ?_
      have hc : ∀ k, ContDiffOn ℝ n (fun x : Lie E a =>
          (b.coord k).toContinuousLinearMap (rmul Z (toL (Matrix.of x)⁻¹))) (invSet E a) := fun k =>
        (b.coord k).toContinuousLinearMap.contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn (GlobalTheory.GLFin.Inhab.contDiffOn_invL.of_le (by exact_mod_cast le_top)))
      have hsum : ContDiffOn ℝ n (fun x => ∑ k ∈ Finset.univ, (b.coord k).toContinuousLinearMap
          (rmul Z (toL (Matrix.of x)⁻¹)) • chart (lieD (b k) F) g x) (invSet E a) :=
        ContDiffOn.sum fun k _ => (hc k).smul (ih _ (hlie F hF (b k)) g)
      refine hsum.congr fun x hx => ?_
      rw [fderivWithin_of_isOpen isOpen_invSet hx,
        fderiv_chart_apply F g hx ((hdiff F hF g).differentiableAt (isOpen_invSet.mem_nhds hx)) Z,
        chart_lieD_basis b F g hx]
      rfl
  intro F hF g
  exact contDiffOn_infty.2 fun n => key n F hF g

end GlobalTheory.SmoothClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecayStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellinType_integral_entire_of_rapid_decay : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (A : X → ℂ) (T : X → ℝ),
    AEStronglyMeasurable A ν → Measurable T → (∀ x, 0 < T x) → Integrable (fun x => min (T x) (T x)⁻¹) ν →
    (∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) →
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  first | exact @GlobalTheory.MellinEntire.integrable_and_differentiable | exact GlobalTheory.MellinEntire.integrable_and_differentiable | (intros; apply GlobalTheory.MellinEntire.integrable_and_differentiable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.ColConvGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (M P : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (M * P)‖ ≤ (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
  have hM : ∀ i k, ‖M i k‖ ≤ ‖toL M‖ := fun i k =>
    (norm_le_pi_norm (toL M i) k).trans (norm_le_pi_norm (toL M) i)
  have hP : ∀ i k, ‖P i k‖ ≤ ‖toL P‖ := fun i k =>
    (norm_le_pi_norm (toL P i) k).trans (norm_le_pi_norm (toL P) i)
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i =>
    pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(M * P) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ k, M i k * P k j‖ ≤ ∑ k, ‖M i k * P k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin a, ‖toL M‖ * ‖toL P‖ := Finset.sum_le_sum fun k _ =>
        (norm_mul_le _ _).trans (mul_le_mul (hM i k) (hP k j) (norm_nonneg _) (norm_nonneg _))
    _ = (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem height_mul_le (y u : GL (Fin a) (Cinf E)) :
    height (y * u) ≤ ((a : ℝ) + 1) * height y * height u := by
  have h1 := norm_toL_mul_le y.val u.val
  have h2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
  have e1 : (y * u).val = y.val * u.val := rfl
  have e2 : ((y * u)⁻¹).val = (u⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (toL u.val)
  have n4 := norm_nonneg (toL (u⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold height
  rw [e1, e2]
  nlinarith [mul_nonneg n1 n3, mul_nonneg n2 n4, mul_nonneg n1 n4, mul_nonneg n2 n3,
    mul_nonneg ha (mul_nonneg n1 n3), mul_nonneg ha (mul_nonneg n2 n4), mul_nonneg ha n1, mul_nonneg ha n2,
    mul_nonneg ha n3, mul_nonneg ha n4, mul_nonneg ha (mul_nonneg n1 n4), mul_nonneg ha (mul_nonneg n2 n3)]

end GlobalTheory.MSpanDecay.ColConvGrowth

namespace GlobalTheory.MSpanDecay

end GlobalTheory.MSpanDecay
end
end

