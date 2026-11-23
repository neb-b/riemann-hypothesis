module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ConjAtPlaces

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev cc : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

def conjPerm : Equiv.Perm (HeightOneSpectrum (𝓞 E)) where
  toFun := conjSrc (cc E)
  invFun := conjSrc (cc E)
  left_inv := GlobalTheory.ThetaPull.conjSrc_conjSrc
  right_inv := GlobalTheory.ThetaPull.conjSrc_conjSrc

variable {E}

def conjCompl (w : HeightOneSpectrum (𝓞 E)) : (conjPerm E w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (cc E) w)
    ⟨(conjLoc (cc E) w).injective, GlobalTheory.CuspRep.ParLaws.conjLoc_surjective (cc E) w⟩

theorem norm_conjCompl (w : HeightOneSpectrum (𝓞 E)) (y : (conjPerm E w).adicCompletion E) :
    ‖conjCompl w y‖ = ‖y‖ := by
  have key : ∀ (a b : NNReal) (ha : a ≠ 0) (hb : b ≠ 0), a = b → ∀ z,
      WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
    rintro a _ ha hb rfl z
    rfl
  have hv : Valued.v (conjCompl w y) = Valued.v y := (conjLoc_spec (cc E) w).2.2 y
  have hN : (Ideal.absNorm w.asIdeal : NNReal) = Ideal.absNorm (conjPerm E w).asIdeal := by
    rw [show Ideal.absNorm (conjPerm E w).asIdeal = Ideal.absNorm w.asIdeal from
      GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (cc E) w]
  rw [FinitePlace.norm_def, FinitePlace.norm_def, hv, key _ _ _ _ hN]

theorem conjPlaces : ConjPlaces := by
  intro E _ _ _
  refine ⟨fun v u => ?_, fun c => conjAd_algebraMap c, conjPerm E, conjCompl, norm_conjCompl, fun w u => ?_⟩
  · exact congrFun (GlobalTheory.ThetaPull.pInf_conjAd u) v
  · rfl

end GlobalTheory.CompanionTheory.ConjAtPlaces

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctions
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BaseTest

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 1) (Fin 1) E}
    (hJ : IsHermND σ J) : ∃ X : Fin 1 → Fin 1 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := by
    have h := hJ.2
    rw [Matrix.det_fin_one] at h
    simpa [hE, hform] using h
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, GlobalTheory.CompanionTheory.SW.MassTest.gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 1) (Fin 1) E) :
    IsOpen {X : Fin 1 → Fin 1 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 1 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 1 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 1) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 1) ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 1
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 1
  obtain ⟨X, hX⟩ := exists_unit_vector R hJ
  exact GlobalTheory.CompanionTheory.SW.MassTest.exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 1 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 1 A ≠ 0 ∧ coordW R b lam 1 1 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 1
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 1
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hJ
  exact GlobalTheory.CompanionTheory.SW.MassTest.exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hJ (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 1 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 1 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 1 (A0 v) := by
    unfold vol
    congr 1
    exact Finset.prod_congr rfl fun v hvS => by simp [hvS]
  refine ⟨φ, fun v => if v ∈ S then A0 v else latV b v, ⟨h1, h2, h3, h4, ?_, ?_⟩, ?_, ?_⟩
  · intro v hvS
    simp only [hvS, if_true]
    exact ⟨hc v, ho v, hs v⟩
  · intro v hvS
    simp [hvS]
  · rw [hv]
    exact mul_ne_zero h5 (Finset.prod_ne_zero_iff.2 fun v _ => hn v)
  · rw [hv]
    exact ENNReal.mul_ne_top h6 (ENNReal.prod_ne_top fun v _ => ht v)

end GlobalTheory.CompanionTheory.SW.BaseTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BaseHasse

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem invol (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2]; simp)

theorem exists_pure (hCM : IsCMExt F E σ) : ∃ e : E, e ≠ 0 ∧ σ e = -e := by
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ x : E, σ x = x := fun x => by
    by_contra hx
    refine hcon (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
    rw [map_sub, invol hCM]
    ring
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    ext x
    have h := hCM.2.2.2 τ x
    rw [hfix] at h
    simpa using h.symm
  haveI : IsTotallyComplex E := hCM.2.1
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hreal)

theorem coord_E (hCM : IsCMExt F E σ) {e : E} (he : e ≠ 0) (hσ : σ e = -e) (z : E) :
    ∃ c d : F, z = algebraMap F E c + algebraMap F E d * e := by
  obtain ⟨c, hc⟩ := GoodMass.fixed_mem hCM ((z + σ z) / 2) (by
    rw [map_div₀, map_add (f := _), invol hCM, map_ofNat]
    ring)
  obtain ⟨d, hd⟩ := GoodMass.fixed_mem hCM ((z - σ z) / (2 * e)) (by
    rw [map_div₀, map_sub, invol hCM, map_mul, map_ofNat, hσ]
    field_simp
    ring)
  refine ⟨c, d, ?_⟩
  rw [hc, hd]
  field_simp
  ring

variable (R : Type) [CommRing R] [Algebra F R]

theorem coord_R (hCM : IsCMExt F E σ) {e : E} (he : e ≠ 0) (hσ : σ e = -e) (y : R ⊗[F] E) :
    ∃ a b : R, y = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] e := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r z =>
    obtain ⟨c, d, rfl⟩ := coord_E hCM he hσ z
    refine ⟨algebraMap F R c * r, algebraMap F R d * r, ?_⟩
    have key : ∀ (c : F) (w : E), r ⊗ₜ[F] (algebraMap F E c * w) = (algebraMap F R c * r) ⊗ₜ[F] w := by
      intro c w
      rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [TensorProduct.tmul_add, ← key, ← key, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

theorem tmul_one_injective {r s : R} (h : r ⊗ₜ[F] (1 : E) = s ⊗ₜ[F] (1 : E)) : r = s :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (R := F) (A := R) (B := E)
    (FaithfulSMul.algebraMap_injective F E) h

theorem local_form (hCM : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} {j : F} (hj : J 0 0 = algebraMap F E j)
    (hj0 : j ≠ 0) {e : E} (he : e ≠ 0) (hσ : σ e = -e) {δ : F} (hδ : e * e = algebraMap F E δ) (β : F)
    (Y : Fin 1 → Fin 1 → R ⊗[F] E) (hY : gramR R σ J Y = (hermScal R σ (algebraMap F R β)).1) :
    ∃ a b : R, algebraMap F R (β / j) = a ^ 2 - algebraMap F R δ * b ^ 2 := by
  obtain ⟨a, b, hab⟩ := coord_R R hCM he hσ (Y 0 0)
  refine ⟨a, b, ?_⟩
  have h00 : hR R σ J (Y 0) (Y 0) = algebraMap F R β ⊗ₜ[F] (1 : E) := congrFun (congrFun hY 0) 0
  have hsig : sigR R σ (Y 0 0) = a ⊗ₜ[F] (1 : E) - b ⊗ₜ[F] e := by
    rw [hab, map_add (f := _)]
    simp [sigR, hσ, TensorProduct.tmul_neg, sub_eq_add_neg]
  have hJ : inclR R (J 0 0) = algebraMap F R j ⊗ₜ[F] (1 : E) := by
    rw [hj]
    simp [inclR, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hee : (b ⊗ₜ[F] e) * (b ⊗ₜ[F] e) = (algebraMap F R δ * b ^ 2) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_mul_assoc, one_mul, sq]
  have hn : sigR R σ (Y 0 0) * Y 0 0 = (a ^ 2 - algebraMap F R δ * b ^ 2) ⊗ₜ[F] (1 : E) := by
    rw [hsig, hab, TensorProduct.sub_tmul, ← hee, sq, ← mul_one (1 : E), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    ring
  have h1 : (algebraMap F R j * (a ^ 2 - algebraMap F R δ * b ^ 2)) ⊗ₜ[F] (1 : E) = algebraMap F R β ⊗ₜ[F] (1 : E) := by
    rw [← h00]
    simp only [hR, hform, JR, Fin.sum_univ_one, Matrix.map_apply, hJ]
    rw [mul_comm (sigR R σ (Y 0 0)), mul_assoc, hn, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h2 := tmul_one_injective (F := F) (E := E) R h1
  have hu : algebraMap F R j * algebraMap F R j⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hj0, map_one]
  rw [div_eq_mul_inv, map_mul, ← h2]
  linear_combination (a ^ 2 - algebraMap F R δ * b ^ 2) * hu

end

section

variable {F : Type} [Field F] [NumberField F]

theorem exists_real_hom (τ : F →+* ℝ) : ∃ ψ : Ainf F →+* ℝ, ∀ x, ψ (algebraMap F (Ainf F) x) = τ x := by
  let φ : F →+* ℂ := Complex.ofRealHom.comp τ
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    simp [φ, ComplexEmbedding.conjugate]
  let v : InfinitePlace F := InfinitePlace.mk φ
  have hv : v.IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v), fun x => ?_⟩
  have h1 : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
      (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) (algebraMap F (Ainf F) x) =
        InfinitePlace.embedding_of_isReal hv x :=
    by
      simpa only [RingHom.comp_apply, Pi.evalRingHom_apply,
        NumberField.InfiniteAdeleRing.algebraMap_apply,
        InfinitePlace.Completion.algebraMap_apply, RingEquiv.apply_symm_apply,
        WithAbs.equiv_symm_apply, WithAbs.equiv_apply, WithAbs.ofAbs_toAbs] using
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x)
  refine h1.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  rfl

end

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ hmi hm β hβ hinf hfin
  obtain ⟨j, hj⟩ := GoodMass.fixed_mem hCM _ (hJ.1 0 0)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hJ.2 (by rw [Matrix.det_fin_one, ← hj, map_zero])
  obtain ⟨e, he, hσ⟩ := exists_pure hCM
  obtain ⟨δ, hδ⟩ := GoodMass.fixed_mem hCM (e * e) (by rw [map_mul, hσ]; ring)
  have hδ' : e * e = algebraMap F E δ := hδ.symm
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact mul_ne_zero he he (by rw [hδ', map_zero])
  have hfib : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
      (μ' : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
      (m' : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)), IsGramFib R σ J 1 μ' ν m' →
      m' (hermScal R σ (algebraMap F R β)) ≠ 0 →
      ∃ a b : R, algebraMap F R (β / j) = a ^ 2 - algebraMap F R δ * b ^ 2 := by
    intro R _ _ _ μ' ν m' hG hne
    by_contra hcon
    have hempty : (gramR R σ J ⁻¹' {(hermScal R σ (algebraMap F R β)).1} ∩
        {X | IsUnit (gramR R σ J X).det}) = ∅ := by
      ext Y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hY _
      exact hcon (local_form R hCM hj.symm hj0 he hσ hδ' β Y hY)
    apply hne
    have h1 := hG.1 (hermScal R σ (algebraMap F R β))
    rw [hempty, Set.compl_empty] at h1
    exact Measure.measure_univ_eq_zero.1 h1
  obtain ⟨a, c, hac⟩ := GlobalTheory.QNorm.hasseNormSt F δ (β / j) hδ0 (div_ne_zero hβ hj0)
    (fun τ => by
      obtain ⟨ψ, hψ⟩ := exists_real_hom τ
      obtain ⟨a, c, h⟩ := hfib (Ainf F) _ _ mi hmi hinf
      refine ⟨ψ a, ψ c, ?_⟩
      have := congrArg ψ h
      simpa [hψ] using this)
    (fun v => hfib (Fv F v) _ _ (m v) (hm v) (hfin v))
  refine ⟨fun _ _ => algebraMap F E a + algebraMap F E c * e, ?_⟩
  funext p q
  have hp : p = 0 := Subsingleton.elim _ _
  have hq : q = 0 := Subsingleton.elim _ _
  subst hp hq
  have hb : β = j * (a ^ 2 - δ * c ^ 2) := by
    rw [← hac]
    field_simp
  simp only [gramE, hE, hform, Fin.sum_univ_one, ← hj, RingHom.coe_coe, map_add (f := _), map_mul, hσ, AlgHom.commutes]
  rw [hb, map_mul, map_sub, map_mul, map_pow, map_pow, ← hδ']
  ring

end GlobalTheory.CompanionTheory.SW.BaseHasse
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrinciple
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgBase

open PositivityTheory.Rg.Base1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_tmul_one {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : AF F ⊗[F] E) :
    (Algebra.norm (AF F) x) ⊗ₜ[F] (1 : E) = sigR (AF F) σ x * x := by
  have e := GlobalTheory.Doubling.algebraMap_norm_eq h (R := AF F) x
  rw [Algebra.TensorProduct.algebraMap_apply] at e
  rw [mul_comm]
  exact e

theorem isNm_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : (AF F ⊗[F] E)ˣ) (a : (AF F)ˣ) :
    IsNm σ x a ↔ Algebra.norm (AF F) (x : AF F ⊗[F] E) = a := by
  have hinj : Function.Injective (fun r : AF F => r ⊗ₜ[F] (1 : E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  unfold IsNm
  rw [← norm_tmul_one h]
  exact ⟨fun e => (hinj e).symm, fun e => by rw [e]⟩

theorem hEx : HEx := by
  intro F E _ _ _ _ _ σ h
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  refine ⟨(GlobalTheory.IdeleNormChar.normSign (K := F) E).ker, ?_, ?_, ?_⟩
  · intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      obtain ⟨t, x, hx⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha
      refine ⟨t, x, a / GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t, ?_, ?_⟩
      · exact (isNm_iff h x _).2 (congrArg Units.val hx)
      · exact (mul_div_cancel (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t) a).symm
    · rintro ⟨t, x, n, hn, rfl⟩
      have h1 : GlobalTheory.IdeleNormChar.normSign E (pr t) = 1 := GlobalTheory.IdeleNormChar.normSign_toUnits E t
      have h2 : GlobalTheory.IdeleNormChar.normSign E n = 1 :=
        GlobalTheory.IdeleNormChar.normSign_of_mem E ⟨x, Units.ext ((isNm_iff h x n).1 hn)⟩
      rw [map_mul, h1, h2, one_mul]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := F) E] with a ha
    exact ha
  · obtain ⟨b, hb⟩ := GlobalTheory.IdeleNormChar.exists_normSign_ne_one (K := F) E
    have hr : (GlobalTheory.IdeleNormChar.normSign (K := F) E).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
    rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

end GlobalTheory.CompanionTheory.RgBase

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOne

theorem dens : Dens := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hσ hJ hli hlam hμ hF hmi hm S φ A hT
  obtain ⟨hφ, hφc, hφ0, hφU, hA, -⟩ := hT
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral (Ainf F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hmi φ hφ hφc hφ0 hφU
  have hv : ∀ v ∈ S, Continuous (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      HasCompactSupport (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      ENNReal.ofReal (∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) =
        coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.FibreCpt.masses_field (Fv F v) (_root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) hσ hJ b (lam v) (hlam v).1
      (m v) (hm v) (A v) (hA v hvS).1 (hA v hvS).2.1 (hA v hvS).2.2
  refine ⟨c1, c2, fun v hvS => ⟨continuous_const.mul (hv v hvS).1, (hv v hvS).2.1.mul_left⟩, ?_⟩
  have hI0 : 0 ≤ ∫ y, Gi mi φ y ∂li :=
    integral_nonneg fun s => integral_nonneg fun X => hφ0 X
  have hJ0 : ∀ v ∈ S, 0 ≤ ∫ s, gv m A v s ∂(lam v) := fun v _ =>
    integral_nonneg fun s => mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hloc : ∀ v ∈ S, ENNReal.ofReal (∫ s, gv m A v s ∂(lam v)) =
      (cfac E v : ℝ≥0∞) * coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have e : ∫ s, gv m A v s ∂(lam v) =
        (cfac E v : ℝ) * ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v) :=
      integral_const_mul _ _
    rw [e, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, (hv v hvS).2.2]
  rw [ENNReal.ofReal_mul hI0, ENNReal.ofReal_prod_of_nonneg hJ0, Finset.prod_congr rfl hloc,
    Finset.prod_mul_distrib]
  have e0 : ENNReal.ofReal (∫ y, Gi mi φ y ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1) := c4
  rw [e0, vol]
  ring

end GlobalTheory.CompanionTheory.SW.RankOne

end
end

