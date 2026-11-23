module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem shear (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n)) :
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := _root_.GlobalTheory.WhitBump.exists_shear_measurePreserving E n u hu

theorem isCompact_setOf_toL (T : Set (Lie E n)) (hT : IsCompact T) (hs : T ⊆ invSet E n) :
    IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := _root_.GlobalTheory.WhitBump.isCompact_GL_of_invSet E n T hT hs

variable [_root_.NumberField.IsTotallyComplex E]

theorem contDiffOn_bumpInf (f : Lie E n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ invSet E n) : ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := _root_.GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet E n f hf hc hs

theorem exists_bumpInf_ne : ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
    bumpInf f (oneL E n) ≠ 0 := _root_.GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero E n

theorem psiFin_integral (u : GL (Fin n) (Af E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hk : u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) : psiFin (GlobalTheory.Whittaker.superDiag u) = 1 :=
  _root_.GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral E n u hu hk

theorem bumpFin_spec
    (htriv : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) :
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := GlobalTheory.T.whittakerBumpFiniteFactor_properties E n htriv

theorem psiN_eq (u : GA E n) :
    GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) *
      psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := _root_.GlobalTheory.WhitBump.psiN_split E n u

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem continuous_finGL_bump : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

variable [_root_.NumberField.IsTotallyComplex E]

theorem psiInf_add (a b : Cinf E) : psiInf (a + b) = psiInf a * psiInf b := by
  simp [psiInf, map_add (f := _), AddChar.map_add_eq_mul]

theorem bumpInf_mul (f : Lie E n → ℝ) (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (x : Lie E n) :
    bumpInf f (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
      psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) * bumpInf f x := by
  obtain ⟨τ, hτ, hτu⟩ := shear u hu
  have hsd : ∀ t, sdM (nu (τ t)) = sdM (nu t) + sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) := fun t => by
    rw [hτu, ← nuGL_val, ← superDiag_eq_sdM, ← superDiag_eq_sdM, ← Units.val_mul, ← superDiag_eq_sdM]
    exact GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip (nuGL_mem t) hu
  have key : ∀ t, (f (toL (nu t * Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)))) : ℂ) *
      psiInf (-sdM (nu t)) = psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) *
        ((f (toL (nu (τ t) * Matrix.of x)) : ℂ) * psiInf (-sdM (nu (τ t)))) := fun t => by
    have e1 : Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
        (u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x := rfl
    have e2 : -sdM (nu t) = sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) + -sdM (nu (τ t)) := by
      rw [hsd]; abel
    rw [e1, ← Matrix.mul_assoc, ← hτu, e2, psiInf_add]
    ring
  unfold bumpInf
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact hτ.integral_comp' (g := fun s => (f (toL (nu s * Matrix.of x)) : ℂ) * psiInf (-sdM (nu s)))

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem map_apply_bump {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin n) R) (i j : Fin n) :
    (GeneralLinearGroup.map p g : Matrix (Fin n) (Fin n) S) i j = p ((g : Matrix (Fin n) (Fin n) R) i j) := rfl

theorem pInf_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) :
    GeneralLinearGroup.map (pFin E) u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Af E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

theorem mem_NA_of {y : GL (Fin n) (Cinf E)} {k : GL (Fin n) (Af E)} (hy : y ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (hk : k ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n)) : infGL E n y * finGL E n k ∈ GlobalTheory.JSW.NA (E := E) (a := n) := by
  have hI : GeneralLinearGroup.map (pInf E) (infGL E n y * finGL E n k) = y := by simp
  have hF : GeneralLinearGroup.map (pFin E) (infGL E n y * finGL E n k) = k := by simp
  obtain ⟨hy1, hy2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hy
  obtain ⟨hk1, hk2⟩ := (GlobalTheory.SmGL.mem_unipB (Af E)).1 hk
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [← map_apply_bump, hI, hy1 i j h, map_zero]
  · rw [← map_apply_bump, hF, hk1 i j h, map_zero]
  · rw [← map_apply_bump, hI, hy2 i, map_one]
  · rw [← map_apply_bump, hF, hk2 i, map_one]

end GlobalTheory.WhitBump


open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in
theorem GlobalTheory.WhitBump.exists_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  intro E _ _ _ m S
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p _ hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dite_eq_left hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddings
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.QuadSigns

section Field

variable {L : Type} [Field L] [NumberField L]

theorem conj_involutive (σ : L →+* L)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (x : L) : σ (σ x) = x := by
  let φ := (Classical.arbitrary (InfinitePlace L)).embedding
  apply φ.injective
  rw [hc, hc, Complex.conj_conj]

theorem isTotallyComplex_of_conj (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) : IsTotallyComplex L := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hr => hσ ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hr
  refine RingHom.ext fun x => w.embedding.injective ?_
  rw [hc, RingHom.id_apply, ← ComplexEmbedding.conjugate_coe_eq, hr]

end Field

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isReal_comp (σ : L →+* L) (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : L →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) := by
  rw [ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun x => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, hK]

theorem isTotallyReal_of_conj [Algebra.IsAlgebraic K L] (σ : L →+* L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) : IsTotallyReal K := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) w
  show (W.comap (algebraMap K L)).IsReal
  rw [← W.mk_embedding, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
  exact isReal_comp σ hK hc _

theorem eq_or_eq_conjugate (hd : Module.finrank K L = 2) (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ ε : L →+* ℂ)
    (h : φ.comp (algebraMap K L) = ε.comp (algebraMap K L)) :
    φ = ε ∨ φ = ComplexEmbedding.conjugate ε := by
  have hss := conj_involutive σ hc
  obtain ⟨s, hs⟩ : ∃ s, σ s ≠ s := by
    by_contra hne
    push_neg at hne
    exact hσ (RingHom.ext hne)
  set t := s - σ s with ht
  have hσt : σ t = -t := by rw [ht, map_sub, hss]; ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have hli : LinearIndependent K ![(1 : L), t] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h2 := congrArg σ hab
    simp only [Algebra.smul_def, map_add (f := _), map_mul, hK, hσt, map_one, map_zero, mul_one] at h2 hab
    have hb2 : (2 : L) * (algebraMap K L b * t) = 0 := by linear_combination hab - h2
    have hb : b = 0 := by simpa [ht0] using hb2
    subst hb
    simp only [map_zero, zero_mul, add_zero, FaithfulSMul.algebraMap_eq_zero_iff] at hab
    exact ⟨hab, rfl⟩
  have hdec : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * t := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hd])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [B, Fin.sum_univ_two, Algebra.smul_def]
  have hφK : ∀ a : K, φ (algebraMap K L a) = ε (algebraMap K L a) := fun a => RingHom.congr_fun h a
  obtain ⟨a, b, hab⟩ := hdec (t * t)
  have hb : b = 0 := by
    have h2 : σ (t * t) = t * t := by rw [map_mul, hσt, neg_mul_neg]
    rw [hab] at h2
    simp only [map_add (f := _), map_mul, hK, hσt] at h2
    have hb2 : (2 : L) * (algebraMap K L b * t) = 0 := by linear_combination -h2
    simpa [ht0] using hb2
  subst hb
  simp only [map_zero, zero_mul, add_zero] at hab
  have hsq : φ t * φ t = ε t * ε t := by rw [← map_mul, ← map_mul, hab, hφK]
  have hfac : (φ t - ε t) * (φ t + ε t) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    have hφt : φ t = ε t := sub_eq_zero.1 h1
    refine RingHom.ext fun x => ?_
    obtain ⟨a', b', rfl⟩ := hdec x
    simp only [map_add (f := _), map_mul, hφK, hφt]
  · right
    have hφt : φ t = -ε t := eq_neg_of_add_eq_zero_left h1
    refine RingHom.ext fun x => ?_
    obtain ⟨a', b', rfl⟩ := hdec x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc]
    simp only [map_add (f := _), map_mul, hφK, hφt, hK, hσt, map_neg]

end GlobalTheory.QuadSigns

namespace GlobalTheory.QuadSigns

open scoped TensorProduct

theorem exists_signs (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hd : Module.finrank K L = 2) (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (ε ε' : L →+* ℂ)
    (h1 : ε ≠ ε') (h2 : ε ≠ ComplexEmbedding.conjugate ε') :
    ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧
      (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' →
        φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L,
        Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  classical
  haveI : Algebra.IsQuadraticExtension K L := ⟨hd⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hKr : IsTotallyReal K := isTotallyReal_of_conj σ hK hc
  have hLc : IsTotallyComplex L := isTotallyComplex_of_conj σ hσ hc
  have hover : ∀ φ ψ : L →+* ℂ, InfinitePlace.mk (φ.comp (algebraMap K L)) =
      InfinitePlace.mk (ψ.comp (algebraMap K L)) → φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
    intro φ ψ hm
    apply eq_or_eq_conjugate hd σ hσ hK hc
    rcases InfinitePlace.mk_eq_iff.1 hm with hh | hh
    · exact hh
    · rwa [ComplexEmbedding.isReal_iff.1 (isReal_comp σ hK hc φ)] at hh
  set w₁ := InfinitePlace.mk (ε.comp (algebraMap K L)) with hw₁
  set w₂ := InfinitePlace.mk (ε'.comp (algebraMap K L)) with hw₂
  have hw : w₁ ≠ w₂ := by
    intro he
    rcases hover ε ε' he with hh | hh
    · exact h1 hh
    · exact h2 hh
  obtain ⟨h, hneg, hpos, hfin⟩ := GlobalTheory.QuadRecip.exists_signs_of_even K L hKr hLc {w₁, w₂}
    (by rw [Finset.card_pair hw]; decide)
  have hsign : ∀ φ : L →+* ℂ, (φ (algebraMap K L (h : K))).re =
      InfinitePlace.embedding_of_isReal (hKr.isReal (InfinitePlace.mk (φ.comp (algebraMap K L))))
        (h : K) := by
    intro φ
    have := InfinitePlace.embedding_of_isReal_apply
      (hKr.isReal (InfinitePlace.mk (φ.comp (algebraMap K L)))) (h : K)
    rw [InfinitePlace.embedding_mk_eq_of_isReal (isReal_comp σ hK hc φ), RingHom.comp_apply] at this
    rw [← this, Complex.ofReal_re]
  refine ⟨h, h.ne_zero, ?_, ?_, ?_, ?_⟩
  · rw [hsign]
    exact hneg _ (by simp [w₁])
  · rw [hsign]
    exact hneg _ (by simp [w₂])
  · intro φ n1 n2 n3 n4
    rw [hsign]
    refine hpos _ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro he
      rcases hover φ ε he with hh | hh
      · exact n1 hh
      · exact n2 hh
    · intro he
      rcases hover φ ε' he with hh | hh
      · exact n3 hh
      · exact n4 hh
  · intro v
    obtain ⟨z, hz⟩ := GlobalTheory.QuadSymbol.mem_normGroup_iff.1 (hfin v)
    exact ⟨z, hz⟩

end GlobalTheory.QuadSigns
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHoms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ContRead

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {U : X.Opens}

theorem val_eq_of_evHom_eq (hU : IsAffineOpen U) {σ τ : k →+* ℂ} {y : CxPts p σ} {z : CxPts p τ}
    (hy : y ∈ ptsIn p σ U) (hz : z ∈ ptsIn p τ U) (e : evHom hy = evHom hz) : y.1 = z.1 := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem eq_of_val_eq (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) {σ τ : k →+* ℂ} (e : σ = τ)
    (y : CxPts p σ) (z : CxPts p τ) (h : y.1 = z.1) : u σ y = u τ z := by
  subst e
  rw [Subtype.ext h]

theorem evHom_ofHom (hU : IsAffineOpen U) {σ : k →+* ℂ} (φ : Γ(X, U) →+* ℂ)
    (h : ∀ a, φ (algX p U a) = σ a) : evHom (ofHom_mem hU φ h) = φ :=
  RingHom.ext fun f => (ev_eq _ f).symm.trans (ev_ofHom hU φ h f)

theorem evHom_comp_algX {σ : k →+* ℂ} {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    (evHom hy).comp (algX p U) = σ :=
  RingHom.ext fun a => (ev_eq hy _).symm.trans (ev_algX hy a)

theorem exists_continuous_read : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  intro k _ X _ p D hX U hU u hu
  letI : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcf : ∀ f : Γ(X, U), Continuous fun x : Γ(X, U) →+* ℂ => x f := fun f =>
    (continuous_apply f).comp continuous_induced_dom
  refine ⟨fun x => u (x.comp (algX p U)) (ofHom hU x fun _ => rfl), ?_, ?_, ?_, ?_⟩
  · have := hX.finite_emb
    classical
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, x₀.comp (algX p U) = σ₀ := ⟨_, rfl⟩
    have hN : {x : Γ(X, U) →+* ℂ | x.comp (algX p U) = σ₀} ∈ 𝓝 x₀ := by
      have hex : ∀ τ : k →+* ℂ, τ ≠ σ₀ → ∃ a, τ a ≠ σ₀ a := fun τ h => by
        by_contra hc
        push_neg at hc
        exact h (RingHom.ext hc)
      choose! a ha using hex
      have hopen : ∀ τ : k →+* ℂ,
          {x : Γ(X, U) →+* ℂ | τ ≠ σ₀ → x (algX p U (a τ)) ≠ τ (a τ)} ∈ 𝓝 x₀ := by
        intro τ
        by_cases hτ : τ = σ₀
        · exact Filter.Eventually.of_forall fun x h => (h hτ).elim
        · have ho : IsOpen {x : Γ(X, U) →+* ℂ | x (algX p U (a τ)) ≠ τ (a τ)} :=
            isOpen_ne_fun (hcf _) continuous_const
          filter_upwards [ho.mem_nhds (show x₀ (algX p U (a τ)) ≠ τ (a τ) from
            fun h => ha τ hτ (h.symm.trans (RingHom.congr_fun hσ₀ (a τ))))] with x hx _ using hx
      filter_upwards [(Filter.iInter_mem (f := 𝓝 x₀)).2 hopen] with x hx
      by_contra hne
      exact (Set.mem_iInter.1 hx _) hne rfl
    let F : (Γ(X, U) →+* ℂ) → CxPts p σ₀ := fun x =>
      if h : x.comp (algX p U) = σ₀ then ofHom hU x (fun a => RingHom.congr_fun h a)
      else ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)
    have hF0 : F x₀ = ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a) := dif_pos hσ₀
    have hFmem : ∀ x, F x ∈ ptsIn p σ₀ U := fun x => by
      by_cases h : x.comp (algX p U) = σ₀
      · simp only [F, dif_pos h]; exact ofHom_mem _ _ _
      · simp only [F, dif_neg h]; exact ofHom_mem _ _ _
    have hF : ContinuousAt F x₀ := by
      refine tendsto_subtype_rng.2 ?_
      rw [hF0]
      refine GlobalTheory.Points.tendsto_of_isAffineOpen hU (ofHom_mem hU x₀ _) (Filter.Eventually.of_forall hFmem)
        fun f => ?_
      have e : ∀ᶠ x in 𝓝 x₀, x f = valR (F x).1 U f := by
        filter_upwards [hN] with x hx
        simp only [F, dif_pos hx]
        exact (ev_ofHom hU x _ f).symm
      rw [show valR (ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)).1 U f = x₀ f from
        ev_ofHom hU x₀ _ f]
      exact ((hcf f).tendsto x₀).congr' e
    have hu0 : ContinuousAt (u σ₀) (F x₀) :=
      (hu σ₀).continuousAt ((isOpen_ptsIn U).mem_nhds (hFmem x₀))
    refine (hu0.comp hF).congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    simp only [Function.comp_apply, F, dif_pos hx]
    exact eq_of_val_eq u hx _ _ rfl
  · intro σ y hy
    exact eq_of_val_eq u (evHom_comp_algX hy) _ _
      (val_eq_of_evHom_eq hU (ofHom_mem hU _ _) hy (evHom_ofHom hU _ _))
  · intro x
    exact ⟨x.comp (algX p U), ofHom hU x (fun _ => rfl), ofHom_mem hU x _, evHom_ofHom hU x _⟩
  · intro σ y hy W hW
    rw [nhds_induced] at hW
    obtain ⟨t, ht, hsub⟩ := mem_comap.1 hW
    have hc : ContinuousAt (fun z : CxPts p σ => fun f : Γ(X, U) => ev p σ U f z) y :=
      continuousAt_pi.2 fun f => (continuousOn_ev f).continuousAt ((isOpen_ptsIn U).mem_nhds hy)
    have hval : (fun f : Γ(X, U) => ev p σ U f y) = ⇑(evHom hy) := funext fun f => ev_eq hy f
    rw [← hval] at ht
    filter_upwards [hc.preimage_mem_nhds ht, (isOpen_ptsIn U).mem_nhds hy] with z hz hzU
    refine ⟨hzU, hsub ?_⟩
    have hv : (fun f : Γ(X, U) => ev p σ U f z) = ⇑(evHom hzU) := funext fun f => ev_eq hzU f
    show ⇑(evHom hzU) ∈ t
    rw [← hv]
    exact hz

end GlobalTheory.ContRead
end
end

