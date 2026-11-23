module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
public import ReciprocityTheory.GaloisValuations.GlobalE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0228
public import GroundTheory.LocalFields.MainTheorem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralVecSmul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS PositivityTheory.AdelicQuotientData
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnipotentNormalizer

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem map_vec_smul {ι : Type} [Fintype ι] (a : ι → (Ad E)ˣ) :
    (vecMeasure E ι).map (fun x p => a p • x p) =
      (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) • vecMeasure E ι := by
  classical
  let c : ι → NNReal := fun p => Real.toNNReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹
  have hm : ∀ p, (GroundTheory.Global.adeleMeasure E).map (fun x => a p • x) = c p • GroundTheory.Global.adeleMeasure E := fun p => by
    rw [GroundTheory.Global.map_smul_adeleMeasure]; rfl
  have : ∀ p, SigmaFinite ((GroundTheory.Global.adeleMeasure E).map (fun x => a p • x)) := fun p => by
    rw [hm]; infer_instance
  have hmeas : ∀ p, Measurable (fun x : Ad E => a p • x) := fun p =>
    (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable
  have h := Measure.pi_map_pi (μ := fun _ : ι => GroundTheory.Global.adeleMeasure E) (f := fun p x => a p • x)
    (fun p => (hmeas p).aemeasurable)
  rw [vecMeasure, h]
  simp_rw [hm]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem lintegral_vec_smul {ι : Type} [Fintype ι] (a : ι → (Ad E)ˣ) (G : (ι → Ad E) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G (fun p => a p • x p) ∂vecMeasure E ι =
      (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) * ∫⁻ x, G x ∂vecMeasure E ι := by
  have hf : Measurable (fun (x : ι → Ad E) p => a p • x p) := Measurable.of_eval fun p =>
    (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable.comp (measurable_pi_apply p)
  rw [← lintegral_map hG hf, map_vec_smul, lintegral_smul_measure]
  rfl

theorem conj_blkU {R : Type} [CommRing R] (D : GL (Fin k) R) (u : Fin k → Rˣ)
    (hD : D.val = diagonal fun i => (u i : R)) {r m : ℕ} (x : UnipotentBlockColumnIndex k r m → R) :
    D * blkU x * D⁻¹ = blkU (fun t => ((u t.1.1 * (u t.1.2)⁻¹ : Rˣ) : R) * x t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  change D.val * (1 + posM Subtype.val x) = (1 + posM Subtype.val _) * D.val
  rw [hD]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.add_apply, mul_add, add_mul]
  congr 1
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · simp only [posM, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t.1.1 = i ∧ t.1.2 = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply_same, Units.val_mul]
      have e : ((u t.1.2)⁻¹ : Rˣ).val * (u t.1.2).val = 1 := Units.inv_mul _
      linear_combination (-(u t.1.1).val * x t) * e
    · have e : ∀ y : R, Matrix.single t.1.1 t.1.2 y i j = 0 := fun y => by
        rw [Matrix.single_apply_of_ne]; exact h
      rw [e, e]; simp

def locId (w : Pl E) : (w.adicCompletion E)ˣ →* (Ad E)ˣ := (finId E).comp (Units.map (corner (sLoc E w)))

theorem fl_torus (w : Pl E) (l : Fin k → ℤ) :
    (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)).val =
      diagonal fun i => ((locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l i) : (Ad E)ˣ) : Ad E) := by
  ext i j
  change (1 : Matrix (Fin k) (Fin k) (Ad E)) i j - sFin E ((1 : Matrix (Fin k) (Fin k) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin k) (Fin k) (Af E)) i j - sLoc E w ((1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) i j) +
      sLoc E w ((Iwasawa.torusPow (w.adicCompletion E) k l).val i j)) = _
  rw [Iwasawa.torusPow, Iwasawa.coe_diagGL]
  by_cases h : i = j
  · subst h
    simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · simp [h]

end GlobalTheory.CompanionTheory.UnipotentNormalizer

namespace GlobalTheory.CompanionTheory.UnipotentNormalizer

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def colS (e : Fin k → ℤ) (j : ℕ) : ℤ := ∑ p : UnipotentBlockColumnIndex k j j, (e p.1.1 - e p.1.2)

def totS (e : Fin k → ℤ) (d : ℕ) : ℤ := ∑ i ∈ Finset.range d, colS e (k - (i + 1))

theorem prod_ofReal_zpow {ι : Type} (s : Finset ι) {q : ℝ} (hq : 0 < q) (e : ι → ℤ) :
    ∏ p ∈ s, ENNReal.ofReal (q ^ e p) = ENNReal.ofReal (q ^ ∑ p ∈ s, e p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq.ne', ENNReal.ofReal_mul (zpow_nonneg hq.le _)]

theorem sFinite_nuD (d : ℕ) : SFinite (nuD E k d) := by
  induction d with
  | zero => change SFinite (Measure.dirac _); infer_instance
  | succ d ih => change SFinite (Measure.map _ _); infer_instance

theorem measurable_blkMul (j : ℕ) : Measurable (fun p : (UnipotentBlockColumnIndex k j j → Ad E) × GA E k => blkU p.1 * p.2) :=
  by
    set_option synthInstance.maxHeartbeats 400000 in
      exact (((continuous_posU _).comp continuous_fst).mul continuous_snd).measurable

theorem nuD_conj (t : GA E k) (u : Fin k → (Ad E)ˣ) (ht : t.val = diagonal fun i => (u i : Ad E)) {q : ℝ} (hq : 0 < q)
    (e : Fin k → ℤ) (hmod : ∀ a b, ((GroundTheory.Global.IdeleGroup.ideleModule E (u a * (u b)⁻¹) : ℝ))⁻¹ = q ^ (e a - e b))
    (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F (t * h * t⁻¹) ∂nuD E k d = ENNReal.ofReal (q ^ totS e d) * ∫⁻ h, F h ∂nuD E k d := by
  have hc : Measurable (fun h : GA E k => t * h * t⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  induction d generalizing F with
  | zero =>
    have hFc : Measurable fun h => F (t * h * t⁻¹) := hF.comp hc
    change ∫⁻ h, F (t * h * t⁻¹) ∂Measure.dirac 1 = _ * ∫⁻ h, F h ∂Measure.dirac 1
    rw [lintegral_dirac' _ hFc, lintegral_dirac' _ hF]
    simp [totS]
  | succ d ih =>
    have := sFinite_nuD (E := E) (k := k) d
    have hM := measurable_blkMul (E := E) (k := k) (k - (d + 1))
    let a : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → (Ad E)ˣ := fun p => u p.1.1 * (u p.1.2)⁻¹
    let G : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) → ℝ≥0∞ := fun y => ∫⁻ h, F (blkU y * h) ∂nuD E k d
    have hFM : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => F (blkU p.1 * p.2) := hF.comp hM
    have hFc : Measurable fun h => F (t * h * t⁻¹) := hF.comp hc
    have hFcM : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k =>
        F (t * (blkU p.1 * p.2) * t⁻¹) := hFc.comp hM
    have hG : Measurable G := hFM.lintegral_prod_right'
    have hf : Measurable (fun (x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) p => a p • x p) :=
      Measurable.of_eval fun p =>
        (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable.comp (measurable_pi_apply p)
    have hR : ∫⁻ h, F h ∂nuD E k (d + 1) = ∫⁻ y, G y ∂vecMeasure E _ := by
      change ∫⁻ h, F h ∂(Measure.map _ _) = _
      rw [lintegral_map hF hM, lintegral_prod _ hFM.aemeasurable]
    have hL : ∫⁻ h, F (t * h * t⁻¹) ∂nuD E k (d + 1) =
        ∫⁻ x, ENNReal.ofReal (q ^ totS e d) * G (fun p => a p • x p) ∂vecMeasure E _ := by
      change ∫⁻ h, F (t * h * t⁻¹) ∂(Measure.map _ _) = _
      rw [lintegral_map hFc hM, lintegral_prod _ hFcM.aemeasurable]
      refine lintegral_congr fun x => ?_
      have key : ∀ h, t * (blkU x * h) * t⁻¹ = blkU (fun p => a p • x p) * (t * h * t⁻¹) := fun h => by
        have e1 : blkU (fun p => a p • x p) = t * blkU x * t⁻¹ := (conj_blkU t u ht x).symm
        rw [e1]; group
      simp only [key]
      exact ih (fun y => F (blkU (fun p => a p • x p) * y)) (hF.comp (measurable_const_mul _))
    have hstep : (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) =
        ENNReal.ofReal (q ^ colS e (k - (d + 1))) := by
      simp only [a, hmod]
      exact prod_ofReal_zpow _ hq _
    have hGf : Measurable fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E => G (fun p => a p • x p) := hG.comp hf
    rw [hL, hR, lintegral_const_mul _ hGf, lintegral_vec_smul a G hG, hstep, ← mul_assoc,
      ← ENNReal.ofReal_mul (zpow_nonneg hq.le _), ← zpow_add₀ hq.ne']
    simp only [totS, Finset.sum_range_succ]

theorem nuP_zero : nuP E k 0 = nuD E k (k - 1) := by
  have h1 : IsMir 0 (1 : GL (Fin k) E) := fun i j _ => rfl
  let i0 : ({γ : GL (Fin k) E | IsMir 0 γ} : Set _) := ⟨1, h1⟩
  have hu : ∀ γ : ({γ : GL (Fin k) E | IsMir 0 γ} : Set _), γ = i0 := fun γ => Subtype.ext (Units.ext (Matrix.ext fun i j =>
    γ.2 i j (Or.inl (Nat.zero_le _))))
  ext s hs
  rw [nuP, nuG, Measure.sum_apply _ hs, tsum_eq_single i0 (fun b hb => absurd (hu b) hb)]
  simp [i0]

theorem colS_eq (l : Fin k → ℤ) (c : Fin k) : colS l c = ∑ i : Fin k, if i < c then l i - l c else 0 := by
  classical
  unfold colS
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin k × Fin k => (p.1 : ℕ) < c ∧ (c : ℕ) ≤ p.2 ∧ (p.2 : ℕ) ≤ c)
    (by simp) (fun p => l p.1 - l p.2), Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single c]
  · simp only [le_refl, and_true, Fin.val_fin_lt]
  · intro b _ hb
    rw [if_neg]
    rintro ⟨-, h1, h2⟩
    have h1' : (c : ℕ) ≤ b := h1
    have h2' : (b : ℕ) ≤ c := h2
    exact hb (Fin.ext (by omega))
  · simp

theorem sum_cols (l : Fin k → ℤ) : ∑ c : Fin k, ∑ i : Fin k, (if i < c then l i - l c else 0) = rhoPair l :=
  _root_.UpperTheory.Reformulated.B.CountingPairs.main l

theorem totS_eq (l : Fin k → ℤ) : totS l (k - 1) = rhoPair l := by
  rw [← sum_cols l]
  simp only [← colS_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => colS l j) k]
  rcases k with _ | n
  · simp [totS]
  · have h0 : colS l 0 = 0 := Finset.sum_eq_zero fun t _ => absurd t.2.1 (Nat.not_lt_zero _)
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp only [totS, Nat.add_sub_cancel]
    rw [Nat.sub_self, h0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    have := Finset.mem_range.1 hi
    omega

variable [_root_.NumberField.IsTotallyComplex E]

theorem mod_locId (hD : D0) (w : Pl E) (m : ℤ) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ m)) : ℝ) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := hD E 1
  have h2 := h w (fun _ => m)
  have e : GeneralLinearGroup.det (fl 1 w (Iwasawa.torusPow (w.adicCompletion E) 1 fun _ => m)) =
      locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ m) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, fl_torus, Matrix.det_diagonal]
    simp
  rw [Dt, e] at h2
  simpa using h2

theorem main : PositivityTheory.AdelicQuotientData.D0 → PositivityTheory.jumpWindows.G0 → PositivityTheory.AdelicQuotientData.N2 := by
  intro hD _ E _ _ _ k w l F hF
  have hm1 := mod_locId hD w 1
  have hq : 0 < (Ideal.absNorm w.asIdeal : ℝ) := by
    have h0 := (GroundTheory.Global.IdeleGroup.ideleModule E (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ (1 : ℤ)))).2
    rw [hm1] at h0
    by_contra hc
    have h00 : (Ideal.absNorm w.asIdeal : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    rw [h00] at h0
    simp at h0
  have hmod : ∀ a b, ((GroundTheory.Global.IdeleGroup.ideleModule E
      (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l a) *
        (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l b))⁻¹) : ℝ))⁻¹ =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (l a - l b) := fun a b => by
    rw [← map_inv, ← map_mul, ← _root_.zpow_neg, ← _root_.zpow_add, ← sub_eq_add_neg, mod_locId hD, _root_.zpow_neg, inv_inv]
  rw [nuP_zero, nuD_conj _ _ (fl_torus w l) hq l hmod (k - 1) F hF, totS_eq]

end GlobalTheory.CompanionTheory.UnipotentNormalizer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummer
section
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open ValuativeRel

namespace GlobalTheory.CompanionTheory.KapChi

theorem pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζ : ζ ^ N = 1) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) N, pow_add, pow_mul, hζ, one_pow, one_mul]

def addHom {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k) :
    D →* Multiplicative (ZMod N) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (χ g)) (fun g k => by rw [h]; rfl)

theorem chi_decomp {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k)
    (φ t i : D) (a : ℕ) (hφ : χ φ = 1) (hi : χ i = 0) : χ (φ ^ a * t ^ N * i) = a := by
  have hp : ∀ (x : D) (n : ℕ), χ (x ^ n) = n * χ x := fun x n => by
    have := map_pow (addHom χ h) x n
    have e : Multiplicative.toAdd (addHom χ h (x ^ n)) = χ (x ^ n) := rfl
    rw [← e, this, toAdd_pow]
    simp [addHom]
  rw [h, h, hi, hp, hp, hφ]
  simp

section Dec

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}

theorem chi_unique (hA : IsPlaceOver A v) (hN : 0 < N) {χ χ' : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    (ha' : ∀ g h, χ' (g * h) = χ' g + χ' h)
    (hI' : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0)
    (hF' : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) :
    χ = χ' := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  funext g
  obtain ⟨a, -, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), chi_decomp χ' ha' φ t i a (hF' φ hφ₁) (hI' i hi)]

theorem chi_eq_zero_of_fix (hA : IsPlaceOver A v) (hN : 0 < N) {χ : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    {ξ : Ω} (hξ : IsPrimitiveRoot ξ (normV v ^ N - 1)) (g : Dec (F := F) A)
    (hg : (g : G F Ω) ξ = ξ) : χ g = 0 := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  obtain ⟨a, haN, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  have h0 := GlobalTheory.T.frobenius_power_fixes_root_unique F Ω A v hA φ hφ₁ N hN ξ hξ a t i haN hi hg
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), h0, Nat.cast_zero]

end Dec

section Core

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem apply_eq_pow_cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) {ζ : Ω} (hζ : ζ ^ l ^ r = 1) :
    g ζ = ζ ^ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ

theorem exists_cochain_cup (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ r)) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) {ϖ ϖ' : 𝓞 F} (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2)
    (h1' : ϖ' ∈ v.asIdeal) (h2' : ϖ' ∉ v.asIdeal ^ 2) {t : Ω}
    (ht : t ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F))
    {κt χ : Dec (F := F) A → ZMod (l ^ r)}
    (hκ : ∀ g : Dec (F := F) A, (g : G F Ω) t = ζ ^ (κt g).val * t)
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) :
    ∃ c : Dec (F := F) A → ZMod (l ^ r), Continuous c ∧ ∀ g h : Dec (F := F) A,
      ((cycMod F Ω l r (g : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c h - c (g * h) + c g =
        κt g * χ h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hN : 0 < l ^ r := pow_pos hl r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  obtain ⟨θ, hθ, hθ', hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v hA ι hι
  have hlift' : ∀ (σ : GlobalTheory.LocDict.GalLoc v) (x : Ω), σ (ι x) = ι ((θ.symm σ : G F Ω) x) := fun σ x => by
    have := hlift (θ.symm σ) x
    rwa [MulEquiv.apply_symm_apply] at this

  have hq : 1 < normV v := ReciprocityTheory.Gal.one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, n = normV v ^ l ^ r - 1 := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  rw [hn] at hξ
  have hξv : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion F] ^ l ^ r - 1) := by
    rw [_root_.GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV F v]
    exact hξ.map_of_injective ι.toRingHom.injective
  let ψ : GlobalTheory.LocDict.GalLoc v →* Multiplicative (ZMod (l ^ r)) :=
    (addHom χ ha).comp θ.symm.toMonoidHom
  have hfix : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ξ) = ι ξ → ψ σ = 1 := fun σ hσ => by
    rw [hlift'] at hσ
    have e := chi_eq_zero_of_fix hA hN ha hI hF hξ (θ.symm σ) (ι.toRingHom.injective hσ)
    show Multiplicative.ofAdd (χ (θ.symm σ)) = 1
    rw [e]
    rfl
  have ho : IsOpen (ψ.ker : Set (GlobalTheory.LocDict.GalLoc v)) := by
    have : FiniteDimensional (v.adicCompletion F) (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}).fixingSubgroup)
      (fun σ hσ => hfix σ ?_) (IntermediateField.fixingSubgroup_isOpen _)
    exact hσ ⟨ι ξ, IntermediateField.mem_adjoin_simple_self _ _⟩

  have hϖ0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hϖ0' : algebraMap F (v.adicCompletion F) (ϖ' : F) ≠ 0 := by
    intro h
    have h0 : (ϖ' : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ' = 0 := by exact_mod_cast h0
    exact h2' (h0' ▸ Ideal.zero_mem _)
  let U : (v.adicCompletion F)ˣ := Units.mk0
    (algebraMap F (v.adicCompletion F) (ϖ' : F) / algebraMap F (v.adicCompletion F) (ϖ : F))
    (div_ne_zero hϖ0' hϖ0)
  have hU : (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) =
      algebraMap F (v.adicCompletion F) (ϖ' : F) := div_mul_cancel₀ _ hϖ0
  have hord := _root_.GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero F v ϖ ϖ' h1 h2 h1' h2' U hU
  have hnorm := _root_.GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN.ne' (ι ξ) hξv ψ ho hfix U hord
  have hcomm : ∀ x : F, ι (algebraMap F Ω x) =
      algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (algebraMap F (v.adicCompletion F) x) := fun x => by
    rw [ι.commutes, ← IsScalarTower.algebraMap_apply]
  have hT : ι t ^ l ^ r = algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (U : v.adicCompletion F) := by
    have e := congrArg ι ht
    rw [map_mul, map_pow, hcomm, hcomm, ← hU, map_mul] at e
    exact mul_right_cancel₀ ((map_ne_zero _).2 hϖ0) e
  have hc0 : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ζ) = ι ζ ^
      ((cycMod F Ω l r (θ.symm σ : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := fun σ => by
    rw [hlift', apply_eq_pow_cycMod l r _ hζ.pow_eq_one, map_pow]
  have hκ' : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι t) = ι ζ ^ (κt (θ.symm σ)).val * ι t := fun σ => by
    rw [hlift', hκ, map_mul, map_pow]
  obtain ⟨c, hc, hc2⟩ := _root_.GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN (ι ζ)
    (hζ.map_of_injective ι.toRingHom.injective) _ hc0 ψ ho U hnorm (ι t) (fun σ => κt (θ.symm σ)) hT hκ'
  refine ⟨fun g => c (θ g), hc.continuous.comp hθ, fun g h => ?_⟩
  have e := hc2 (θ g) (θ h)
  have hψ : Multiplicative.toAdd (ψ (θ h)) = χ h := by
    show χ (θ.symm (θ h)) = χ h
    rw [MulEquiv.symm_apply_apply]
  simp only [MulEquiv.symm_apply_apply, ← map_mul] at e
  rw [hψ] at e
  exact e

end Core

theorem cup_class_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 hy hκ hχa hχI hχF hz ϖ' y' κ' χ' z' h1' h2' hy'
    hκ' hχa' hχI' hχF' hz'
  have hN : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  obtain rfl : χ = χ' := chi_unique hA hN hχa hχI hχF hχa' hχI' hχF'
  have hϖ0 : algebraMap F Ω (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hy
    exact hϖ0 hy.symm
  have ht : (y' / y) ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F) := by
    rw [div_pow, hy, hy', div_mul_cancel₀ _ hϖ0]
  have hκt : ∀ g : Dec (F := F) A, (g : G F Ω) (y' / y) = ζ ^ (κ' g - κ g).val * (y' / y) := fun g => by
    have e := pow_val_add hζ.pow_eq_one (κ' g - κ g) (κ g)
    rw [sub_add_cancel] at e
    have hgy : ζ ^ (κ g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [map_div₀, hκ, hκ', e]
    field_simp
  obtain ⟨c, hc, hc2⟩ := exists_cochain_cup l r hr hζ hA h1 h2 h1' h2' ht hκt hχa hχI hχF
  refine ((Submodule.Quotient.eq _).2 ?_).symm
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  have e := hc2 g h
  rw [sub_mul] at e
  show _ = z'.1 (g, h) - z.1 (g, h)
  rw [hz, hz', ← e]
  rfl

end GlobalTheory.CompanionTheory.KapChi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslateStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_unipotent_translate : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g b hg Φ
  obtain ⟨-, -, hψ, -, -, -, -, hW⟩ := hS
  refine tsum_congr fun ξ => ?_
  have hmul : (b.map (incA D) * inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n) =
      (b * (ξᴴ * (V.gram * ξ))).map (incA D) := by
    change rat b * (adj (rat ξ) * (gA V * rat ξ)) = rat (b * (ξᴴ * (V.gram * ξ)))
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose, gA]
  have htrace (M : Matrix (Fin n) (Fin n) D.host.E) :
      Matrix.trace (M.map (incA D)) = incA D (Matrix.trace M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [hW.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), hmul, htrace,
    GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, hψ.2.2.1, one_mul]
end

