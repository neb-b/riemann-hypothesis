module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitarySiegelThetaTransformationLawStandar
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0010
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleIndicatorFunctions
section
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}


theorem mem_stdL {x : Fin n → E} : x ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      intro a
      by_cases hab : a = b
      · subst hab
        simpa using isIntegral_one
      · simp [hab, isIntegral_zero]
    | zero => intro a; exact isIntegral_zero
    | add y z _ _ hy hz => intro a; exact (hy a).add (hz a)
    | smul r y _ hy =>
      intro a
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe r).mul (hy a)
  · intro hx
    have hsum : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      ext b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

private theorem cc_zero_siegel_theta_transformation : cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

private theorem cc_one' : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

private theorem isIntegral_cc' {t : E} (ht : IsIntegral ℤ t) : IsIntegral ℤ (cc t) :=
  ht.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

private theorem herm_one_apply (x y : Fin n → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

theorem stdL_mem_Vset (M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_,
    ⟨1, one_pos, Nat.coprime_one_left M, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩⟩
  constructor
  · intro hx y hy
    rw [herm_one_apply]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc' (hy a))
  · intro h
    rw [mem_stdL]
    intro a
    have ha := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one_apply, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc_zero_siegel_theta_transformation])
      (by simp)] at ha
    simpa [cc_one'] using ha

end
end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem exists_weil_mul {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (h : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ')
    (h' : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ' φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ') :
    ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS (σ * σ') φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨ω, hω⟩ := h
  obtain ⟨ω', hω'⟩ := h'
  refine ⟨fun φ => ω (ω' φ), fun φ hφ => ?_⟩
  obtain ⟨hs', ht', hi'⟩ := hω' φ hφ
  obtain ⟨hs, ht, hi⟩ := hω (ω' φ) hs'
  refine ⟨hs, _root_.GlobalTheory.SW.transS_comp κ ι σ' σ hσ' hσ φ (ω' φ) (ω (ω' φ)) ht' ht, fun φ' hφ' => ?_⟩
  rw [hi _ (hω' φ' hφ').1, hi' φ' hφ']

theorem exists_weil_of_symplectic :
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  intro κ ι _ _ _ σ hκ hσ
  obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, l₁, l₂, l₃, rfl⟩ := _root_.GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ : Matrix.J ι ℚ ∈ Matrix.symplecticGroup ι ℚ := SymplecticGroup.J_mem ι ℚ
  have w₁ := _root_.GlobalTheory.SW.Parab.trans_parabolic κ ι p₁ hκ h₁ l₁
  have w₂ := _root_.GlobalTheory.SW.Parab.trans_parabolic κ ι p₂ hκ h₂ l₂
  have w₃ := _root_.GlobalTheory.SW.Parab.trans_parabolic κ ι p₃ hκ h₃ l₃
  have wJ := _root_.GlobalTheory.SW.FourierJ.exists_trans_J κ ι hκ
  have a₁ := mul_mem h₁ hJ
  have a₂ := mul_mem a₁ h₂
  have a₃ := mul_mem a₂ hJ
  exact exists_weil_mul a₃ h₃
    (exists_weil_mul a₂ hJ (exists_weil_mul a₁ h₂ (exists_weil_mul h₁ hJ w₁ wJ) w₂) wJ) w₃

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
section
noncomputable section

open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.VolPairExists

theorem exists_haar_image {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Continuous ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t)
    (hf : ∀ t, ∃ W ∈ 𝓝 t, ∃ K : Set G, IsCompact K ∧ (H : Set G) ∩ ψ ⁻¹' W ⊆ K) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ s, MeasurableSet s → μ (ψ ⁻¹' s ∩ H) = ν s := by
  classical
  have hψm : Measurable ψ := hψ.measurable
  set μ₀ : Measure G := Measure.haar
  set ρ : Measure R := (μ₀.restrict (H : Set G)).map ψ with hρdef
  have hρ : ∀ s, MeasurableSet s → ρ s = μ₀ (ψ ⁻¹' s ∩ H) := by
    intro s hsm
    rw [hρdef, Measure.map_apply hψm hsm, Measure.restrict_apply (hψm hsm)]
  have : ρ.IsMulLeftInvariant := by
    refine ⟨fun r => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hs r
    refine Measure.ext fun s hsm => ?_
    have hpre : ψ ⁻¹' ((fun x => ψ h * x) ⁻¹' s) ∩ H = (fun x => h * x) ⁻¹' (ψ ⁻¹' s ∩ H) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe]
      rw [Subgroup.mul_mem_cancel_left H hh]
    rw [Measure.map_apply (measurable_const_mul _) hsm, hρ _ ((measurable_const_mul _) hsm), hρ _ hsm,
      hpre, measure_preimage_mul]
  have : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun C hC => ?_⟩
    choose W hW K hK hWK using hf
    obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun x => interior (W x))
      (fun x _ => interior_mem_nhds.2 (hW x))
    have hUo : IsOpen (⋃ x ∈ t, interior (W x)) := isOpen_biUnion fun x _ => isOpen_interior
    calc ρ C ≤ ρ (⋃ x ∈ t, interior (W x)) := measure_mono ht
      _ = μ₀ (ψ ⁻¹' (⋃ x ∈ t, interior (W x)) ∩ H) := hρ _ hUo.measurableSet
      _ ≤ μ₀ (⋃ x ∈ t, K x) := by
          apply measure_mono
          rintro y ⟨hy1, hy2⟩
          simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 ⊢
          obtain ⟨x, hx, hyx⟩ := hy1
          exact ⟨x, hx, hWK x ⟨hy2, show ψ y ∈ W x from interior_subset hyx⟩⟩
      _ ≤ ∑ x ∈ t, μ₀ (K x) := measure_biUnion_finset_le t K
      _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ => (hK x).measure_lt_top
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have h1 := hρ Set.univ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.preimage_univ, Set.univ_inter] at h1
    exact (hH.measure_pos μ₀ ⟨1, H.one_mem⟩).ne' h1.symm
  have hc := Measure.isMulLeftInvariant_eq_smul ρ ν
  set c := Measure.haarScalarFactor ρ ν
  have hc0 : c ≠ 0 := by
    intro h0
    apply hρ0
    rw [hc, h0, zero_smul]
  have : (c⁻¹ • μ₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc0)
  refine ⟨c⁻¹ • μ₀, inferInstance, fun s hsm => ?_⟩
  have h1 := hρ s hsm
  rw [hc] at h1
  rw [Measure.smul_apply, ← h1, Measure.smul_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]

variable {P Q : ℕ}

theorem jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem left_inv_of_unitary {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  calc Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q * (uᴴ * Formalism.UG.Jpq P Q * u) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, jpq_mul_self]

def mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) :
    UpqT P Q :=
  (⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv_of_unitary h),
    left_inv_of_unitary h⟩, h⟩ : Formalism.UG.Upq P Q)

theorem mat_mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h) : UpqT.mat (mkU u h) = u := rfl

theorem mat_injective : Function.Injective (UpqT.mat (P := P) (Q := Q)) := by
  intro a b h
  let a' : Formalism.UG.Upq P Q := a
  let b' : Formalism.UG.Upq P Q := b
  have h' : a'.1 = b'.1 := Units.ext h
  exact (Subtype.ext h' : a' = b')

theorem mat_mul (b c : UpqT P Q) : UpqT.mat (b * c) = UpqT.mat b * UpqT.mat c := rfl

theorem mat_one : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := by
  have hb := (b : Formalism.UG.Upq P Q).2
  exact hb

theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) := by
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_mkU {X : Type} [TopologicalSpace X] (f : X → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
    (hf : Continuous f) (h : ∀ x, (f x)ᴴ * Formalism.UG.Jpq P Q * f x = Formalism.UG.Jpq P Q) :
    Continuous fun x => mkU (f x) (h x) := by
  have hinv : Continuous fun x => Formalism.UG.Jpq P Q * (f x)ᴴ * Formalism.UG.Jpq P Q :=
    (continuous_const.matrix_mul hf.matrix_conjTranspose).matrix_mul continuous_const
  unfold mkU
  refine (Units.continuous_iff.2 ⟨?_, ?_⟩).subtype_mk _
  · exact hf
  · exact hinv

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}

theorem exists_frame (h : Formalism.UG.HasSignature G P Q) :
    ∃ (A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ) (L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ),
      Aᴴ * Formalism.UG.Jpq P Q * A = G ∧ L * A = 1 ∧ A * L = 1 := by
  unfold Formalism.UG.HasSignature at h
  obtain ⟨e, g, hg⟩ := h
  have hg' : (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Matrix.reindex e e G * g = Formalism.UG.Jpq P Q := hg
  have key : Matrix.reindex e e G =
      ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q *
        ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    set u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := g.val
    set v : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (g⁻¹).val
    have huv : u * v = 1 := Units.mul_inv g
    calc Matrix.reindex e e G = (u * v)ᴴ * Matrix.reindex e e G * (u * v) := by
          rw [huv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = vᴴ * (uᴴ * Matrix.reindex e e G * u) * v := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = vᴴ * Formalism.UG.Jpq P Q * v := by rw [hg']
  refine ⟨((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix id e,
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (Formalism.UG.Jpq P Q),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← key]
    ext i j
    simp [Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Units.mul_inv, Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_id_id]

variable {A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} {L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ}

theorem conj_frame (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) : Lᴴ * G * L = Formalism.UG.Jpq P Q := by
  rw [← hA]
  have h1 : Lᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * L = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, hr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem change_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (hA' : A'ᴴ * Formalism.UG.Jpq P Q * A' = G) :
    (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul]
  have h1 : Lᴴ * A'ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Lᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA', conj_frame hA hr]

theorem conj_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * G * g = G) : (A * g * L)ᴴ * Formalism.UG.Jpq P Q * (A * g * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Lᴴ * (gᴴ * Aᴴ) * Formalism.UG.Jpq P Q * (A * g * L) =
      Lᴴ * (gᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * g) * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hg, conj_frame hA hr]

theorem conj_unitary_back (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (b : UpqT P Q) :
    (L * UpqT.mat b * A)ᴴ * G * (L * UpqT.mat b * A) = G := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Aᴴ * ((UpqT.mat b)ᴴ * Lᴴ) * G * (L * UpqT.mat b * A) =
      Aᴴ * ((UpqT.mat b)ᴴ * (Lᴴ * G * L) * UpqT.mat b) * A := by
    simp only [Matrix.mul_assoc]
  rw [h1, conj_frame hA hr, mat_unitary, hA]

theorem exists_hom {Γ : Type} [Group Γ] [TopologicalSpace Γ] (m : Γ → Matrix (Fin n) (Fin n) ℂ)
    (hm : Continuous m) (hmul : ∀ g h, m (g * h) = m g * m h) (hu : ∀ h, (m h)ᴴ * G * m h = G)
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hl : L * A = 1) (hr : A * L = 1) :
    ∃ ψ : Γ →* UpqT P Q, Continuous ψ ∧ ∀ h, UpqT.mat (ψ h) = A * m h * L := by
  let f : Γ → UpqT P Q := fun x => mkU (A * m x * L) (conj_unitary hA hr (hu x))
  have hf : ∀ x, UpqT.mat (f x) = A * m x * L := fun x => mat_mkU _ _
  refine ⟨MonoidHom.mk' f fun x y => mat_injective ?_, ?_, fun x => hf x⟩
  · rw [mat_mul, hf, hf, hf, hmul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L, hl, Matrix.one_mul]
  · show Continuous f
    exact continuous_mkU (fun x => A * m x * L) ((continuous_const.matrix_mul hm).matrix_mul continuous_const)
      (fun x => conj_unitary hA hr (hu x))

theorem read_iff (hl : L * A = 1) (hr : A * L = 1) (u : UpqT P Q) (hu : UpqT.mat u = A' * L)
    {g : Matrix (Fin n) (Fin n) ℂ} (t : UpqT P Q) (ht : UpqT.mat t = A * g * L) (B : Set (UpqT P Q)) :
    (∃ b ∈ B, UpqT.mat b * A' = A' * g) ↔ t ∈ (fun b => b * u⁻¹) ⁻¹' ((fun b => u * b) ⁻¹' B) := by
  have hA' : A' = UpqT.mat u * A := by rw [hu, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hinv : UpqT.mat u⁻¹ * UpqT.mat u = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have key : ∀ b : UpqT P Q, UpqT.mat b * A' = A' * g ↔ b = u * (t * u⁻¹) := by
    intro b
    constructor
    · intro h
      have h2 : UpqT.mat (b * u) = UpqT.mat (u * t) := by
        rw [mat_mul, mat_mul, ht]
        calc UpqT.mat b * UpqT.mat u = UpqT.mat b * A' * L := by rw [hu, Matrix.mul_assoc]
          _ = A' * g * L := by rw [h]
          _ = UpqT.mat u * (A * g * L) := by rw [hA']; simp only [Matrix.mul_assoc]
      have h3 := mat_injective h2
      rw [← mul_assoc, ← h3, mul_inv_cancel_right]
    · rintro rfl
      rw [mat_mul, mat_mul, ht, hA']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UpqT.mat u⁻¹), hinv, Matrix.one_mul, hl, Matrix.mul_one]
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [(key b).1 h] at hb
  · intro h
    exact ⟨_, h, (key _).2 rfl⟩

end GlobalTheory.VolPairExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSUnique
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

theorem transS_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := _root_.GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ I_mem_siegel
  refine _root_.GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e1 := h _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e2 := h' _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e := e1.trans e2.symm
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.vecMul_one] using e

theorem val_trans_J : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ →
      TransS (Matrix.J ι ℚ) φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ),
        Ph u ∧ ψ y = u * haar (fun x => φ x * chr y' x) := by
  intro κ ι _ _ _ ⟨p, hp⟩ φ ψ ⟨R, hR, h⟩ hψ ht y
  have e := transS_unique (SymplecticGroup.J_mem ι ℚ) hψ
    ⟨R, hR, FourierJ.ft_level hR h _⟩ ht (FourierJ.trans_J hp hR h)
  refine ⟨I ^ (Fintype.card ι * p), y, ⟨4, by norm_num, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; simp [Complex.I_pow_four]
  · rw [e]
    simp only [FourierJ.ft, FourierJ.pr, FourierJ.ech, chr]

end GlobalTheory.Phase
end

