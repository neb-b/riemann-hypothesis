module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalIsoPartOfSimple
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def isoPart (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Submodule ℂ H :=
  ⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = π k (T w)), LinearMap.range T

theorem range_le_isoPart (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) {T : W →ₗ[ℂ] H} (hT : ∀ k w, T (ρ k w) = π k (T w)) :
    LinearMap.range T ≤ isoPart π ρ := by
  unfold isoPart
  exact le_iSup₂_of_le (f := fun (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = π k (T w)) => LinearMap.range T)
    T hT le_rfl

theorem starProjection_comm {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) (R : Submodule ℂ H)
    [FiniteDimensional ℂ R] (hR : ∀ k, ∀ w ∈ R, π k w ∈ R) (k : K) (x : H) :
    R.starProjection (π k x) = π k (R.starProjection x) := by
  have hinner : ∀ u v, ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := fun u v =>
    (⟨(π k : H →ₗ[ℂ] H), hπ k⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v
  have hsurj : ∀ w ∈ R, ∃ w' ∈ R, π k w' = w := by
    intro w hw
    refine ⟨π k⁻¹ w, hR _ w hw, ?_⟩
    change (π k * π k⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hR k _ (R.starProjection_apply_mem x))
  intro w hw
  obtain ⟨w', hw', rfl⟩ := hsurj w hw
  rw [← map_sub, hinner]
  exact (Submodule.mem_orthogonal' _ _).1 (R.sub_starProjection_mem_orthogonal x) w' hw'

variable [CompleteSpace H]

theorem isoPart_le_sup {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) {W : Type} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W) (W' : Submodule ℂ W)
    (hW : ∀ k, W' ≤ W'.comap (ρ k)) :
    isoPart π ρ ≤ isoPart π (ρ.subrepresentation W' hW) ⊔ isoPart π (ρ.quotient W' hW) := by
  refine iSup₂_le fun T hT => ?_
  let R : Submodule ℂ H := W'.map T
  have hRinv : ∀ k, ∀ w ∈ R, π k w ∈ R := by
    rintro k _ ⟨v, hv, rfl⟩
    exact ⟨ρ k v, hW k hv, hT k v⟩
  have hP : ∀ k x, R.starProjection (π k x) = π k (R.starProjection x) :=
    starProjection_comm hπ R hRinv
  have h1 : LinearMap.range (T ∘ₗ W'.subtype) ≤ isoPart π (ρ.subrepresentation W' hW) :=
    range_le_isoPart π _ (fun k w => by simp [hT])
  have hRle : R ≤ LinearMap.range (T ∘ₗ W'.subtype) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  have hker : W' ≤ LinearMap.ker ((LinearMap.id - (R.starProjection : H →ₗ[ℂ] H)) ∘ₗ T) := by
    intro v hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe]
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
    exact ⟨v, hv, rfl⟩
  let Q := W'.liftQ ((LinearMap.id - (R.starProjection : H →ₗ[ℂ] H)) ∘ₗ T) hker
  have hQmk : ∀ v, Q (Submodule.Quotient.mk v) = T v - R.starProjection (T v) := by
    intro v
    simp [Q]
  have hQ : ∀ k w, Q (ρ.quotient W' hW k w) = π k (Q w) := by
    intro k w
    induction w using Submodule.Quotient.induction_on with
    | H v =>
      rw [Representation.quotient_apply, Submodule.mapQ_apply, hQmk, hQmk, hT, hP, map_sub]
  have h2 := range_le_isoPart π (ρ.quotient W' hW) hQ
  rintro _ ⟨v, rfl⟩
  rw [show T v = R.starProjection (T v) + (T v - R.starProjection (T v)) by abel]
  exact Submodule.add_mem_sup (h1 (hRle (R.starProjection_apply_mem (T v))))
    (h2 ⟨Submodule.Quotient.mk v, hQmk v⟩)

theorem finiteDimensional_isoPart_of_simple {π : K →* (H →L[ℂ] H)}
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W)
    (hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤) :
    FiniteDimensional ℂ (isoPart π ρ) := by
  classical
  by_cases h0 : ∀ T : W →ₗ[ℂ] H, (∀ k w, T (ρ k w) = π k (T w)) → T = 0
  · have hbot : isoPart π ρ = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun T hT => ?_)
      rw [h0 T hT, LinearMap.range_zero]
    rw [hbot]
    infer_instance
  push Not at h0
  obtain ⟨T₀, hT₀, hne⟩ := h0
  have hinj : Function.Injective T₀ := by
    rw [← LinearMap.ker_eq_bot]
    rcases hs (LinearMap.ker T₀) (fun k v hv => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
      rw [hT₀, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  let S : Submodule ℂ H := LinearMap.range T₀
  have hSinv : ∀ k, ∀ w ∈ S, π k w ∈ S := by
    rintro k _ ⟨v, rfl⟩
    exact ⟨ρ k v, hT₀ k v⟩
  have hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S := by
    intro S' hle hinv
    rcases hs (S'.comap T₀) (fun k v hv => by
      simp only [Submodule.mem_comap] at hv ⊢
      rw [hT₀]
      exact hinv k _ hv) with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := hle hw
      have hv : v ∈ S'.comap T₀ := hw
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ S'.comap T₀ := by rw [h]; trivial
      exact hv
  have hfin := hadm S inferInstance hSinv hSirr
  let e : W ≃ₗ[ℂ] S := LinearEquiv.ofInjective T₀ hinj
  refine Submodule.finiteDimensional_of_le
    (S₂ := sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)})
    (iSup₂_le fun T hT => ?_)
  let T' : H →ₗ[ℂ] H := T ∘ₗ (e.symm : S →ₗ[ℂ] W) ∘ₗ (S.orthogonalProjectionOnto : H →ₗ[ℂ] S)
  have hT' : ∀ v, T' (T₀ v) = T v := by
    intro v
    have he : ((e v : S) : H) = T₀ v := LinearEquiv.ofInjective_apply _ v
    simp only [T', LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← he, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  refine le_sSup ⟨T', ?_, ?_⟩
  · have hc : T' ∘ₗ T₀ = T := LinearMap.ext hT'
    rw [← hc, LinearMap.range_comp]
  · rintro k _ ⟨v, rfl⟩
    rw [← hT₀, hT', hT', hT]

theorem finiteDimensional_isoPart {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖)
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    (d : ℕ) : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W),
      Module.finrank ℂ W = d → FiniteDimensional ℂ (isoPart π ρ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W _ _ _ ρ hd
  by_cases hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤
  · exact finiteDimensional_isoPart_of_simple hadm ρ hs
  push Not at hs
  obtain ⟨W', hW, hbot, htop⟩ := hs
  have h1 : Module.finrank ℂ W' < d := hd ▸ Submodule.finrank_lt htop
  have h2 : Module.finrank ℂ (W ⧸ W') < d := by
    have hsum := Submodule.finrank_quotient_add_finrank W'
    have hpos : 0 < Module.finrank ℂ W' :=
      Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.1 h)
    omega
  have := ih _ h1 W' (ρ.subrepresentation W' hW) rfl
  have := ih _ h2 (W ⧸ W') (ρ.quotient W' hW) rfl
  exact Submodule.finiteDimensional_of_le (isoPart_le_sup hπ ρ W' hW)

end GlobalTheory.CompanionTheory.AdmGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariant
section
namespace GlobalTheory.CompanionTheory.TopGroup

theorem finite_image_of_right_invariant_near_one :
    ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ),
      IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) →
        (Gf '' K).Finite := by
  intro Γ X _ _ _ K hK Gf hS
  have hU : ∀ k ∈ K, {y : Γ | k⁻¹ * y ∈ {s : Γ | ∀ x, Gf (x * s) = Gf x}} ∈ nhds k := by
    intro k _
    have hc : Continuous fun y : Γ => k⁻¹ * y := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds ?_
    show _ ∈ nhds (k⁻¹ * k)
    rw [inv_mul_cancel]
    exact hS
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image Gf).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hcover hy)
  refine ⟨k, hk, ?_⟩
  have h := hyk k
  rw [mul_inv_cancel_left] at h
  exact h.symm

end GlobalTheory.CompanionTheory.TopGroup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjective
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.FlatCoker

theorem lTensor_rTensor_comm {R P Q X Y : Type} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (i : P →ₗ[R] Q) (g : X →ₗ[R] Y) (t : P ⊗[R] X) :
    g.lTensor Q (i.rTensor X t) = i.rTensor Y (g.lTensor P t) := by
  have h1 := LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor P i g) t
  have h2 := LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor P i g) t
  exact h1.trans h2.symm

theorem flat_quotient_range_of_lTensor_injective
    (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Flat R B] (f : A →ₗ[R] B)
    (hf : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) :
    Module.Flat R (B ⧸ LinearMap.range f) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  have hRrow := lTensor_exact R (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective (LinearMap.range f))
  have hIrow := lTensor_exact (↥I) (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective (LinearMap.range f))
  have hAcol := rTensor_exact A (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  have hBcol := rTensor_exact B (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  have hBinj : Function.Injective (LinearMap.rTensor B I.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (↥I)
    (Submodule.mkQ_surjective (LinearMap.range f)) z
  rw [← lTensor_rTensor_comm I.subtype (LinearMap.range f).mkQ y] at hz
  obtain ⟨x, hx⟩ := (hRrow _).mp hz
  have hq : LinearMap.lTensor (R ⧸ I) f (LinearMap.rTensor A I.mkQ x) = 0 := by
    rw [lTensor_rTensor_comm I.mkQ f x, hx]
    exact (hBcol _).mpr ⟨y, rfl⟩
  have hq0 : LinearMap.rTensor A I.mkQ x = 0 :=
    (injective_iff_map_eq_zero (LinearMap.lTensor (R ⧸ I) f)).mp (hf (R ⧸ I)) _ hq
  obtain ⟨w, rfl⟩ := (hAcol x).mp hq0
  have hyw : LinearMap.lTensor (↥I) f w = y := by
    apply hBinj
    rw [← hx]
    exact (lTensor_rTensor_comm I.subtype f w).symm
  rw [← hyw]
  exact (hIrow _).mpr ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.FlatCoker
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpace
section
open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FourierMat

noncomputable def entries (m n : ℕ) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x a j => x (a, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem entries_apply (m n : ℕ) (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    entries m n u p = u p.1 p.2 := rfl

theorem pairing {m n : ℕ} {s : ℂ} (hs : s ≠ 0) (w : EuclideanSpace ℂ (Fin m × Fin n))
    (v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)).re =
      -(⟪entries m n v, w⟫_ℝ) := by
  have key : s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)
      = -(∑ a, ∑ j, conj (w (a, j)) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_div₀, star_neg, Complex.star_def, Complex.conj_conj]
    field_simp
  rw [key, PiLp.inner_apply, Fintype.sum_prod_type, Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.inner]
  simp only [entries_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem fourier_uniqueness : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ,
    Continuous g → Integrable g →
    (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  intro m n s hs g hgc hgi hF
  have hemb : MeasurableEmbedding (entries m n) := (entries m n).toHomeomorph.measurableEmbedding
  have hC : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have hV1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have hV2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have : (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))).IsAddHaarMeasure :=
    (entries m n).isAddHaarMeasure_map volume
  have hμ := Measure.isAddLeftInvariant_eq_smul
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcomp : (fun x => g ((entries m n).symm x)) ∘ (entries m n) = g := by
    funext v
    simp
  have hGmap : Integrable (fun x => g ((entries m n).symm x))
      (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) :=
    hemb.integrable_map_iff.mpr (by rw [hcomp]; exact hgi)
  rw [hμ, ← Measure.coe_nnreal_smul] at hGmap
  have hGi : Integrable (fun x => g ((entries m n).symm x))
      (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n))) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hcpos.ne') ENNReal.coe_ne_top).mp hGmap
  have hGc : Continuous (fun x => g ((entries m n).symm x)) :=
    hgc.comp (entries m n).symm.continuous
  have hFG : FourierTransform.fourier (fun x => g ((entries m n).symm x)) = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h0 := hF (fun a j => -(w (a, j)) / conj s)
    have h1 : ∫ x, Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫_ℝ) * Complex.I) • g ((entries m n).symm x)
        ∂(Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) = 0 := by
      rw [hemb.integral_map]
      refine Eq.trans ?_ h0
      congr 1
      funext v
      rw [pairing hs w v]
      simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
      congr 2
      push_cast
      ring
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_zero] at h1
    exact h1.resolve_left (by exact_mod_cast hcpos.ne')
  have hinv := Continuous.fourierInv_fourier_eq hGc hGi
    (by rw [hFG]; exact integrable_zero _ _ _)
  rw [hFG] at hinv
  funext v
  have hx := congrFun hinv ((entries m n) v)
  rw [Real.fourierInv_eq'] at hx
  simp only [Pi.zero_apply, smul_zero, integral_zero, ContinuousLinearEquiv.symm_apply_apply] at hx
  rw [Pi.zero_apply]
  exact hx.symm

end GlobalTheory.CompanionTheory.FourierMat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionInvariantMatrix
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem fourier_prod_symm_preserving :
    ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  intro A _ _ ν _ ψ ι _ _ Bm hsym hemb hmap t f hf hint hinv
  have hψ : ∀ (s : Finset ι) (h : ι → A), ψ (∑ i ∈ s, h i) = ∏ i ∈ s, ψ (h i) := by
    intro s h
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  have hsplit : ∀ (g : A → ℂ) (x w : ι → A),
      (∏ i, g (x i)) * ψ (dotProduct x w) = ∏ i, (g (x i) * ψ (x i * w i)) := by
    intro g x w
    rw [Finset.prod_mul_distrib]
    congr 1
    exact hψ Finset.univ _
  have key : ∀ w : ι → A, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x w)
      ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (w i) := by
    intro w
    simp_rw [hsplit t]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => t x * ψ (x * w i))]
    exact Finset.prod_congr rfl fun i _ => (hf (w i)).symm
  refine ⟨fun y => key _, ?_, ?_⟩
  · have h1 : Integrable (fun w : ι → A => ∏ i, f (w i)) (Measure.pi fun _ : ι => ν) :=
      Integrable.fintype_prod (fun _ => hint)
    rw [← hmap] at h1
    exact (hemb.integrable_map_iff).1 h1
  · intro z
    have hdot : ∀ y : ι → A, dotProduct y (Bm.mulVec z) = dotProduct (Bm.mulVec y) z := by
      intro y
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose Bm y, ← hsym.eq]
      simp [hsym.eq]
    have hG : ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z))
          ∂(Measure.pi fun _ : ι => ν)
        = ∫ w : ι → A, (∏ i, f (w i)) * ψ (dotProduct w z)
          ∂((Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x)) := by
      rw [hemb.integral_map]
      simp_rw [hdot]
    rw [hG, hmap]
    simp_rw [hsplit f]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => f x * ψ (x * z i))]
    exact Finset.prod_congr rfl fun i _ => hinv (z i)

end GlobalTheory.CompanionTheory.BigCell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierParameterDerivative
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Analysis.OscPhase

private lemma norm_exp_two_pi_I_mul_real (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_integral_oscillating_phase
    (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ)
    (hM : Measurable M) (hg : Integrable g μ)
    (hMg : Integrable (fun y => (M y : ℂ) * g y) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ)
      (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  have hnorm : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := norm_exp_two_pi_I_mul_real
  have hmeasE : ∀ t : ℝ,
      Measurable fun y => Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) :=
    fun t => by fun_prop
  have hdiff : ∀ (y : X) (t : ℝ), HasDerivAt
      (fun t : ℝ => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
      (2 * Real.pi * Complex.I *
        ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))) t := by
    intro y t
    have h1 : HasDerivAt (fun t : ℝ => ((t * M y : ℝ) : ℂ)) ((M y : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).mul_const (M y)).ofReal_comp
    have h2 := ((h1.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul (g y)
    exact h2.congr_deriv (by ring)
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun (t : ℝ) y => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
    (F' := fun (t : ℝ) y => 2 * Real.pi * Complex.I *
      ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ))))
    (bound := fun y => ‖2 * Real.pi * Complex.I‖ * ‖(M y : ℂ) * g y‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      hg.aestronglyMeasurable.mul (hmeasE t).aestronglyMeasurable)
    (hg.mono (hg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [norm_mul, hnorm, mul_one]))
    ((hMg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable).const_mul _)
    (ae_of_all _ fun y t _ => by simp only [norm_mul, hnorm, mul_one, le_refl])
    (hMg.norm.const_mul _)
    (ae_of_all _ fun y t _ => hdiff y t)
  rwa [integral_const_mul] at hd

end GlobalTheory.CompanionTheory.Analysis.OscPhase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangular
section
open Matrix

namespace GlobalTheory.CompanionTheory.QR

theorem exists_unitary_mul_blockTriangular {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 fun i => g i j
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩
  have hmul := Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f
  rw [OrthonormalBasis.coe_toBasis] at hmul
  rw [hmul]
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

end GlobalTheory.CompanionTheory.QR
end

