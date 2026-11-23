module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreLintegralNeZeroOfPos
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.FibrePositive

theorem act_mul {P Q : ℕ} (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  have : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := rfl
  simp only [ActionCoordinates.act, this, Matrix.mulVec_mulVec]

theorem act_one {P Q : ℕ} (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := by
  have : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  simp only [ActionCoordinates.act, this, Matrix.one_mulVec]

theorem act_inv_of_fix {P Q : ℕ} {g : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (h : ActionCoordinates.act g x = x) :
    ActionCoordinates.act g⁻¹ x = x := by
  conv_lhs => rw [← h]
  rw [← act_mul, inv_mul_cancel, act_one]

theorem fibre_lintegral_ne_zero : ActionCoordinates.QuotientMeasure → CDHaar → ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : ActionCoordinates.Wsp P Q → ℝ, Continuous φ → 0 < φ x₀ → ∫⁻ y, ENNReal.ofReal (φ y) ∂(fib β) ≠ 0 := by
  intro hQ c P Q β hβ x₀ hx₀ fib hfib φ hφ hpos h0
  obtain ⟨h1, ⟨P', Q', j, ι, -, -, hfr⟩, h3⟩ := hQ P Q β hβ x₀ hx₀
  obtain ⟨htop, -, -, -, hbor, hcl⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  classical
  choose s0 hs0 using h1
  let s : ActionCoordinates.Wsp P Q → UpqT P Q := fun y => if h : ActionCoordinates.qf y = β then s0 y h else 1
  have hs : ∀ y, ActionCoordinates.qf y = β → ActionCoordinates.act (s y)⁻¹ x₀ = y := by
    intro y hy
    simp only [s, dif_pos hy]
    exact hs0 y hy
  have hc : Continuous fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x₀ :=
    (hcl.continuous.comp continuous_inv).matrix_mulVec continuous_const
  have hfc : Continuous fun g : UpqT P Q => ENNReal.ofReal (φ (ActionCoordinates.act g⁻¹ x₀)) :=
    ENNReal.continuous_ofReal.comp (hφ.comp hc)
  have key := (h3 P' Q' j ι hfr).2 c fib hfib s hs _ hfc.measurable
  have hφm : Measurable fun y => ENNReal.ofReal (φ y) :=
    (ENNReal.continuous_ofReal.comp hφ).measurable
  have hae := (lintegral_eq_zero_iff hφm).1 h0
  have hqm : MeasurableSet {y : ActionCoordinates.Wsp P Q | ActionCoordinates.qf y = β} := by
    have : Continuous (ActionCoordinates.qf : ActionCoordinates.Wsp P Q → ℝ) := by
      unfold ActionCoordinates.qf ActionCoordinates.herm
      fun_prop
    exact (isClosed_eq this continuous_const).measurableSet
  have hR : ∫⁻ y in {y | ActionCoordinates.qf y = β}, (∫⁻ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀))
      ∂(c.cd P' Q')) ∂(fib β) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hqm] with y hy hq
    have : ∀ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀)) = 0 := by
      intro g'
      rw [_root_.mul_inv_rev, act_mul, act_inv_of_fix (hfr.2.2 g').1, hs y hq]
      exact hy
    simp only [this, lintegral_zero, Pi.zero_apply]
  rw [hR, mul_zero] at key
  have := c.haar P Q
  have hz := (hfc.ae_eq_iff_eq (c.cd P Q) continuous_const).1 ((lintegral_eq_zero_iff hfc.measurable).1 key)
  have h1 : ENNReal.ofReal (φ (ActionCoordinates.act (1 : UpqT P Q)⁻¹ x₀)) = 0 := congrFun hz 1
  rw [inv_one, act_one, ENNReal.ofReal_eq_zero] at h1
  linarith

end GlobalTheory.FibrePositive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsBasisAtBlock
section
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchBasis

theorem mem_sumLat {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 K) (Fin n → K)) (t : K)
    (x : Fin N → K) :
    x ∈ Br.sumLat hN M t ↔ (fun a => x (Br.iC hN a)) ∈ M ∧ ∃ c : 𝓞 K, x (Br.iL hN) = (c : K) * t := Iff.rfl

theorem mem_colLat {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, ∀ a, ∑ j, (c j : K) * (B : Matrix (Fin n) (Fin n) K) a j = x a := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]

theorem colLat_block {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (t : K) (B : GL (Fin n) K)
    (B' : GL (Fin N) K) (h : IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t) :
    colLat B' = Br.sumLat hN (colLat B) t := by
  obtain ⟨h1, h2, h3⟩ := h
  ext x
  rw [mem_sumLat, mem_colLat, mem_colLat]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨fun j => c (Br.iC hN j), fun a => ?_⟩, c (Br.iL hN), ?_⟩
    · rw [← hc, sum_split hN]
      simp only [h1, (h2 _).1, mul_zero, add_zero]
    · rw [← hc, sum_split hN]
      simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add]
  · rintro ⟨⟨c, hc⟩, d, hd⟩
    refine ⟨fun j => if hj : j.val < n then c ⟨j.val, hj⟩ else d, fun a => ?_⟩
    rw [sum_split hN]
    have e1 : ∀ j : Fin n, (if hj : (Br.iC hN j).val < n then c ⟨(Br.iC hN j).val, hj⟩ else d) = c j :=
      fun j => dif_pos j.2
    have e2 : (if hj : (Br.iL hN).val < n then c ⟨(Br.iL hN).val, hj⟩ else d) = d := dif_neg (lt_irrefl n)
    simp only [e1, e2]
    rcases cases_idx hN a with rfl | ⟨a, rfl⟩
    · simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add, hd]
    · simp only [h1, (h2 _).1, mul_zero, add_zero]
      exact hc a

theorem localization_sumLat_le {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K))
    (M M₂ : Submodule (𝓞 K) (Fin n → K)) (t : K) (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M₂) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M t) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M₂ t) := by
  rintro x ⟨s, hs, hx1, c, hc⟩
  have h0 : (fun a => (s • x) (Br.iC hN a)) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx1⟩
  obtain ⟨u, hu, hux⟩ := h h0
  refine ⟨u * s, Submonoid.mul_mem _ hu hs, ?_⟩
  rw [mul_smul, mem_sumLat]
  refine ⟨hux, u * c, ?_⟩
  rw [Pi.smul_apply, hc, Algebra.smul_def]
  push_cast
  exact (mul_assoc _ _ _).symm

theorem isBasisAt_block : ∀ (K : Type) [Field K] [NumberField K] (N n : ℕ) (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (t : K) (B : GL (Fin n) K) (B' : GL (Fin N) K), IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t → IsBasisAt w M B → IsBasisAt w (Br.sumLat hN M t) B' := by
  intro K _ _ N n hN w M t B B' hB h
  unfold IsBasisAt at h ⊢
  rw [colLat_block hN t B B' hB]
  exact le_antisymm (localization_sumLat_le hN w _ _ t h.le) (localization_sumLat_le hN w _ _ t h.ge)

end GlobalTheory.BranchBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFundamentalDomainIffImageHA
section
noncomputable section

namespace GlobalTheory.VolIndepCompare

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

theorem isFundamentalDomain_iff_image {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁]
    [MeasurableSpace G₂] (φ : G₁ ≃* G₂) (hφ : Measurable φ) (hφ' : Measurable φ.symm)
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) (hΓ : ∀ h, h ∈ Γ₁ ↔ φ h ∈ Γ₂) (μ : Measure G₁) (𝓕 : Set G₁) :
    IsFundamentalDomain Γ₁ 𝓕 μ ↔ IsFundamentalDomain Γ₂ (φ '' 𝓕) (μ.map φ) := by
  let e : Γ₁ ≃ Γ₂ :=
    { toFun := fun g => ⟨φ g, (hΓ g).1 g.2⟩
      invFun := fun g => ⟨φ.symm g, (hΓ _).2 (by simp)⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  have hq : Measure.QuasiMeasurePreserving φ μ (μ.map φ) := ⟨hφ.aemeasurable, Measure.AbsolutelyContinuous.rfl⟩
  have hq' : Measure.QuasiMeasurePreserving φ.symm (μ.map φ) μ := by
    refine ⟨hφ'.aemeasurable, ?_⟩
    rw [Measure.map_map hφ' hφ]
    have : (φ.symm : G₂ → G₁) ∘ φ = id := by ext x; simp
    rw [this, Measure.map_id]
  constructor
  · intro h
    exact h.image_of_equiv φ.toEquiv hq' e.symm (fun g x => by
      change φ (φ.symm g * x) = (g : G₂) * φ x
      simp)
  · intro h
    have h2 := h.image_of_equiv φ.symm.toEquiv (ν := μ) hq e (fun g x => by
      change φ.symm (φ g * x) = (g : G₁) * φ.symm x
      simp)
    have h3 : φ.symm.toEquiv '' (φ '' 𝓕) = 𝓕 := by
      rw [Set.image_image]; simp
    rwa [h3] at h2

theorem isFundamentalDomain_iff_image_HA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ} (J₁ : Matrix (Fin M₁) (Fin M₁) E)
    (J₂ : Matrix (Fin M₂) (Fin M₂) E) (φ : HA R σ J₁ ≃ₜ* HA R σ J₂)
    (hΓ : ∀ h, h ∈ HFinIn R σ J₁ ↔ φ h ∈ HFinIn R σ J₂) (μ : Measure (HA R σ J₁)) (𝓕 : Set (HA R σ J₁)) :
    IsFundamentalDomain (HFinIn R σ J₁) 𝓕 μ ↔ IsFundamentalDomain (HFinIn R σ J₂) (φ '' 𝓕) (μ.map φ) := by
  have : BorelSpace (HA R σ J₁) := ⟨rfl⟩
  have : BorelSpace (HA R σ J₂) := ⟨rfl⟩
  exact isFundamentalDomain_iff_image (G₁ := HA R σ J₁) (G₂ := HA R σ J₂) φ.toMulEquiv
    φ.continuous.measurable φ.symm.continuous.measurable (HFinIn R σ J₁) (HFinIn R σ J₂) hΓ μ 𝓕

theorem conj_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (C : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) :
    GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.IsConjugationBy (AF F) σ J₁ J₂ C φ ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.IsConjBy σ J₁ J₂ C φ := Iff.rfl

theorem conclusion_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (C : Matrix (Fin M₂) (Fin M₁) E)
    (V₁ : Measure (HA (AF F) σ J₁) → Prop) (V₂ : Measure (HA (AF F) σ J₂) → Prop) :
    (∃ Φ : HA (AF F) σ J₁ ≃ₜ* HA (AF F) σ J₂,
        GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.IsConjugationBy (AF F) σ J₁ J₂ C Φ ∧
        (∀ h : HA (AF F) σ J₁, HA.mat (AF F) σ J₁ h ∈ HFin (AF F) σ J₁ ↔
            HA.mat (AF F) σ J₂ (Φ h) ∈ HFin (AF F) σ J₂) ∧
        (∀ μ : Measure (HA (AF F) σ J₁), V₁ μ ↔ V₂ (μ.map Φ)) ∧
        ∀ μ : Measure (HA (AF F) σ J₁), V₁ μ → ∀ 𝓕 : Set (HA (AF F) σ J₁),
            IsFundamentalDomain (HFinIn (AF F) σ J₁) 𝓕 μ ↔
              IsFundamentalDomain (HFinIn (AF F) σ J₂) (Φ '' 𝓕) (μ.map Φ)) ↔
    (∃ φ : HA (AF F) σ J₁ ≃ₜ* HA (AF F) σ J₂,
        GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.IsConjBy σ J₁ J₂ C φ ∧
        (∀ h, h ∈ HFinIn (AF F) σ J₁ ↔ φ h ∈ HFinIn (AF F) σ J₂) ∧
        (∀ μ : Measure (HA (AF F) σ J₁), V₁ μ ↔ V₂ (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF F) σ J₁)) (𝓕 : Set (HA (AF F) σ J₁)),
          IsFundamentalDomain (HFinIn (AF F) σ J₁) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF F) σ J₂) (φ '' 𝓕) (μ.map φ))) := by
  constructor
  · rintro ⟨Φ, a, b, c, -⟩
    exact ⟨Φ, (conj_iff σ J₁ J₂ C Φ).1 a, b, c, isFundamentalDomain_iff_image_HA (AF F) σ J₁ J₂ Φ b⟩
  · rintro ⟨Φ, a, b, c, d⟩
    exact ⟨Φ, (conj_iff σ J₁ J₂ C Φ).2 a, b, c, fun μ _ => d μ⟩

theorem lattice_iff (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.LatticeIndependence D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.LatticeIndep D := by
  constructor
  · intro h W P Q hs L hL hU μ
    exact h W P Q hs _ L _ _ hL hU μ
  · intro h W P Q hs L L' hL hU hL' hU' μ
    exact (h W P Q hs L hL hU μ).symm.trans (h W P Q hs L' hL' hU' μ)

theorem transport_iff (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.IsometryTransport D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.IsometryTransport D := by
  let _ := D.host.cmStar
  constructor
  · intro h W₁ W₂ P Q h₁ h₂ e he hc
    exact (conclusion_iff D.sp.cm.sig W₁.gram W₂.gram _ (IsVolMeas D W₁ P Q) (IsVolMeas D W₂ P Q)).1
      (h W₁ W₂ P Q h₁ h₂ e he hc)
  · intro h W₁ W₂ P Q h₁ h₂ e he hc
    exact (conclusion_iff D.sp.cm.sig W₁.gram W₂.gram _ (IsVolMeas D W₁ P Q) (IsVolMeas D W₂ P Q)).2
      (h W₁ W₂ P Q h₁ h₂ e he hc)

theorem volume_iff (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.VolumeInvariance D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolEqOfIsometric D := by
  constructor
  · intro h hV W₁ W₂ P Q h₁ h₂ e he
    exact h hV W₁ W₂ P Q h₁ h₂ ⟨e, he⟩
  · rintro h hV W₁ W₂ P Q h₁ h₂ ⟨e, he⟩
    exact h hV W₁ W₂ P Q h₁ h₂ e he

theorem volumeIndependence_iff (D : D7) :
    GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.VolumeIndependence D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  and_congr (lattice_iff D) (and_congr (transport_iff D) (volume_iff D))

end GlobalTheory.VolIndepCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
section
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchMembers

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

theorem lamTrue_lo (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (j : Fin R.k) (h : i.1 = j.1) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      (W.hc u τ).u j - ((R.k : ℚ) - 1) / 2 + (j.1 : ℚ) - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : i.1 < R.k := h ▸ j.2
  have e : (⟨i.1, hi⟩ : Fin R.k) = j := Fin.ext h
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dite_eq_left hi, e]
  unfold hcToWeightQ rhoVec
  ring

theorem lamTrue_hi (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (B ρ : ℕ) (hρ : ρ < R.t + 1)
    (h : i.1 = R.k + B * (R.t + 1) + ρ) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      -(RowPar.of (W.hc u τ)).eAt B + (R.k : ℚ) / 2 + (2 * (B : ℚ) + 1) * (((R.t : ℚ) + 1) / 2) -
        (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : ¬ i.1 < R.k := by omega
  have e1 : (i.1 - R.k) / (R.t + 1) = B := by
    have : i.1 - R.k = B * (R.t + 1) + ρ := by omega
    rw [this]
    exact (divmod (R.t + 1) B ρ hρ).1
  have hB : B < R.m := e1 ▸ R.blk_lt le_rfl i hi
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dite_eq_right hi, RowPar.eAt_of _ hB]
  simp only [e1]
  unfold wG
  push_cast
  ring

theorem sgTrue_entry (hW : W.Ok) (u : Word) (τ : X.Tau) (i : Fin (R.N R.m - 1)) :
    ((W.sgTrue τ).w i : ℚ) =
      (RowPar.of (W.hc u τ)).sgHC i.1 - RowPar.sh R - ((R.k : ℚ) - 2) / 2 - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) + (i.1 : ℚ) := by
  unfold Wts.sgTrue
  rw [← hW.hc_row u τ, RowPar.sgTrue_eq]
  unfold rhoVec
  have c1 : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    rw [Nat.cast_sub (R.N_pos R.m)]
    unfold Ranks.N
    push_cast
    ring
  rw [c1]
  ring

theorem nonneg_sub_of_lt {a b : ℤ} (h : (b : ℚ) - 1 < a) : 0 ≤ a - b := by
  have : b - 1 < a := by exact_mod_cast h
  omega

theorem interlace (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) := by
  intro i
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hs := sgTrue_entry W hW u τ i
  have hi : i.1 < R.k + R.m * (R.t + 1) - 1 := i.2
  have hS : (Br.iS (N_m_succ R) i).1 = i.1 + 1 := rfl
  have hC : (Br.iC (N_m_succ R) i).1 = i.1 := rfl
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  unfold Br.aBr Br.bBr
  by_cases h1 : i.1 < R.k - 1
  · rw [RowPar.sgHC_lo _ h1, RowPar.vb_lo _ h1] at hs
    have a1 := (W.hc u τ).u_gt_v ⟨i.1, h1⟩
    have a2 := (W.hc u τ).v_gt_u ⟨i.1, h1⟩
    have l1 := lamTrue_lo W u τ _ ⟨i.1 + 1, by omega⟩ hS
    have l2 := lamTrue_lo W u τ _ ⟨i.1, by omega⟩ hC
    simp only at a1 a2 l1 l2
    push_cast at l1
    exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩
  · obtain ⟨B, ρ, hρ, hn⟩ : ∃ B ρ, ρ < R.t + 1 ∧ i.1 = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(i.1 - (R.k - 1)) / (R.t + 1), (i.1 - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (i.1 - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    have l1 := lamTrue_hi W u τ _ B ρ hρ (by rw [hS]; omega : (Br.iS (N_m_succ R) i).1 = _)
    rw [hn] at hs
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ0
    · rw [Nat.add_zero, RowPar.sgHC_b] at hs
      push_cast [ck] at hs
      have g1 := RowPar.gap_be (W.hc u τ) hBm
      refine ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt ?_⟩
      rcases B with _ | B
      · have l2 := lamTrue_lo W u τ _ ⟨R.k - 1, by omega⟩ (by rw [hC]; simp only; omega : (Br.iC (N_m_succ R) i).1 = _)
        have a1 := (W.hc u τ).u_last_gt (by omega) hBm
        rw [RowPar.bAt_of _ hBm] at hs
        simp only [ck] at l2
        push_cast at hs
        linarith
      · have l2 := lamTrue_hi W u τ _ B R.t (by omega)
          (by rw [hC, hn, Nat.succ_mul]; omega : (Br.iC (N_m_succ R) i).1 = _)
        have g2 := RowPar.gap_eb (W.hc u τ) hBm
        push_cast at hs
        linarith
    · rw [RowPar.sgHC_e _ B ρ hρ0 (by omega)] at hs
      push_cast [ck] at hs
      have l2 := lamTrue_hi W u τ _ B (ρ - 1) (by omega) (by rw [hC]; omega : (Br.iC (N_m_succ R) i).1 = _)
      exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩

theorem members : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Members :=
  fun _ _ _ W hW u τ => ⟨interlace W hW u τ, members_sameShift W hW u τ⟩

end GlobalTheory.BranchMembers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeLevel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

theorem isSelfDualLat_iff {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]
    (σ : E →+* E) (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) :
    SelfDualStabiliserIndex.IsSelfDualLat σ J N ↔ SelfDualLatticeIndex.IsSelfDualLat σ J N :=
  and_congr_right fun _ => and_congr_right fun _ => eq_comm

theorem self_dual_lattice_iff_x0 (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    (letI := D.host.cmStar
     SelfDualStabiliserIndex.IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N) ↔
      SelfDualLatticeIndex.IsSelfDualDefiniteLattice D N :=
  isSelfDualLat_iff _ _ _

theorem indexAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    SelfDualStabiliserIndex.IndexAt D Lv u ↔ SelfDualLatticeIndex.IndexAt D Lv u :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun N =>
    imp_congr (self_dual_lattice_iff_x0 D N) Iff.rfl

theorem indexKU_iff : SelfDualStabiliserIndex.IndexKU ↔ SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => indexAt_iff D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualStabilizer
section
noncomputable section

namespace GlobalTheory.Proof.SelfDualStabilizer

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

theorem unramifiedAtFinite_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.UnramifiedAtFinite F E ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.UnramifiedAtFinite F E := by
  constructor
  · intro h P hP hne
    exact h ⟨P, hP, hne⟩
  · intro h P
    exact @h P.asIdeal P.isPrime P.ne_bot

section Clauses

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)


omit [NumberField F] [NumberField E] in
theorem isSelfDualLattice_iff (L : Submodule (𝓞 E) (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.IsSelfDualLat σ J L := Iff.rfl


omit [NumberField F] [NumberField E] in
theorem perpPart_eq (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.perpPart σ J (L : Set (Fin M → E)) x = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.perpIn σ J L x := rfl


omit [NumberField E] in
theorem stabHat_eq (S : Set (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.stabHat σ J S = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.stabLat (Af F) σ J (latHat F E S) :=
  Subgroup.ext fun _ => Iff.rfl


omit [NumberField E] in
theorem orbitClaims_iff (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims σ J (L : Set (Fin M → E)) x β ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl F E σ J L x β := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl
  rw [stabHat_eq, stabHat_eq, perpPart_eq]
  exact Iff.rfl

end Clauses

theorem stabTransitive_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_
  refine imp_congr (unramifiedAtFinite_iff F E) ?_
  refine forall_congr' fun M => forall_congr' fun J => imp_congr_right fun _ =>
    forall_congr' fun L => imp_congr (isSelfDualLattice_iff σ J L) ?_
  exact forall_congr' fun β => imp_congr_right fun _ => forall_congr' fun x =>
    imp_congr_right fun _ => imp_congr_right fun _ => orbitClaims_iff σ J L x β

end GlobalTheory.Proof.SelfDualStabilizer
end
end

