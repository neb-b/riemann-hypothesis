module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isFibreFamily_transport {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure V) (ν : Measure R) (q q₂ : V → R) (e : V ≃ₜ V) (u : Rˣ) (a d : ℝ≥0) (hd : d ≠ 0)
    (hμ : μ = a • μ.map e) (hν : ν = d • ν.map (fun z => (u : R) * z))
    (hq : ∀ v, q₂ (e v) = u * q v) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν {c | IsUnit c} fib) :
    IsFibreFamily μ q₂ id Set.univ ν {c | IsUnit c}
      (fun b => (a * d⁻¹) • (fib ((u⁻¹ : Rˣ) * b)).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmu : MeasurableEmbedding (fun z : R => (u : R) * z) :=
    (Homeomorph.smul u : R ≃ₜ R).measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [Measure.smul_apply, hme.map_apply]
    have : e ⁻¹' (q₂ ⁻¹' {id b} ∩ Set.univ)ᶜ = (q ⁻¹' {id ((u⁻¹ : Rˣ) * b)} ∩ Set.univ)ᶜ := by
      ext v
      simp [hq, Units.eq_inv_mul_iff_mul_eq]
    rw [this, h1, smul_zero]
  · have h2' := h2 (φ ∘ e) (hφ.comp e.measurable)
    simp only [Measure.restrict_univ, Function.comp] at h2' ⊢
    have hL : ∫⁻ v, φ v ∂μ = (a : ℝ≥0∞) * ∫⁻ v, φ (e v) ∂μ := by
      conv_lhs => rw [hμ]
      rw [lintegral_smul_measure, hme.lintegral_map, ENNReal.smul_def, smul_eq_mul]
    rw [hL, h2']
    conv_rhs => rw [hν]
    rw [lintegral_smul_measure, hmu.lintegral_map]
    simp only [lintegral_smul_measure, hme.lintegral_map, Units.inv_mul_cancel_left,
      ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul]
    congr 2
    field_simp
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    have hmem : ∀ b ∈ {c : R | IsUnit c}, ((u⁻¹ : Rˣ) : R) * b ∈ {c : R | IsUnit c} :=
      fun b hb => (Units.isUnit _).mul hb
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (hme.integrable_map_iff.2 (h4 _ (hmem b hb))).smul_measure_nnreal
    · simp only [integral_smul_nnreal_measure, hme.integral_map]
      exact (h5.comp (continuous_const.mul continuous_id).continuousOn hmem).const_smul _

theorem lrAct_one_right {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S)
    (X : Fin n → Fin M → S) : lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

theorem exists_homeomorph_lrAct {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (hg : IsUnit g.det) :
    ∃ e : (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S), ⇑e = lrAct g 1 := by
  refine ⟨{ toFun := fun X a => g.mulVec (X a)
            invFun := fun X a => g⁻¹.mulVec (X a)
            left_inv := fun X => ?_
            right_inv := fun X => ?_
            continuous_toFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a)
            continuous_invFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a) }, ?_⟩
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg]
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hg]
  · funext X
    rw [lrAct_one_right]
    rfl

theorem fibAt_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hR M J J₂ lam ν β c m g hlam hν hg hc hq hfib
  obtain ⟨fib, hfib, rfl⟩ := hfib
  obtain ⟨hA, hred, -⟩ := _root_.GlobalTheory.GaugeEx.nice_tensor F E R hR
  have hμ := _root_.GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct (R ⊗[F] E) hA hred lam hlam 1 M g 1 hg (by simp)
  rw [Matrix.det_one, (modu_basic (R ⊗[F] E)).2.2.1, one_pow, mul_one, pow_one] at hμ
  obtain ⟨e, he⟩ := exists_homeomorph_lrAct (n := 1) g hg
  obtain ⟨hpos, hν'⟩ := (modu_basic R).1 c hc
  obtain ⟨u, rfl⟩ := hc
  rw [← he] at hμ ⊢
  refine ⟨_, isFibreFamily_transport _ ν _ _ e u _ _ hpos.ne' hμ (hν' ν hν) (fun X => ?_) fib hfib, ?_⟩
  · rw [he, lrAct_one_right]
    exact hq _
  · simp only [Units.inv_mul_cancel_left]

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints
section
namespace GlobalTheory.MixedSignature

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem compact_mod_stabiliser_of_minGe :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) {den : 𝓞 E} (_ : den ≠ 0) (_ : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, Orth X G p x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, MinGe X ε (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  intro r X G p hG den hden hint H hH x0 hx0 ε hε
  obtain ⟨-, -, hfr⟩ := unitary_group_frames r X p H hH
  obtain ⟨horth, ι, hιc, -, hιg⟩ := hfr x0 hx0
  obtain ⟨R, hR⟩ := exists_bound_orthonormal_frame X G p hG hden hint ε hε
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  refine ⟨ι '' {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R},
    (isCompact_orth_bounded r X G p R).image_of_continuousOn
      (hιc.mono fun x hx => hx.1), fun g hg => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := hR _ (horth g) hg
  obtain ⟨u, hu⟩ := exists_unitary_elem_of_isUStab r X H hH γ hγ
  have huΓ : u ∈ Γ := (hΓ u).2 ⟨γ, hγ, hu⟩
  refine ⟨u⁻¹, (hΓ _).1 (Γ.inv_mem huΓ), u * g, ⟨_, ⟨horth (u * g), ?_⟩, hιg (u * g)⟩,
    (inv_mul_cancel_left u g).symm⟩
  have key : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) x0 = lact γ (X.lmulC (fun τ =>
        (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
    funext τ
    change (((u : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) * mat x0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ)
    rw [hu, Matrix.mul_assoc]
  rw [key]
  exact hb

theorem exists_finite_measure_cover : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) {den : 𝓞 E} (_ : den ≠ 0) (_ : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (x0 : Frame X.Ψ r) (_ : Orth X G p x0) (_ : ∀ τ, p τ ≤ r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro r X G p hG den hden hint x0 hx0 hple H hH _ _ ν _
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  suffices hS : ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w by
    obtain ⟨Ω, h1, h2, h3⟩ := hS
    refine ⟨Ω, h1, h2, fun g => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := h3 g
    obtain ⟨γ, hγ, hγu⟩ := (hΓ u).1 hu
    refine ⟨γ, hγ, w, hw, fun τ => ?_⟩
    rw [← hγu τ]
    simp
  by_cases hp : ∀ τ, p τ = 0 ∨ p τ = r
  · have : CompactSpace H := compactSpace_unitary_of_definite r X H hH hp x0 hx0
    exact ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top,
      fun g => ⟨1, Γ.one_mem, g, Set.mem_univ _, (one_mul g).symm⟩⟩
  · obtain ⟨τ0, hp⟩ := not_forall.1 hp
    have hp0 : 0 < p τ0 := Nat.pos_of_ne_zero fun h => hp (Or.inl h)
    have hpr : p τ0 < r := lt_of_le_of_ne (hple τ0) fun h => hp (Or.inr h)
    obtain ⟨hlc, hsc, -⟩ := unitary_group_frames r X p H hH
    obtain ⟨σ, _, _, h, f, c, b, hk, hf, hf0, hinv, hc0, hc1, hb, hdrift, hsub⟩ :=
      exists_drift_function r X G p hG τ0 H hH hp0 hpr x0 hx0
    obtain ⟨U, hU, hU1⟩ := gamDisc r X H hH
    refine GlobalTheory.exists_finite_measure_cover_of_drift_function H ν Γ σ h f c b
      ⟨U, hU, fun γ hγ => hU1 γ ((hΓ γ).1 hγ)⟩ hk hf hf0
      (fun γ hγ => hinv γ ((hΓ γ).1 hγ)) hc0 hc1 hb hdrift fun M => ?_
    obtain ⟨ε, hε, hM⟩ := hsub M
    obtain ⟨K, hK, hKc⟩ := compact_mod_stabiliser_of_minGe r X G p hG hden hint H hH x0 hx0 ε hε
    refine ⟨K, hK, fun g hg => ?_⟩
    obtain ⟨u, hu, k, hk, e⟩ := hKc g (hM g hg)
    exact ⟨u, (hΓ u).2 hu, k, hk, e⟩

end


open NumberField in
theorem exists_cmType_finite_measure_cover : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro E _ _ _ r G Λ hh hG hfg hsp
  obtain ⟨X, rfl⟩ := GlobalTheory.Member.LatData.exists_data_lattice E r Λ hfg hsp
  obtain ⟨den, hden, hint⟩ := GlobalTheory.HermDen.exists_den E r G X.Λ hfg
  choose p hp P _ hP using fun τ : X.Ψ => GlobalTheory.HermSignature.exists_le_gram_eq_sgn E r G hh hG τ.1
  exact ⟨X.Ψ, X.cmType, exists_finite_measure_cover r X G p hG hden hint P hP hp⟩

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem finite_covolume_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w :=
  GlobalTheory.Mem.CovolTransport.finite_covolume_real_points exists_cmType_finite_measure_cover

end GlobalTheory.MixedSignature
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumPairsAboveEqAffineHyperplane
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.AboveSum

variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem mem_of_one {res : R →+* k} {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem smul_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ) {t : R}
    (ht : res t = 0) {e : V} (he : q.f e = 1) : t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ (mem_of_one h he), by rw [h.smul _ _ (mem_of_one h he), ht, zero_mul]⟩

theorem sub_mem_ker {res : R →+* k} {q : Pr R V k} {Λ : Submodule R V} (h : q.Ok res) (hk : q.IsKer Λ)
    {e : V} (he : q.f e = 1) {y : V} (hy : y ∈ q.L) {a : R} (ha : res a = q.f y) : y + (-a) • e ∈ Λ := by
  have he' := mem_of_one h he
  refine (hk _).2 ⟨q.L.add_mem hy (q.L.smul_mem _ he'), ?_⟩
  rw [h.add _ hy _ (q.L.smul_mem _ he'), h.smul _ _ he', he, map_neg, ha]
  ring

theorem le_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) {y : V} (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  obtain ⟨a, ha⟩ := hres (q.f y)
  have h1 := sub_mem_ker h hk he hy ha
  have h2 := (hk' _).1 (Λ.add_mem h1 (Λ.smul_mem a hd))
  have h3 := mem_of_one h' he'
  have e0 : y = (y + (-a) • e + a • (e - e')) + a • e' := by
    rw [smul_sub, neg_smul]; abel
  have h4 := q'.L.smul_mem a h3
  constructor
  · rw [e0]; exact q'.L.add_mem h2.1 h4
  · have h5 := h'.add _ h2.1 _ h4
    rw [← e0, h2.2, h'.smul _ _ h3, he', ha] at h5
    rw [h5]; ring

theorem eq_of_ker {res : R →+* k} (hres : Function.Surjective res) {q q' : Pr R V k} {Λ : Submodule R V}
    (h : q.Ok res) (hk : q.IsKer Λ) (h' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1)
    (he' : q'.f e' = 1) (hd : e - e' ∈ Λ) : q = q' := by
  have hd' : e' - e ∈ Λ := by rw [← neg_sub]; exact Λ.neg_mem hd
  ext y
  · exact ⟨fun hy => (le_of_ker hres h hk h' hk' he he' hd hy).1,
      fun hy => (le_of_ker hres h' hk' h hk he' he hd' hy).1⟩
  · by_cases hy : y ∈ q.L
    · exact (le_of_ker hres h hk h' hk' he he' hd hy).2.symm
    · rw [h.off y hy, h'.off y (fun hy' => hy (le_of_ker hres h' hk' h hk he' he hd' hy').1)]

theorem finsum_above : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [AddCommMonoid M] (res : R →+* k) (t : R) (p : Pr R V k) (π : V → W) (φ : Module.Dual k W) (q : W → Pr R V k) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L) → Red res t p.L π → (∀ x ∈ p.L, p.f x = φ (π x)) → (∀ w, φ w = 1 → (q w).Ok res ∧ (q w).IsKer p.L ∧ ∃ e, (q w).f e = 1 ∧ π (t • e) = w) → ∑ᶠ q' ∈ {q' | Pr.Inc res t p q'}, Φ q' = ∑ᶠ w ∈ {w | φ w = 1}, Φ (q w) := by
  intro R V k W M _ _ _ _ _ _ _ res t p π φ q Φ hres ht htf hsat hred hf hq
  symm
  refine finsum_mem_eq_of_bijOn q ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro w hw
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    refine ⟨h1, h2, e, h3, ?_⟩
    rw [hf _ (smul_mem_ker h1 h2 ht h3), h4]
    exact hw
  · intro w hw w' hw' hww
    obtain ⟨h1, h2, e, h3, h4⟩ := hq w hw
    obtain ⟨-, -, e', h3', h4'⟩ := hq w' hw'
    rw [← hww] at h3'
    have hd : e + (-1 : R) • e' ∈ p.L :=
      sub_mem_ker h1 h2 h3' (mem_of_one h1 h3) (by rw [map_one, h3])
    have e0 : t • e = t • e' + t • (e + (-1 : R) • e') := by
      rw [neg_smul, one_smul, smul_add, smul_neg]; abel
    rw [← h4, ← h4', e0, hred.add _ (smul_mem_ker h1 h2 ht h3') _ (p.L.smul_mem _ hd), hred.smul _ _ hd, ht,
      zero_smul, add_zero]
  · rintro q' ⟨h1', h2', e', h3', h4'⟩
    have hm' := smul_mem_ker h1' h2' ht h3'
    have hw : φ (π (t • e')) = 1 := by rw [← hf _ hm', h4']
    refine ⟨π (t • e'), hw, ?_⟩
    obtain ⟨h1, h2, e, h3, h4⟩ := hq _ hw
    have hm := smul_mem_ker h1 h2 ht h3
    have h0 : π (t • e + (-1 : R) • t • e') = 0 := by
      rw [hred.add _ hm _ (p.L.smul_mem _ hm'), hred.smul _ _ hm', h4, map_neg, map_one, neg_smul, one_smul,
        add_neg_cancel]
    obtain ⟨y, hy, s, hs, hsy⟩ := (hred.ker _ (p.L.add_mem hm (p.L.smul_mem _ hm'))).1 h0
    have h5 : s • (e - e') - y = 0 := by
      apply htf
      rw [smul_sub, ← hsy, smul_comm t s, neg_smul, one_smul, smul_sub t, sub_eq_add_neg (t • e), sub_self]
    refine eq_of_ker hres h1 h2 h1' h2' h3 h3' (hsat s _ hs ?_)
    rw [sub_eq_zero.1 h5]; exact hy

end GlobalTheory.LevelHecke.AboveSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem kerAlg_exponent {P Q : ℕ} (B : Matrix (Fin P) (Fin Q) ℂ) (C : Matrix (Fin Q) (Fin P) ℂ)
    (h : IsUnit (1 - C * B).det) (a c : Fin P → ℂ) (b d s u : Fin Q → ℂ) :
    -(b ⬝ᵥ s) + -(d ⬝ᵥ u) + (a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
      + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c) =
    ((a + s ᵥ* C) ⬝ᵥ (c + B *ᵥ u) - s ⬝ᵥ u) -
      (a ᵥ* B + d - s ᵥ* (1 - C * B)) ⬝ᵥ (1 - C * B)⁻¹ *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) := by
  have h1 := Matrix.nonsing_inv_mul _ h
  have h2 := Matrix.mul_nonsing_inv _ h
  generalize (1 - C * B)⁻¹ = N at h1 h2 ⊢
  have h3 : C * B * N = N - 1 := by rw [← h2, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  have h4 : N * (C * B) = N - 1 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have hM : (1 - B * C)⁻¹ = 1 + B * N * C := by
    apply Matrix.inv_eq_right_inv
    have : B * C * (B * N * C) = B * (C * B * N) * C := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, this, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_one]
    abel
  have hMB : (1 + B * N * C) * B = B * N := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h4, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hM, hMB]
  have e1 : N *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) = u - N *ᵥ (b + C *ᵥ c) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_neg]; abel
  have e2 : (s ᵥ* (1 - C * B)) ⬝ᵥ N *ᵥ (b + C *ᵥ c) = s ⬝ᵥ (b + C *ᵥ c) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e1, dotProduct_sub, sub_dotProduct _ _ (N *ᵥ _), e2]
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, ← Matrix.dotProduct_mulVec, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    dotProduct_comm b s]
  ring

theorem kerAlg_proj {P Q : ℕ} (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det)
    (h' : IsUnit Y'.toRows₂.det) :
    Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q =
      Matrix.fromRows (matA Y') 1 * (1 - (matA Y)ᴴ * matA Y')⁻¹ * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
  have hH : IsUnit (Y.toRows₂ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h.star
  have e0 : Yᴴ * Jm P Q * Y' = (-Y.toRows₂ᴴ) * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
    rw [Matrix.neg_mul, Matrix.neg_mul, ← form_factor Y Y' h h', neg_neg]
  have e1 : Yᴴ * Jm P Q = (-Y.toRows₂ᴴ) * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
    conv_lhs => rw [frame_eq Y h]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, baseY, Jm, Formalism.UG.Jpq,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.neg_mul,
      ← Matrix.mul_neg]
    congr 1
    ext i (j | j) <;> simp
  have hN : IsUnit (-Y.toRows₂ᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det] at hH ⊢; exact hH.neg
  rw [e0, Matrix.mul_assoc _ Yᴴ, e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e2 := frame_eq Y' h'
  generalize matA Y' = B at e2 ⊢
  generalize Y'.toRows₂ = Z at e2 h' ⊢
  subst e2
  simp only [Matrix.mul_assoc, baseY]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h', Matrix.nonsing_inv_mul_cancel_left _ _ hN]

theorem kerAlg : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  intro P Q Y Y' v φ v' φ' h h' hK A B a b c d M N
  have hs : star (scal Y v φ) = ((Y.toRows₂ᴴ).det)⁻¹ * Complex.exp (-(b ⬝ᵥ star (v ∘ Sum.inr))) := by
    rw [scal, star_mul', star_inv₀, Matrix.det_conjTranspose, Complex.star_def, ← Complex.exp_conj]
    congr 2
    simp [b, dotProduct]
  have hs' : scal Y' v' φ' = (Y'.toRows₂.det)⁻¹ * Complex.exp (-(d ⬝ᵥ (v' ∘ Sum.inr))) := rfl
  have ha : star (v ∘ Sum.inl) = a + star (v ∘ Sum.inr) ᵥ* Aᴴ := by
    have : a = star (v ∘ Sum.inl - A *ᵥ (v ∘ Sum.inr)) := rfl
    rw [this, star_sub, Matrix.star_mulVec]; abel
  have hb : b = Aᴴ *ᵥ star (φ ∘ Sum.inl) + star (φ ∘ Sum.inr) := by
    have : b = star ((φ ∘ Sum.inl) ᵥ* A + φ ∘ Sum.inr) := rfl
    rw [this, star_add, Matrix.star_vecMul]
  have hc : v' ∘ Sum.inl = c + B *ᵥ (v' ∘ Sum.inr) := by
    have : c = v' ∘ Sum.inl - B *ᵥ (v' ∘ Sum.inr) := rfl
    rw [this]; abel
  have hd : d = (φ' ∘ Sum.inl) ᵥ* B + φ' ∘ Sum.inr := rfl
  have hJ1 : star v ᵥ* Jm P Q = Sum.elim (star (v ∘ Sum.inl)) (-star (v ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.vecMul_fromBlocks]
    ext (i | i) <;> simp [Matrix.vecMul_neg]
  have hJ2 : Jm P Q *ᵥ star φ = Sum.elim (star (φ ∘ Sum.inl)) (-star (φ ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_mulVec]
    ext (i | i) <;> simp [Matrix.neg_mulVec]
  have e0 : (star v ᵥ* Jm P Q) ⬝ᵥ v' = (a + star (v ∘ Sum.inr) ᵥ* Aᴴ) ⬝ᵥ (c + B *ᵥ (v' ∘ Sum.inr))
      - star (v ∘ Sum.inr) ⬝ᵥ (v' ∘ Sum.inr) := by
    rw [← ha, ← hc, hJ1]
    simp [dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]
  have e1 : (star v ᵥ* Jm P Q + φ') ᵥ* Matrix.fromRows B 1 =
      a ᵥ* B + d - star (v ∘ Sum.inr) ᵥ* (1 - Aᴴ * B) := by
    have : star v ᵥ* Jm P Q + φ' = Sum.elim (star (v ∘ Sum.inl) + φ' ∘ Sum.inl)
        (-star (v ∘ Sum.inr) + φ' ∘ Sum.inr) := by
      rw [hJ1]; ext (i | i) <;> rfl
    rw [this, Matrix.sumElim_vecMul_fromRows, ha, hd]
    simp only [Matrix.add_vecMul, Matrix.vecMul_one, Matrix.vecMul_sub, Matrix.vecMul_vecMul]
    abel
  have e2 : Matrix.fromCols (-Aᴴ) 1 *ᵥ (Jm P Q *ᵥ star φ + v') =
      -(b + Aᴴ *ᵥ c) + (1 - Aᴴ * B) *ᵥ (v' ∘ Sum.inr) := by
    have : Jm P Q *ᵥ star φ + v' = Sum.elim (star (φ ∘ Sum.inl) + v' ∘ Sum.inl)
        (-star (φ ∘ Sum.inr) + v' ∘ Sum.inr) := by
      rw [hJ2]; ext (i | i) <;> rfl
    rw [this, Matrix.fromCols_mulVec_sumElim, hb]
    conv_lhs => rw [hc]
    simp only [Matrix.mulVec_add, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.neg_mulVec,
      Matrix.neg_mul]
    abel
  have key := kerAlg_exponent B Aᴴ hK a c b d (star (v ∘ Sum.inr)) (v' ∘ Sum.inr)
  rw [ker, kerAlg_proj Y Y' h h', form_factor Y Y' h h', ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _ * _),
    ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _), Matrix.dotProduct_mulVec _ (Matrix.fromRows _ _), e0, e1, e2,
    ← key, hs, hs', Complex.exp_add (-_ + -_), Complex.exp_add (-_) (-_), Matrix.det_mul, Matrix.det_mul]
  simp only [mul_inv, M, N, A, B]
  ring

end GlobalTheory.OscGauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorPropertiesStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralPointsFinitePlaceTensor_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (intV b v) ∧ IsOpen (intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : Fv F v ⊗[F] E) ∈ intV b v ∧ (∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) ∧ ∀ y ∈ intV b v, sigR (Fv F v) σ y ∈ intV b v) ∧ (∀ z : AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, prV v z ∈ intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, intV b v = intV b' v := by
  first | exact @GlobalTheory.GaugeEx.IntBasis.main | exact GlobalTheory.GaugeEx.IntBasis.main | (intros; apply GlobalTheory.GaugeEx.IntBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartierStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier : ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I → IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  first | exact @GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | exact GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | (intros; apply GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem isUnit_det_one_sub_conjTranspose_mul_of_contractions (P Q : ℕ)
    (A B : Matrix (Fin P) (Fin Q) ℂ) (hA : (1 - Aᴴ * A).PosDef) (hB : (1 - Bᴴ * B).PosDef) :
    IsUnit (1 - Aᴴ * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef :=
    (hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)
  have heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)
      = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [heq] at hsum
  have hpos := hsum.dotProduct_mulVec_pos hu
  have h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]
    simp
  rw [Matrix.add_mulVec, dotProduct_add, h0, h2] at hpos
  simp at hpos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponentsStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  first | exact @GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding | exact GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding | (intros; apply GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding <;> assumption)
end

