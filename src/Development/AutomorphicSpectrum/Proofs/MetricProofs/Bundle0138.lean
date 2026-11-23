module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitaryRepresentation
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic

theorem conj_unitary {ι : Type} [Fintype ι] (M G : Matrix ι ι ℂ)
    (h : (M.map (starRingEnd ℂ))ᵀ * G.map (starRingEnd ℂ) * M = G.map (starRingEnd ℂ)) :
    (M.map (starRingEnd ℂ))ᴴ * G * M.map (starRingEnd ℂ) = G := by
  have h2 := congrArg (fun X : Matrix ι ι ℂ => X.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (G.map (starRingEnd ℂ)).map (starRingEnd ℂ) = G := by ext i k; simp
  have e2 : ((M.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ := by
    ext i k; simp [Matrix.conjTranspose_apply]
  rw [e1, e2] at h2
  exact h2

theorem tm_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), (∀ (a b : C.Arch) τ, C.tm (a * b) τ = C.tm a τ * C.tm b τ) ∧ (∀ τ, C.tm 1 τ = 1) ∧ (∀ (a : C.Arch) τ, (C.tm a τ)ᴴ * C.gr τ * C.tm a τ = C.gr τ) ∧ ∀ τ, Continuous fun a : C.Arch => C.tm a τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp [Matrix.map_mul]
  · intro τ
    simp only [LatEmb.tm, tauMat]
    split_ifs with h
    · simp
    · simp
  · intro a τ
    have hm := mem_archUnitary.1 a.2 (plc F τ)
    simp only [LatEmb.tm, tauMat, LatEmb.gr]
    by_cases h0 : (plc F τ).embedding = embOf (F.σ τ)
    · rw [if_pos h0]
      rw [gramAt, h0] at hm
      have e : ((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)ᴴ =
          (((a.1 (plc F τ) : GL (Fin (j + j')) ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map
            (starRingEnd ℂ))ᵀ := by
        ext i k; simp [Matrix.conjTranspose_apply]
      rw [e]
      exact hm
    · have h' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) :=
        (InfinitePlace.embedding_mk_eq (embOf (F.σ τ))).resolve_left h0
      rw [if_neg h0]
      apply conj_unitary
      have e : gramAt C.h (Pi.basisFun E (Fin (j + j'))) (plc F τ) =
          ((gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))).map (starRingEnd ℂ) := by
        rw [gramAt, h']
        ext i k
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e] at hm
      exact hm
  · intro τ
    simp only [LatEmb.tm, tauMat]
    have hc : Continuous fun a : C.Arch =>
        ((a.1 (plc F τ) : GL _ ℂ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) :=
      Units.continuous_val.comp ((continuous_apply (plc F τ)).comp continuous_subtype_val)
    split_ifs with h
    · exact hc
    · exact hc.matrix_map Complex.continuous_conj

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjective
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

section TmSurj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (x : 𝓞 E) : embOf s (x : E) = s x :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) x


omit [IsCMField E] in
theorem embOf_restrict (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) x


omit [IsCMField E] in
theorem embOf_conj (s : 𝓞 E →+* ℂ) : embOf ((starRingEnd ℂ).comp s) = ComplexEmbedding.conjugate (embOf s) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  have h1 := embOf_coe ((starRingEnd ℂ).comp s) x
  have h2 := embOf_coe s x
  simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq]
  change embOf ((starRingEnd ℂ).comp s) (x : E) = starRingEnd ℂ (embOf s (x : E))
  rw [h1, h2]; rfl


omit [IsCMField E] in
theorem embOf_inj {s s' : 𝓞 E →+* ℂ} (h : embOf s = embOf s') : s = s' := by
  ext x
  rw [← embOf_coe s, ← embOf_coe s', h]

variable {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact F.cm.1 (embOf_inj h)
    · exfalso
      rw [← embOf_conj] at h
      have h' := embOf_inj h
      exact (F.cm.2 (F.σ τ)).1 ⟨τ, rfl⟩ ⟨τ', h'.symm⟩
  · intro w
    by_cases hs : ∃ τ, F.σ τ = w.embedding.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := hs
      refine ⟨τ, ?_⟩
      simp only [plc, hτ, embOf_restrict, InfinitePlace.mk_embedding]
    · have := not_imp_not.2 (F.cm.2 (w.embedding.comp (algebraMap (𝓞 E) E))).2 hs
      obtain ⟨τ, hτ⟩ := not_not.1 this
      refine ⟨τ, ?_⟩
      have : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ, ← RingHom.comp_assoc, embOf_restrict]; rfl
      simp only [plc, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

end TmSurj

theorem tm_surj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C b hb
  classical
  have hbij := plc_bijective F
  let e : Ψ ≃ InfinitePlace E := Equiv.ofBijective (plc F) hbij
  have he : ∀ τ, e.symm (plc F τ) = τ := fun τ => e.symm_apply_apply τ
  have hw : ∀ w, plc F (e.symm w) = w := fun w => e.apply_symm_apply w
  let v := Pi.basisFun E (Fin (j + j'))
  let M : InfinitePlace E → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun w =>
    if w.embedding = embOf (F.σ (e.symm w)) then b (e.symm w) else (b (e.symm w)).map (starRingEnd ℂ)
  have hct : ∀ X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i k; simp [Matrix.conjTranspose_apply]
  have hM : ∀ w, ((M w).map (starRingEnd ℂ))ᵀ * gramAt C.h v w * M w = gramAt C.h v w := by
    intro w
    have hτ := hb (e.symm w)
    rw [hct]
    by_cases hc : w.embedding = embOf (F.σ (e.symm w))
    · have hg : gramAt C.h v w = C.gr (e.symm w) := by
        simp only [gramAt, LatEmb.gr, hc]; rfl
      simp only [M, if_pos hc, hg]
      exact hτ
    · have hconj : w.embedding = ComplexEmbedding.conjugate (embOf (F.σ (e.symm w))) := by
        have h1 : InfinitePlace.mk (embOf (F.σ (e.symm w))) = InfinitePlace.mk w.embedding := by
          rw [InfinitePlace.mk_embedding]; exact hw w
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · exact absurd h.symm hc
        · exact h.symm
      have hg : gramAt C.h v w = (C.gr (e.symm w)).map (starRingEnd ℂ) := by
        ext i k
        simp only [gramAt, LatEmb.gr, Matrix.map_apply, hconj]
        rfl
      have h2 := congrArg (fun X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ => X.map (starRingEnd ℂ)) hτ
      simp only [Matrix.map_mul] at h2
      have h3 : ((b (e.symm w)).map (starRingEnd ℂ))ᴴ = ((b (e.symm w))ᴴ).map (starRingEnd ℂ) := by
        ext i k; simp [Matrix.conjTranspose_apply]
      simp only [M, if_neg hc, hg]
      rw [h3]
      exact h2
  have hH : ∀ w, IsUnit (gramAt C.h v w).det := by
    intro w
    have := (isUnit_det_gram C.h v).map w.embedding
    rw [RingHom.map_det] at this
    exact this
  let a : InfinitePlace E → GL (Fin (j + j')) ℂ := fun w =>
    Matrix.nonsingInvUnit (M w) (isUnit_det_of_unitary (starRingEnd ℂ) (hH w) (hM w))
  have ha : a ∈ C.Arch := mem_archUnitary.2 fun w => hM w
  refine ⟨⟨a, ha⟩, fun τ => ?_⟩
  have haM : ∀ w, (a w : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = M w := fun w => rfl
  simp only [LatEmb.tm, tauMat, haM, M, he]
  by_cases hc : (plc F τ).embedding = embOf (F.σ τ)
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    ext i k
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse

theorem isOpen_posDef_hermitian {X κ : Type} [TopologicalSpace X] [Fintype κ]
    (M : X → Matrix κ κ ℂ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : κ → ℂ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (κ → ℂ) => (dotProduct (star p.2) ((M p.1).mulVec p.2)).re) :=
    Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd))
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : κ → ℂ) 1,
      0 < (dotProduct (star v) ((M x).mulVec v)).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0)).1
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul] at h1
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  have hre : 0 < (dotProduct (star v) ((M x).mulVec v)).re :=
    (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)
  have hstar : star (dotProduct (star v) ((M x).mulVec v)) = dotProduct (star v) ((M x).mulVec v) := by
    conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, (hs x).eq, ← Matrix.dotProduct_mulVec]
  have him : (dotProduct (star v) ((M x).mulVec v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
  exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem isOpen_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsOpen (ballDom q) := by
  have hset : ballDom q = ⋂ τ, {t | (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef} := by
    ext t
    simp [ballDom]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => isOpen_posDef_hermitian _ ?_ fun t => ?_
  · have hm : Continuous fun t : Fin n → ℂ => ballMat q t τ :=
      continuous_matrix fun a b => continuous_apply _
    exact continuous_const.sub (hm.matrix_conjTranspose.matrix_mul hm)
  · exact (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)

theorem exists_inverse : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  intro Ψ _ j j' n q Z G hZ hbij _ _
  have hJ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof
  obtain ⟨-, Y, hY, hYZ⟩ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof hJ n _ Z
    (isOpen_ballDom q) hZ hbij.injOn
  rw [hbij.image_eq] at hY
  refine ⟨Y, hY, fun t ht => ?_⟩
  obtain ⟨s, hs, hst⟩ := hbij.surjOn ht
  have hYt : Y t = s := by
    rw [← hst]
    exact hYZ s hs
  exact ⟨hYt ▸ hs, by rw [hYt, hst], hYZ t ht⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

theorem exists_sqLen {m : Type} [Fintype m] (x : m → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star x ⬝ᵥ x = (r : ℂ) ∧ (x ≠ 0 → 0 < r) := by
  have h0 : 0 ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
  have hz := Complex.nonneg_iff.1 h0
  have heq : star x ⬝ᵥ x = (((star x ⬝ᵥ x).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz.2.symm
  refine ⟨(star x ⬝ᵥ x).re, hz.1, heq, fun hx => ?_⟩
  have hp : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.2 hx
  exact (Complex.pos_iff.1 hp).1

theorem qf_one_sub {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ ((1 - Aᴴ * A) *ᵥ w) = star w ⬝ᵥ w - star (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
  rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

theorem posDef_adjoint {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    (h : (1 - Aᴴ * A).PosDef) : (1 - A * Aᴴ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · simp [IsHermitian, conjTranspose_sub, conjTranspose_mul]
  have hq := qf_one_sub Aᴴ v
  rw [conjTranspose_conjTranspose] at hq
  rw [hq]
  obtain ⟨c, hc0, hc, hcp⟩ := exists_sqLen v
  obtain ⟨a, ha0, ha, hap⟩ := exists_sqLen (Aᴴ *ᵥ v)
  rw [hc, ha, ← Complex.ofReal_sub]
  have hcpos := hcp hv
  suffices hac : a < c from by exact_mod_cast sub_pos.2 hac
  by_cases hw : Aᴴ *ᵥ v = 0
  · have : a = 0 := by
      have : (a : ℂ) = 0 := by rw [← ha, hw]; simp
      exact_mod_cast this
    rw [this]; exact hcpos
  have hapos := hap hw
  set w := Aᴴ *ᵥ v with hwdef
  obtain ⟨b, hb0, hb, -⟩ := exists_sqLen (A *ᵥ w)
  have hba : b < a := by
    have h1 := (posDef_iff_dotProduct_mulVec.1 h).2 hw
    rw [qf_one_sub, ha, hb, ← Complex.ofReal_sub] at h1
    have : (0 : ℝ) < a - b := by exact_mod_cast h1
    linarith
  have hpv : star (A *ᵥ w) ⬝ᵥ v = (a : ℂ) := by
    rw [star_mulVec, ← dotProduct_mulVec, ← hwdef, ha]
  have hvp : star v ⬝ᵥ (A *ᵥ w) = (a : ℂ) := by
    rw [dotProduct_mulVec, ← star_star (star v ᵥ* A)]
    rw [star_vecMul, star_star, ← hwdef, ha]
  have hu := dotProduct_star_self_nonneg ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v)
  have hexp : star ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) ⬝ᵥ ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) =
      ((c * (c * b - a ^ 2) : ℝ) : ℂ) := by
    simp only [star_sub, star_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, hb, hc, hpv, hvp]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    push_cast
    ring
  rw [hexp] at hu
  have hu' : 0 ≤ c * (c * b - a ^ 2) := by exact_mod_cast hu
  have h2 : 0 ≤ c * b - a ^ 2 := nonneg_of_mul_nonneg_right hu' hcpos
  nlinarith

theorem posDef_adjoint_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    (1 - Aᴴ * A).PosDef ↔ (1 - A * Aᴴ).PosDef :=
  ⟨posDef_adjoint A, fun h => by simpa using posDef_adjoint Aᴴ (by simpa using h)⟩

theorem posDef_blockDiagonal_iff {m o : Type} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (M : o → Matrix m m ℂ) : (blockDiagonal M).PosDef ↔ ∀ k, (M k).PosDef := by
  constructor
  · intro h k
    have hinj : Function.Injective (fun i : m => (i, k)) := fun a b hab => (Prod.ext_iff.1 hab).1
    have := h.submatrix hinj
    convert this using 1
    ext a b
    simp [blockDiagonal_apply]
  · intro h
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, blockDiagonal_conjTranspose]
      congr 1
      funext k
      exact (h k).1
    have hmv : ∀ i k, (blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ fun i => x (i, k)) i := by
      intro i k
      simp only [mulVec, dotProduct, Fintype.sum_prod_type_right, blockDiagonal_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    have hsum : star x ⬝ᵥ (blockDiagonal M *ᵥ x) =
        ∑ k, star (fun i => x (i, k)) ⬝ᵥ (M k *ᵥ fun i => x (i, k)) := by
      simp only [dotProduct, Fintype.sum_prod_type_right, hmv]
      rfl
    rw [hsum]
    obtain ⟨⟨i, k⟩, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun k _ => (h k).posSemidef.dotProduct_mulVec_nonneg _) ⟨k, Finset.mem_univ _, ?_⟩
    refine (posDef_iff_dotProduct_mulVec.1 (h k)).2 (Function.ne_iff.2 ⟨i, ?_⟩)
    simpa using hp

theorem posDef_fromBlocks_diag_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) : (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  constructor
  · intro h
    constructor
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inl : m → m ⊕ n) Sum.inl = A := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inl_injective
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inr : n → m ⊕ n) Sum.inr = D := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inr_injective
  · rintro ⟨hA, hD⟩
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, fromBlocks_conjTranspose, hA.1, hD.1]
      simp
    have hsum : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      rw [fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [hsum]
    have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    rcases p with i | i
    · refine add_pos_of_pos_of_nonneg ((posDef_iff_dotProduct_mulVec.1 hA).2 (Function.ne_iff.2 ⟨i, ?_⟩)) h2
      simpa using hp
    · refine add_pos_of_nonneg_of_pos h1 ((posDef_iff_dotProduct_mulVec.1 hD).2 (Function.ne_iff.2 ⟨i, ?_⟩))
      simpa using hp

theorem posDef_transpose_block {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (Z : Matrix m n ℂ) :
    (1 - Zᵀᴴ * Zᵀ).PosDef ↔ (1 - Zᴴ * Z).PosDef := by
  rw [posDef_adjoint_iff Z, ← PosDef.transpose_iff (M := 1 - Z * Zᴴ)]
  have : (1 - Z * Zᴴ)ᵀ = 1 - Zᵀᴴ * Zᵀ := by
    rw [transpose_sub, transpose_one, transpose_mul]
    congr 2
  rw [this]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ


open MemBall in
theorem mem_ballDom_iff_posDef_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  have hblk : (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t =
      blockDiagonal fun τ => fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0
        (1 - (ballMat q t τ)ᵀᴴ * (ballMat q t τ)ᵀ) := by
    rw [bigZ, blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
    congr 1
    funext τ
    simp only [Pi.sub_apply, Pi.one_apply]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [conjTranspose_zero, mul_zero, add_zero, zero_add, ← fromBlocks_one]
    ext (a | a) (c | c) <;> simp [Matrix.one_apply]
  have hsub : (1 : Matrix (Fin g) (Fin g) ℂ) - (bigZe e q t)ᴴ * bigZe e q t =
      ((1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    rw [bigZe, conjTranspose_submatrix, submatrix_mul_equiv]
    ext a c
    simp [Matrix.one_apply]
  have hequiv : ((1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm).PosDef ↔
      (1 - (bigZ q t)ᴴ * bigZ q t).PosDef :=
    ⟨fun h => by simpa using h.submatrix e.injective, fun h => h.submatrix e.symm.injective⟩
  rw [hsub, hequiv, hblk, MemBall.posDef_blockDiagonal_iff]
  simp only [MemBall.posDef_fromBlocks_diag_iff, MemBall.posDef_transpose_block, and_self]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

