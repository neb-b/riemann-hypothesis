module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Master
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0139
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolModel
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

theorem qconj_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (x : E) :
    GroundTheory.Automorphic.conj (maximalRealSubfield E) E x = IsCMField.complexConj E x :=
  HermTrace.quadConj_eq_complexConj x

theorem sesq_eq_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (h : GroundTheory.Automorphic.HermitianForm (maximalRealSubfield E) E (Fin N → E)) (r : E) (x y : Fin N → E) :
    herm (r • (GroundTheory.Automorphic.gram h.toSesq (Pi.basisFun E (Fin N)))ᵀ) x y = r * h.toSesq y x := by
  rw [GroundTheory.Automorphic.sesq_eq_sum h.toSesq (Pi.basisFun E (Fin N)), herm, Finset.sum_comm]
  simp only [Finset.mul_sum, qconj_eq, Pi.basisFun_repr, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, cc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sgI_sq (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem stdModel_of (h : StdZ) : StdModel := by
  intro E _ _ _ Ψ _ _ j j' n g Λ _ _ H F ξ c₀ hc₀ hξ
  obtain ⟨C⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.exists_latEmb E Ψ j j' n g Λ H F
  obtain ⟨A, hA, Z, hbij, hmeas, hZ⟩ := h E Ψ j j' n g Λ F C
  obtain ⟨τ₀⟩ := ‹Nonempty Ψ›
  have hc := C.c_pos
  have hc₀' : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀.ne'
  have hξ0 : ξ ≠ 0 := fun h0 => by
    have := hξ τ₀
    rw [h0, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero hc₀' this.symm
  set r : E := C.xi / ξ with hr
  have hsr : ∀ τ, embOf (F.σ τ) r = ((C.c / c₀ * C.eps τ : ℝ) : ℂ) := fun τ => by
    rw [hr, map_div₀, C.xi_eq, hξ]
    push_cast
    field_simp
  have heps : ∀ τ, C.eps τ ≠ 0 := fun τ h0 => by
    have := C.eps_sq τ
    rw [h0] at this
    norm_num at this
  have hsr0 : ∀ τ, embOf (F.σ τ) r ≠ 0 := fun τ => by
    rw [hsr]
    exact_mod_cast mul_ne_zero (div_pos hc hc₀).ne' (heps τ)
  have hr0 : r ≠ 0 := fun h0 => hsr0 τ₀ (by rw [h0, map_zero])
  have hcr : cc r = r := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, hsr, Complex.conj_ofReal])
  set g₀ := GroundTheory.Automorphic.gram C.h.toSesq (Pi.basisFun E (Fin (j + j'))) with hg₀
  have hGs : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = embOf (F.σ τ) r • C.gr τ := fun τ => by
    ext a b
    simp [LatEmb.gr, hg₀]
  have hGs' : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = ((C.c / c₀ : ℝ) : ℂ) • C.sgr τ := fun τ => by
    rw [hGs, hsr, LatEmb.sgr, smul_smul, Complex.ofReal_mul]
  let e : Λ →ₗ[𝓞 E] (Fin (j + j') → E) :=
    { toFun := C.e, map_add' := C.e.map_add, map_smul' := fun a x => C.e_smul a x }
  let k : ℝ := Real.sqrt (c₀ / C.c)
  have hk : 0 < k := Real.sqrt_pos.2 (div_pos hc₀ hc)
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkk : (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) * k = 1 := by
    have : k * (C.c / c₀) * k = 1 := by
      have h1 : k * k = c₀ / C.c := Real.mul_self_sqrt (div_pos hc₀ hc).le
      rw [mul_right_comm, h1]
      field_simp
    exact_mod_cast this
  have hl : ∀ τ, C.cinv (A τ) τ * A τ = 1 := fun τ => by
    rw [LatEmb.cinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A τ)ᴴ, hA, sgI_sq]
  have hrr : ∀ τ, A τ * C.cinv (A τ) τ = 1 := fun τ =>
    (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (hl τ)
  have hform : ∀ x y, ((F.form x y : ℤ) : ℚ) = EFf (-ξ) (r • g₀ᵀ) (e x) (e y) := fun x y => by
    rw [C.form_eq, EFf, hg₀, sesq_eq_herm, neg_neg, ← mul_assoc, hr, mul_div_cancel₀ _ hξ0]
    rfl
  refine ⟨r • g₀ᵀ, e, fun τ => (k : ℂ) • A τ, fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ, Z, fun a b => ?_, ?_, C.e_inj, ⟨?_, ?_⟩,
    hform, fun τ => ⟨?_, ?_, ?_⟩, hbij, hmeas, fun γ hγ δ hδ t ht t' ht' => ?_⟩
  · have h1 : cc (g₀ b a) = g₀ a b := by
      rw [cc, ← qconj_eq]
      exact C.h.isSymm.eq _ _
    show cc (r * g₀ b a) = r * g₀ a b
    rw [← h1]
    conv_rhs => rw [← hcr]
    exact map_mul (IsCMField.complexConj E) _ _
  · rw [det_smul, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr0) (GroundTheory.Automorphic.isUnit_det_gram C.h _).ne_zero
  · have := (F.R 0).fin
    have : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ _ _
    exact Module.Finite.iff_fg.1 inferInstance
  · exact C.integral.isLattice.span_eq_top
  · rw [hGs', conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      hA, smul_smul, smul_smul]
    have : star (k : ℂ) * (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_ofReal, mul_right_comm, hkk]
    rw [this, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ hk', one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, mul_inv_cancel₀ hk', one_smul]
  · have hγ' : (γ : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * (r • g₀ᵀ) *
        (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = r • g₀ᵀ := hγ
    have hrho : rho (fun τ => embOf (F.σ τ)) (fun τ => (k : ℂ) • A τ) (fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ) γ =
        rho (fun τ => embOf (F.σ τ)) A (fun τ => C.cinv (A τ) τ) γ := by
      funext τ
      simp only [rho]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul]
    rw [hrho]
    refine hZ γ δ hδ (fun x y => ?_) (fun τ => ?_) t ht t' ht'
    · have h1 := hform (δ x) (δ y)
      rw [hδ, hδ, EFf, herm_mulVec', hγ', ← EFf, ← hform] at h1
      exact_mod_cast h1
    · have h1 := congrArg (fun M => (M.map (embOf (F.σ τ)))ᵀ) hγ'
      have h2 : (((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E)).map (embOf (F.σ τ)))ᵀ =
          ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)))ᴴ := by
        ext a b
        exact IsCMField.complexEmbedding_complexConj E (embOf (F.σ τ)) ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E) b a)
      simp only [Matrix.map_mul, transpose_mul] at h1
      rw [hGs, h2, ← Matrix.transpose_map, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul] at h1
      rw [Matrix.mul_assoc]
      exact smul_right_injective _ (hsr0 τ) h1

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolMoeb
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas PositivityTheory.EqVol

namespace Moeb

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem sgI_sq : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

def sinv (u : Matrix (Sg j j') (Sg j j') ℂ) : Matrix (Sg j j') (Sg j j') ℂ := sgI j j' * uᴴ * sgI j j'

theorem sinv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : sinv u * u = 1 := by
  unfold IsSgU at h
  rw [sinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, sgI_sq]

theorem mul_sinv {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : u * sinv u = 1 :=
  mul_eq_one_comm.1 (sinv_mul h)

theorem sinv_su {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : IsSgU (sinv u) := by
  have h1 := mul_sinv h
  unfold IsSgU at h ⊢
  conv_lhs => rw [← h]
  have : (sinv u)ᴴ * (uᴴ * sgI j j' * u) * sinv u = (u * sinv u)ᴴ * sgI j j' * (u * sinv u) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h1]
  simp

theorem moeb_one (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : moebBall q (fun _ => 1) t = t := by
  funext k
  have : ∀ W : Matrix (Fin j') (Fin j) ℂ, moebW (1 : Matrix (Sg j j') (Sg j j') ℂ) W = W := fun W => by
    rw [moebW, ← fromBlocks_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp
  simp [moebBall, ballPt, this, ballMat, Function.swap]

theorem moeb_maps (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {t : Fin n → ℂ} (ht : t ∈ ballDom q) : moebBall q u t ∈ ballDom q :=
  (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props Ψ j j' n q u hu).2.1 ht

theorem moeb_mul (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v w : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = w τ) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = moebBall q w t := by
  rw [← _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul Ψ j j' n q u v hu hv t ht, funext hw]

theorem moeb_inv (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = 1) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = t :=
  (moeb_mul q hu hv hw ht).trans (moeb_one q t)

theorem moeb_injOn (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ)) :
    Set.InjOn (moebBall q u) (ballDom q) := fun t ht t' ht' h => by
  rw [← moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht, h,
    moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht']

theorem moeb_meas (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    MeasurableSet (moebBall q u '' S) ∧ ballMeas q (moebBall q u '' S) = ballMeas q S := by
  obtain ⟨h1, h2, G, h3, h4⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props Ψ j j' n q u hu
  exact ⟨hS.image_of_continuousOn_injOn (h1.continuousOn.mono hSD) ((moeb_injOn q hu).mono hSD),
    ballMeas_image q h1 h2 (moeb_injOn q hu) (fun t ht => ballDens_transform q h1 h3 h2 h4 ht) hS hSD⟩

def ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (q'.symm.trans q)

theorem ren_apply (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (x : Ψ × Fin j × Fin j') :
    ren q q' t (q x) = t (q' x) := by
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) (q'.symm.trans q) t (q' x)
  simpa [ren] using this

theorem ballMat_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ballMat q (ren q q' t) = ballMat q' t := by
  funext τ
  ext a b
  simp [ballMat, ren_apply]

theorem ren_mem (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ren q q' t ∈ ballDom q ↔ t ∈ ballDom q' := by
  simp only [ballDom, Set.mem_setOf_eq, ballMat_ren]

theorem moeb_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) :
    moebBall q u (ren q q' t) = ren q q' (moebBall q' u t) := by
  funext k
  obtain ⟨x, rfl⟩ := q.surjective k
  rw [ren_apply]
  simp [moebBall, ballPt, ballMat_ren]

theorem ren_meas (q q' : Ψ × Fin j × Fin j' ≃ Fin n) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q') :
    ballMeas q (ren q q' '' S) = ballMeas q' S := by
  have hm : MeasurePreserving (ren q q') volume volume := volume_measurePreserving_piCongrLeft (fun _ => ℂ) _
  rw [ballMeas_apply q ((ren q q').measurableSet_image.2 hS) (by rintro _ ⟨t, ht, rfl⟩; exact (ren_mem q q' t).2 (hSD ht)),
    ballMeas_apply q' hS hSD, ← hm.setLIntegral_comp_emb (ren q q').measurableEmbedding]
  simp only [ballDens, ballPot, ballMat_ren]

theorem core (q : Ψ × Fin j × Fin j' ≃ Fin n) {G : Type} [Group G] [Countable G]
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (S S' : Set (Fin n → ℂ)) (h1 : ∀ τ, ρ 1 τ = 1)
    (hm : ∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) (hU : ∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) (hΓ : Γ ≤ U) (hΓ' : Γ' ≤ U)
    (hI : EqIdx Γ Γ') (hS : MFund q ρ Γ S) (hS' : MFund q ρ Γ' S') : ballMeas q S = ballMeas q S' := by
  have hD : MeasurableSet (ballDom q) := (BallInverse.isOpen_ballDom q).measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : ballDom q → Fin n → ℂ) := MeasurableEmbedding.subtype_coe hD
  letI act : MulAction U (ballDom q) :=
    { smul := fun γ t => ⟨moebBall q (ρ γ) t, moeb_maps q (hU γ γ.2) t.2⟩
      one_smul := fun t => Subtype.ext (by
        show moebBall q (ρ 1) t = t
        rw [funext h1, moeb_one])
      mul_smul := fun a b t => Subtype.ext
        (moeb_mul q (hU a a.2) (hU b b.2) (fun τ => (hm a b τ).symm) t.2).symm }
  have sm : ∀ (γ : U) (t : ballDom q), ((γ • t : ballDom q) : Fin n → ℂ) = moebBall q (ρ γ) t := fun _ _ => rfl
  haveI : MeasurableConstSMul U (ballDom q) := ⟨fun γ =>
    (Continuous.subtype_mk (continuousOn_iff_continuous_restrict.1
      (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props Ψ j j' n q (ρ γ) (hU γ γ.2)).1.continuousOn) _).measurable⟩
  let μ : Measure (ballDom q) := (ballMeas q).comap Subtype.val
  have hμ : ∀ s, μ s = ballMeas q (Subtype.val '' s) := fun s => hemb.comap_apply _ s
  haveI : SMulInvariantMeasure U (ballDom q) μ := ⟨fun γ s hs => by
    rw [hμ, hμ, ← (moeb_meas q (hU _ (γ⁻¹).2) (hemb.measurableSet_image.2 hs) (Subtype.coe_image_subset _ _)).2]
    congr 1
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨γ • x, hx, rfl⟩, by rw [← sm, inv_smul_smul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨γ⁻¹ • x, by simpa using hx, rfl⟩⟩
  have fd : ∀ (Γ : Subgroup G) (S : Set (Fin n → ℂ)), Γ ≤ U → MFund q ρ Γ S →
      IsFundamentalDomain (Γ.subgroupOf U) (Subtype.val ⁻¹' S : Set (ballDom q)) μ ∧
        μ (Subtype.val ⁻¹' S) = ballMeas q S := fun Γ S hΓ ⟨a1, a2, a3, a4⟩ => by
    refine ⟨IsFundamentalDomain.mk' (hemb.measurable a1).nullMeasurableSet fun x => ?_, ?_⟩
    · obtain ⟨γ, hγ, h⟩ := a3 x x.2
      refine ⟨⟨⟨γ, hΓ hγ⟩, hγ⟩, h, fun g hg => ?_⟩
      have e : (g.1 * (⟨γ, hΓ hγ⟩ : U)⁻¹) • ((⟨γ, hΓ hγ⟩ : U) • x) = g.1 • x := by
        rw [← mul_smul, inv_mul_cancel_right]
      have := a4 _ h (g.1.1 * γ⁻¹) (Γ.mul_mem g.2 (Γ.inv_mem hγ)) (by
        have e' := congrArg Subtype.val e
        rw [sm, sm, sm] at e'
        exact e' ▸ hg)
      exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
    · rw [hμ, Subtype.image_preimage_coe, Set.inter_eq_right.2 a2]
  obtain ⟨a₁, b₁⟩ := fd Γ S hΓ hS
  obtain ⟨a₂, b₂⟩ := fd Γ' S' hΓ' hS'
  rw [← b₁, ← b₂]
  exact fdEqual _ _ μ _ _ _ _
    (by rw [Subgroup.relIndex_subgroupOf hΓ, Subgroup.relIndex_subgroupOf hΓ']; exact hI.1)
    (by rw [Subgroup.relIndex_subgroupOf hΓ']; exact hI.2) a₁ a₂

end Moeb

open Moeb

theorem moebVol : MoebVol := by
  intro Ψ _ j j' n q q' G _ _ ρ ρ' w U Γ Γ' a S S' h1 hm hU hU' hw hc hΓ hΓ' hI hS ⟨b1, b2, b3, b4⟩
  have r1 : MeasurableSet (ren q q' '' S') := (ren q q').measurableSet_image.2 b1
  have r2 : ren q q' '' S' ⊆ ballDom q := by
    rintro _ ⟨t, ht, rfl⟩
    exact (ren_mem q q' t).2 (b2 ht)
  obtain ⟨m1, m2⟩ := moeb_meas q hw r1 r2
  have key : ∀ γ ∈ Γ', ∀ t ∈ ballDom q', moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) =
      moebBall q w (ren q q' (moebBall q' (ρ' γ) t)) := fun γ hγ t ht => by
    have ht' := (ren_mem q q' t).2 ht
    rw [← moeb_ren, moeb_mul q (hU (a * γ * a⁻¹) (hΓ' ⟨γ, hγ, rfl⟩)) hw (fun _ => rfl) ht',
      moeb_mul q hw (hU' γ hγ) (hc γ) ht']
  rw [← ren_meas q q' b1 b2, ← m2]
  refine core q ρ U Γ _ S _ h1 hm hU hΓ hΓ' hI hS ⟨m1, ?_, fun t ht => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact moeb_maps q hw (r2 ht)
  · have hi := fun τ => sinv_su (hw τ)
    obtain ⟨s, hs⟩ := (ren q q').surjective (moebBall q (fun τ => sinv (w τ)) t)
    have hs' : s ∈ ballDom q' := (ren_mem q q' s).1 (hs ▸ moeb_maps q hi ht)
    obtain ⟨γ, hγ, h⟩ := b3 s hs'
    refine ⟨a * γ * a⁻¹, ⟨γ, hγ, rfl⟩, _, ⟨_, h, rfl⟩, ?_⟩
    rw [← key γ hγ s hs', hs, moeb_inv q hw hi (fun τ => mul_sinv (hw τ)) ht]
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ _ ⟨γ, hγ, rfl⟩ ⟨_, ⟨s, hs, rfl⟩, e⟩
    replace e : moebBall q w (ren q q' s) = moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) := e
    rw [key γ hγ t (b2 ht)] at e
    have e2 := (ren q q').injective (moeb_injOn q hw ((ren_mem q q' _).2 (b2 hs))
      ((ren_mem q q' _).2 (moeb_maps q' (hU' γ hγ) (b2 ht))) e)
    obtain rfl := b4 t ht γ hγ (e2 ▸ hs)
    exact map_one _

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolRed
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
  GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)

def permQ (π : Ψ ≃ Ψ) : Ψ × Fin j × Fin j' ≃ Fin n := (π.prodCongr (Equiv.refl _)).trans q

theorem ballDom_permQ (π : Ψ ≃ Ψ) : ballDom (permQ q π) = ballDom q :=
  Set.ext fun t => ⟨fun h τ => by
    obtain ⟨τ, rfl⟩ := π.surjective τ
    exact h τ, fun h τ => h (π τ)⟩

theorem ballPot_permQ (π : Ψ ≃ Ψ) (t : Fin n → ℂ) : ballPot (permQ q π) t = ballPot q t :=
  congrArg Neg.neg (π.sum_comp fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)

theorem ballMeas_permQ (π : Ψ ≃ Ψ) : ballMeas (permQ q π) = ballMeas q := by
  simp only [ballMeas, ballDens, ballDom_permQ, ballPot_permQ]

theorem star_measurePreserving : MeasurePreserving (star : (Fin n → ℂ) → Fin n → ℂ) volume volume :=
  volume_preserving_pi (f := fun _ => Complex.conjLIE) fun _ => Complex.conjLIE.measurePreserving

theorem ballMeas_star {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ballMeas q (star ⁻¹' S) = ballMeas q S := by
  have hemb : MeasurableEmbedding (star : (Fin n → ℂ) → Fin n → ℂ) :=
    (Homeomorph.mk ⟨star, star, star_star, star_star⟩ continuous_star continuous_star).measurableEmbedding
  rw [ballMeas_apply q hS hD, ballMeas_apply q (hemb.measurable hS)
    (fun t ht => by simpa using star_mem_ballDom (hD ht)),
    ← star_measurePreserving.setLIntegral_comp_preimage_emb hemb _ S]
  simp only [ballDens, ballPot_star]

theorem integral_ballDens {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ∫ t in S, ballDens q t = (ballMeas q S).toReal := by
  rw [ballMeas_apply q hS hD]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
    (DictMeas.measurable_ballDens q).aestronglyMeasurable

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

def permFam (F : UnivFam E Ψ j j' n g Λ) (π : Ψ ≃ Ψ) : UnivFam E Ψ j j' n g Λ where
  q := permQ F.q π
  σ τ := F.σ (π τ)
  cm := ⟨F.cm.1.comp π.injective, fun s => by
    rw [π.exists_congr_right (q := fun τ => F.σ τ = s),
      π.exists_congr_right (q := fun τ => F.σ τ = (starRingEnd ℂ).comp s)]
    exact F.cm.2 s⟩
  form := F.form
  R := F.R
  form_eq := F.form_eq
  hol := by rw [ballDom_permQ]; exact F.hol
  sig t ht τ := F.sig t (ballDom_permQ F.q π ▸ ht) (π τ)
  b τ := F.b (π τ)
  frames := by
    rw [ballDom_permQ]
    exact ⟨fun τ => F.frames.1 (π τ), fun t ht τ => F.frames.2 t ht (π τ)⟩
  logDet_eq t ht := by
    rw [ballPot_permQ, ← F.logDet_eq t (ballDom_permQ F.q π ▸ ht)]
    exact π.sum_comp fun τ => Real.log ((F.R t).gram fun i => F.b τ i t).det.re
  univ R' hf hs := by
    rw [ballDom_permQ]
    exact F.univ R' hf fun τ => by
      obtain ⟨τ, rfl⟩ := π.surjective τ
      exact hs τ

theorem permFam_fund {F : UnivFam E Ψ j j' n g Λ} (π : Ψ ≃ Ψ) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (permFam F π).IsFundSet Γ FF := by
  have e : ballDom (permFam F π).q = ballDom F.q := ballDom_permQ F.q π
  unfold UnivFam.IsFundSet
  rw [e]
  exact h

theorem conjFam_fund {F : UnivFam E Ψ j j' n g Λ} {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (conjFam F).IsFundSet Γ (star ⁻¹' FF) := by
  refine ⟨continuous_star.measurable h.1, fun t ht => ?_, fun t ht => ?_, fun t ht t' ht' ⟨γ, hγ, he⟩ => ?_⟩
  · show t ∈ ballDom F.q
    simpa using star_mem_ballDom (h.2.1 ht)
  · obtain ⟨t', ht', γ, hγ, he⟩ := h.2.2.1 (star t) (star_mem_ballDom (q := F.q) ht)
    refine ⟨star t', by simpa using ht', γ, hγ, eqvBy_conj (fun x => rfl) (fun x => ?_) he⟩
    show star ((F.R (star (star t'))).P x) = _
    rw [star_star]
  · refine star_injective (h.2.2.2 _ ht _ ht' ⟨γ, hγ, eqvBy_conj (fun x => ?_) (fun x => ?_) he⟩)
    · exact (star_star _).symm
    · exact (star_star _).symm

theorem normalise (F : UnivFam E Ψ j j' n g Λ) (r : 𝓞 E) (d : ℕ) (hr : r ^ 2 = -(d : 𝓞 E))
    (hc : ∀ τ τ', F.σ τ r = F.σ τ' r) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)} (h : F.IsFundSet Γ FF) :
    ∃ (F₁ : UnivFam E Ψ j j' n g Λ) (FF₁ : Set (Fin n → ℂ)), (∀ τ, F₁.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ∧
      (F₁.form = F.form ∨ F₁.form = -F.form) ∧ F₁.IsFundSet Γ FF₁ ∧ ballMeas F₁.q FF₁ = ballMeas F.q FF := by
  by_cases h0 : ∀ τ, F.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)
  · exact ⟨F, FF, h0, Or.inl rfl, h, rfl⟩
  · obtain ⟨τ₀, h1⟩ := not_forall.1 h0
    have h2 : F.σ τ₀ r ^ 2 = (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 := by
      rw [← map_pow, hr, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      simp
    have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h1
    refine ⟨conjFam F, star ⁻¹' FF, fun τ => ?_, Or.inr rfl, conjFam_fund h, ballMeas_star F.q h.1 h.2.1⟩
    show starRingEnd ℂ (F.σ τ r) = _
    rw [hc τ τ₀, h3]
    simp

omit [NumberField E] [IsCMField E] in
theorem exists_perm {σ σ' : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) (h' : IsCMFam σ') (r : 𝓞 E) {c : ℝ} (hc : 0 < c)
    (hs : ∀ τ, σ τ r = Complex.I * (c : ℂ)) (hs' : ∀ τ, σ' τ r = Complex.I * (c : ℂ)) :
    ∃ π : Ψ ≃ Ψ, ∀ τ, σ' (π τ) = σ τ := by
  have : ∀ τ, ∃ τ', σ' τ' = σ τ := fun τ => (h'.2 _).2 fun ⟨τ', e⟩ => by
    have e1 := hs' τ'
    rw [e, RingHom.comp_apply, hs] at e1
    have := congrArg Complex.im e1
    simp at this
    linarith
  choose f hf using this
  have hi : Function.Injective f := fun a b e => h.1 (by rw [← hf, ← hf, e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hi), hf⟩

theorem label_rt {H : Host E} {l : Level H} (c : Coeff l) (τ τ' : CMType H) :
    labelEmb c (.inr τ) H.rt = labelEmb c (.inr τ') H.rt := by
  refine Subtype.ext ?_
  show τ.1 ((H.bar H.rt : 𝓞 E) : E) = τ'.1 ((H.bar H.rt : 𝓞 E) : E)
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj, τ.2, τ'.2]

theorem ballVolEq_of (h : FamVol) : BallVolEq := by
  intro _ E _ _ _ _ H D l Xo c Y n B FF hq hp hF k k'
  have hn := fun k => normalise (B.F k) H.rt H.d H.rt_sq
    (fun τ τ' => by rw [B.σ_eq, B.σ_eq, RingHom.comp_apply, RingHom.comp_apply, label_rt c τ τ']) (hF k)
  obtain ⟨F₁, FF₁, s₁, f₁, u₁, m₁⟩ := hn k
  obtain ⟨F₂, FF₂, s₂, f₂, u₂, m₂⟩ := hn k'
  have hd : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
  obtain ⟨π, hπ⟩ := exists_perm F₁.cm F₂.cm H.rt hd s₁ s₂
  have hf : ∀ k (f : _ →ₗ[ℤ] _ →ₗ[ℤ] ℤ), (f = (B.F k).form ∨ f = -(B.F k).form) → f = (B.Di k).EF ∨ f = -(B.Di k).EF := by
    intro k f hf
    rcases hf with rfl | rfl <;> rcases B.form_eq k with e | e <;> rw [e] <;> simp
  have key := h E H l (B.Di k) (B.Di k') (CMType H) D.p D.q n B.g F₁ (permFam F₂ π) (B.Γ k) (B.Γ k') FF₁ FF₂ _
    (by omega) (by omega) (by omega) hd (funext hπ) s₁ (hf k _ f₁) (hf k' _ f₂) (B.mem_Γ k) (B.mem_Γ k') u₁
    (permFam_fund π u₂)
  rw [integral_ballDens _ (hF k).1 (hF k).2.1, integral_ballDens _ (hF k').1 (hF k').2.1, ← m₁, ← m₂, key]
  exact congrArg (fun μ : Measure (Fin n → ℂ) => (μ FF₂).toReal) (ballMeas_permQ F₂.q π)

end SheetDecomposition
end
end

