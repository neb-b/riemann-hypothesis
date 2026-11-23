module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdapted
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := by
  simp [vOf]

theorem qi_gram {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  rw [← h3]
  calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
      = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem pinv_gram (v : InfinitePlace X.B.I.F) :
    ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
  have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have h1 : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  rw [← X.B.I.P_spec v]
  calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
      = (X.B.I.P v * (X.B.I.P v)⁻¹)ᴴ * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem besselModelTransportMatrix_gram_eq {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * A0 X C w = (Jc X).map (embS D (tauOf D w)) := by
  set τ := tauOf D w
  set B := C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ with hBdef
  have hB : Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B = X.B.I.J.map (X.B.I.φ (vOf X τ)) := by
    rw [← pinv_gram X (vOf X τ), ← qi_gram X C τ, hBdef, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hA : A0 X C w = B.submatrix id (ci X) := rfl
  have hAt : (A0 X C w)ᴴ = Bᴴ.submatrix (ci X) id := by rw [hA, conjTranspose_submatrix]
  have hprod : Bᴴ.submatrix (ci X) id * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B.submatrix id (ci X) =
      (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B).submatrix (ci X) (ci X) := by
    symm
    rw [submatrix_mul (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) B (ci X) id (ci X) Function.bijective_id,
      submatrix_mul Bᴴ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (ci X) id id Function.bijective_id, submatrix_id_id]
  rw [hAt, hA, hprod, hB]
  ext i j
  simp only [submatrix_apply, map_apply, Jc, X.φ_eq, X.J_eq, pl_vOf]

theorem embedding_of_not_direct (w : InfinitePlace D.host.E) (h : ¬ Direct D w) :
    w.embedding = ComplexEmbedding.conjugate (embS D (tauOf D w)) := by
  have hw : InfinitePlace.mk (embS D (tauOf D w)) = w := (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec
  rcases InfinitePlace.embedding_mk_eq (embS D (tauOf D w)) with h1 | h1
  · rw [hw] at h1; exact (h h1).elim
  · rwa [hw] at h1

theorem isModel {θ : ℝ} (C : Choice X θ) : GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) := by
  intro w
  unfold Ac
  split_ifs with h
  · rw [besselModelTransportMatrix_gram_eq, show w.embedding = embS D (tauOf D w) from h]
  · rw [embedding_of_not_direct w h]
    have hH : (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS).map (starRingEnd ℂ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      ext i j; simp only [map_apply, Formalism.QuantumDeterminants.Hpk]; split_ifs <;> simp
    have hc : ((A0 X C w).map (starRingEnd ℂ))ᴴ = ((A0 X C w)ᴴ).map (starRingEnd ℂ) := by
      ext i j; simp [conjTranspose_apply]
    show ((A0 X C w).map (starRingEnd ℂ))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (A0 X C w).map (starRingEnd ℂ) = _
    rw [hc, ← hH, ← Matrix.map_mul, ← Matrix.map_mul, besselModelTransportMatrix_gram_eq]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem v_pos : 0 < D.host.v := by
  have := GlobalTheory.RealPlaces.one_le_rdE D
  unfold Host.v; linarith

theorem frS_ne_zero : frS D ≠ 0 := by
  have hv := v_pos (D := D)
  unfold frS Host.ka
  have : Real.pi / D.host.v / (2 * Real.pi) ≠ 0 := by positivity
  exact_mod_cast this

theorem frS_pow_inv (m : ℕ) : ((frS D) ^ m)⁻¹ = (((2 * D.host.v) ^ m : ℝ) : ℂ) := by
  have hv := v_pos (D := D)
  have h : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
    unfold Host.ka; field_simp
  rw [frS, h]; push_cast; rw [inv_pow, inv_inv]

theorem star_frS : star (frS D) = frS D := by
  unfold frS; exact Complex.conj_ofReal _

theorem besselModelTransportMatrix_mulVec_coordinates {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) :
    (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) =
      C.Qi (tauOf D w) *ᵥ rv X.B.I (vOf X (tauOf D w)) (X.crd y) := by
  have hx : (fun i => embS D (tauOf D w) (crdH X y i)) =
      (fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X) := rfl
  have hx2 : ((fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X)) ∘ (ci X).symm =
      fun j => embS D (tauOf D w) (X.bas.repr y j) := by
    funext j; simp
  rw [hx, A0, submatrix_mulVec_equiv, hx2, Function.comp_id, ← mulVec_mulVec]
  congr 1
  unfold rv
  congr 1
  funext i
  rw [X.φ_eq, pl_vOf]
  simp [HidaSetting.crd, crdOf]

theorem qi_e {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.eR a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).1
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  rw [← frS_pow_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem qi_f {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.fR a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).2
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  have hs : star (frS D ^ (D.R.rS - (a : ℕ))) = frS D ^ (D.R.rS - (a : ℕ)) := by
    rw [star_pow, star_frS]
  rw [hs] at he
  rw [← frS_pow_inv, inv_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem Ac_mulVec {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) (c : ℝ)
    (j' : Fin (2 * D.R.rS + D.R.k + 1))
    (h : (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j') :
    (Ac X C w *ᵥ fun i => w.embedding (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j' := by
  unfold Ac
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd]; exact h
  · rw [embedding_of_not_direct w hd]
    have e1 : (fun i => (ComplexEmbedding.conjugate (embS D (tauOf D w))) (crdH X y i)) =
        ⇑(starRingEnd ℂ) ∘ (fun i => embS D (tauOf D w) (crdH X y i)) := by
      funext i; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e1]
    funext i
    rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← RingHom.map_mulVec, h]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Formalism.QuantumDeterminants.bvec]
    congr 1
    rcases eq_or_ne i j' with rfl | hij
    · simp
    · simp [hij]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

theorem model_adapted : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) ∧ GlobalTheory.SnMass.Adapted (Ac X C) (Pc X u) (fc X) (sc D) := by
  intro D X θ C u
  refine ⟨isModel X C, fun w a => ⟨?_, ?_⟩⟩
  · have hP : (fun i => w.embedding (Pc X u i a.castSucc)) = fun i => w.embedding (crdH X (X.eX a) i) := by
      funext i; simp [Pc]
    rw [hP]
    exact Ac_mulVec X C w _ _ _ (by rw [besselModelTransportMatrix_mulVec_coordinates]; exact qi_e X C _ a)
  · have hf : (fun i => w.embedding (fc X i a)) = fun i => w.embedding (crdH X (X.fY a) i) := rfl
    rw [hf]
    have := Ac_mulVec X C w (X.fY a) ((2 * D.host.v) ^ (D.R.rS - (a : ℕ)))⁻¹ (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a)
      (by rw [besselModelTransportMatrix_mulVec_coordinates]; have := qi_f X C (tauOf D w) a; push_cast at this ⊢; exact this)
    unfold sc; push_cast at this ⊢; exact this

end GlobalTheory.CovDom.ModelIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConcreteGramHermitianNondegenerateLatticeSelfDua
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  exact Fintype.sum_equiv (ci X).symm _ _ fun j => by simp

theorem vecOf_bijective : Function.Bijective (vecOf X) := by
  unfold vecOf
  rw [LinearMap.coe_comp]
  exact X.bas.equivFun.symm.bijective.comp (LinearEquiv.funCongrLeft _ _ _).bijective

private theorem sig_eq_star' (a : D.host.E) : D.sp.cm.sig a = star a := by rfl

theorem form_Jc (x y : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) x y = (VS D).hT (vecOf X y) (vecOf X x) := by
  rw [vecOf_apply, vecOf_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, Jc, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [AlgHom.coe_toRingHom, sig_eq_star', starRingEnd_apply]
  ring

end GlobalTheory.CovDom

theorem GlobalTheory.CovDom.herm_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  intro D X
  have hform := form_Jc X
  have hinj := (vecOf_bijective X).1
  have hsurj := (vecOf_bijective X).2
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND GlobalTheory.SgGlob.SelfDual
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, fun v => ?_⟩
  · simp only [Jc]
    rw [sig_eq_star']
    exact (VS D).herm.eq _ _
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv0
    apply hinj
    rw [map_zero]
    apply (VS D).nondeg.2
    intro w
    obtain ⟨y, rfl⟩ := hsurj w
    rw [← hform v y]
    simp [GlobalTheory.SgAlg.form, hv]
  · let e : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[𝓞 D.host.E] (VS D).V :=
      (LinearEquiv.ofBijective (vecOf X) (vecOf_bijective X)).restrictScalars (𝓞 D.host.E)
    have hc : Lc X = (VS D).L0.comap (e : _ →ₗ[𝓞 D.host.E] (VS D).V) := rfl
    rw [hc, Submodule.comap_equiv_eq_map_symm]
    exact (VS D).standardTuple_isLattice.fg.map _
  · show vecOf X v ∈ (VS D).L0 ↔ _
    conv_lhs => rw [← (VS D).baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    constructor
    · intro h w hw
      rw [hform v w]
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (h _ hw)
      exact ⟨a, ha⟩
    · intro h y hy
      obtain ⟨w, rfl⟩ := hsurj y
      have hw := h w hy
      rw [hform v w] at hw
      obtain ⟨a, ha⟩ := hw
      exact Submodule.mem_one.mpr ⟨a, ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidt
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstApprox

variable {n : ℕ}

theorem nrm_conj_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by

  have hs : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  unfold nrm
  congr 1
  unfold Formalism.REAL.hs Formalism.REAL.Jm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, hs, hs, one_mul, mul_one]

theorem nrm_sub_proj_le_sq (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (h : IsCut ε S E) (g : Formalism.REAL.UJ ε) (hg : g ∈ S) :
    nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by

  have hON : IsON E := h.isON
  obtain ⟨H, hH, -⟩ := h.subgroup
  obtain ⟨A, hAmul, -, hspan, hS⟩ := h
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hgU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g⁻¹ * uMat g = 1 := by
    show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : uMat g * uMat g⁻¹ = 1 := by
    show _ * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hinv : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * uMat g⁻¹ := by rw [hJJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by rw [hgU]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h2, Matrix.mul_one]
  have hgH : g ∈ H := by rw [← SetLike.mem_coe, hH]; exact hg
  have hgi : g⁻¹ ∈ S := by rw [← hH]; exact H.inv_mem hgH
  rw [hS] at hg hgi
  have hXA : uMat g - 1 ∈ A := hg
  have hXsA : uMat g⁻¹ - 1 ∈ A := hgi
  have hXs : Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε = uMat g⁻¹ - 1 := by
    rw [hinv]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hJJ]
  have key : (uMat g⁻¹ - 1) * (uMat g - 1) = -((uMat g - 1) + (uMat g⁻¹ - 1)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_one, Matrix.one_mul]
    abel
  have hG : Formalism.REAL.inG ε ((1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := by
    rw [← hXs]
    generalize uMat g - 1 = X
    have h0 : (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε +
        Formalism.REAL.Jm ε * (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) = 0 := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hJt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJJ', Matrix.mul_one]
      abel
    unfold Formalism.REAL.inG
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0,
      smul_zero]
  have hY : (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)) ∈ Submodule.span ℝ (Set.range E) :=
    (hspan _).1 ⟨A.smul_mem _ (A.sub_mem hXA hXsA), hG⟩
  have hsq : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
    rw [← hXs, nrm_conj_Jm, nrm_conjTranspose]
  calc nrm (uMat g - 1 - cmb E (crd E (uMat g - 1)))
      ≤ nrm (uMat g - 1 - (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := nrm_sub_proj_le hON _ hY
    _ = nrm ((-(1 / 2 : ℝ)) • ((uMat g⁻¹ - 1) * (uMat g - 1))) := by
        rw [key]
        congr 1
        module
    _ = 1 / 2 * nrm ((uMat g⁻¹ - 1) * (uMat g - 1)) := by
        rw [nrm_smul]
        norm_num
    _ ≤ 1 / 2 * (nrm (uMat g⁻¹ - 1) * nrm (uMat g - 1)) := by
        gcongr
        exact nrm_mul_le _ _
    _ ≤ nrm (uMat g - 1) ^ 2 := by
        rw [hsq]
        nlinarith [sq_nonneg (nrm (uMat g - 1)), nrm_nonneg (uMat g - 1)]

end GlobalTheory.IwConstApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqCHolds
section
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqC_holds : EqC := by
  intro D X Y u t₁ t₂ h1 h2 h
  obtain ⟨l, m, l', m', c⟩ := t₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := t₂
  simp only at h1 h2
  subst h1 h2
  have hc : c = c₂ := by
    rw [← Quot.out_eq c, ← Quot.out_eq c₂]
    exact Quot.sound h
  subst hc
  rfl
end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatum
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitRel

open Formalism.MainNotions.S.Loc ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem framePairFixator_unitary_and_fixes_frame (P : Formalism.MainNotions.S.LocNG.FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    Formalism.MainNotions.S.LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold Formalism.MainNotions.S.LocNG.FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x.symm u) (x.symm v) = H.h u v
      have := hx.1 (x.symm u) (x.symm v)
      simpa using this.symm
    · show x.symm (P.A.f b) = P.A.f b
      conv_lhs => rw [← (hx.2 b).1]
      simp
    · show x.symm (P.B.f b) = P.B.f b
      conv_lhs => rw [← (hx.2 b).2]
      simp

theorem perp_stable {g : V ≃ₗ[E] V} (hu : Formalism.MainNotions.S.LocNG.IsUnitary H g) {f : Fin (r + 1) → V}
    (hf : ∀ b, g (f b) = f b) {x : V} (hx : x ∈ H.perp (H.X f)) : g x ∈ H.perp (H.X f) := by
  intro v hv
  have hfix : Set.EqOn (g : V →ₗ[E] V) (LinearMap.id : V →ₗ[E] V) (Set.range fun a : Fin r => f a.castSucc) := by
    rintro _ ⟨a, rfl⟩
    simpa using hf a.castSucc
  have hv' : g v = v := LinearMap.eqOn_span' hfix hv
  have := hu x v
  rw [hv'] at this
  rw [this]
  exact hx v hv

theorem rel_equivalence (P : Formalism.MainNotions.S.LocNG.FPair H r) :
    Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := P)) := by
  refine ⟨fun d => ?_, fun {d d'} h => ?_, fun {d d' d''} h h' => ?_⟩
  · refine ⟨1, P.UW0.one_mem, ?_, ?_, ?_⟩
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x' y' x y hx' hx
      have e1 : y' = x' := Subtype.ext (by simpa using hx')
      have e2 : y = x := Subtype.ext (by simpa using hx)
      subst e1; subst e2; exact Iff.rfl
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    refine ⟨g⁻¹, P.UW0.inv_mem hg, ?_, ?_, ?_⟩
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h1 y x this).symm
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h2 y x this).symm
    · intro x' y' x y hx' hx
      have a1 : (x' : V) = g y' := by rw [hx']; show (x' : V) = g (g.symm x'); simp
      have a2 : (x : V) = g y := by rw [hx]; show (x : V) = g (g.symm x); simp
      exact (h3 y' x' y x a1 a2).symm
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    obtain ⟨g', hg', h1', h2', h3'⟩ := h'
    have hs := framePairFixator_unitary_and_fixes_frame P hg
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, ?_, ?_, ?_⟩
    · intro x y hxy
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h1 x z rfl).trans (h1' z y hxy)
    · intro x y hxy
      let z : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).2) x.2⟩
      exact (h2 x z rfl).trans (h2' z y hxy)
    · intro x' y' x y hx' hx
      let z' : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x', perp_stable hs.1 (fun b => (hs.2 b).2) x'.2⟩
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h3 x' z' x z rfl rfl).trans (h3' z' y' z y hx' hx)

theorem relEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    (p : PlF D), Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := FP p)) :=
  fun _ _ FP p => rel_equivalence (FP p)

end GlobalTheory.OrbitRel
end

