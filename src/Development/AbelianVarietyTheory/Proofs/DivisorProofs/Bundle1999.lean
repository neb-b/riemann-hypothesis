module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSqMulPowLeProdBilinFormLatticeBasis
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.LatIndex

open Matrix

theorem cast_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (((z ⬝ᵥ M *ᵥ z : ℤ)) : ℝ) =
      (fun i => (z i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (z i : ℝ)) := by
  simp [dotProduct, mulVec, Int.cast_sum, Int.cast_mul]

theorem gram_quad {n : ℕ} {Y : Type} [AddCommGroup Y] (β : LinearMap.BilinForm ℤ Y)
    (v : Fin n → Y) (z : Fin n → ℤ) :
    z ⬝ᵥ (Matrix.of fun i j => β (v i) (v j)) *ᵥ z = β (∑ i, z i • v i) (∑ i, z i • v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, mulVec, map_sum, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem posSemidef_map_intCast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hs : Mᵀ = M)
    (h : ∀ z : Fin n → ℤ, 0 ≤ z ⬝ᵥ M *ᵥ z) : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    have := congrFun (congrFun hs i) j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
    rw [this]
  · simp only [star_trivial]
    have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ x ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ x} :=
      isClosed_le continuous_const (by fun_prop)
    refine (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
      fun q => ?_
    show 0 ≤ (fun i => ((q i : ℚ) : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => ((q i : ℚ) : ℝ))
    set d : ℕ := ∏ i, (q i).den with hd
    have hd0 : (0 : ℝ) < d := by
      rw [hd]; exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hc : ∀ i, ∃ c : ℕ, d = (q i).den * c := fun i =>
      Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
    choose c hc using hc
    let z : Fin n → ℤ := fun i => (q i).num * c i
    have hz : ∀ i, ((q i : ℚ) : ℝ) = (d : ℝ)⁻¹ * (z i : ℝ) := by
      intro i
      have h1 : ((z i : ℤ) : ℚ) = q i * d := by
        simp only [z, hc i, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
        rw [← Rat.mul_den_eq_num]; ring
      have h2 : ((z i : ℤ) : ℝ) = ((q i : ℚ) : ℝ) * d := by
        have := congrArg (fun t : ℚ => (t : ℝ)) h1
        simpa using this
      rw [h2]; field_simp
    have hfun : (fun i => ((q i : ℚ) : ℝ)) = (d : ℝ)⁻¹ • (fun i => (z i : ℝ)) := by
      ext i; simp [hz i]
    rw [hfun, smul_dotProduct, mulVec_smul, dotProduct_smul, ← cast_quad]
    have := h z
    have h3 : (0 : ℝ) ≤ ((z ⬝ᵥ M *ᵥ z : ℤ) : ℝ) := by exact_mod_cast this
    simp only [smul_eq_mul]
    positivity

theorem det_sq_mul_pow_le_prod :
    ∀ (r : ℕ) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (X : Type)
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (b : Module.Basis (Fin r) ℤ X₀)
      (ε : X ≃ₗ[ℤ] X₀) (k : X₀ →ₗ[ℤ] X) (β : LinearMap.BilinForm ℤ X),
      (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam →
      (∀ x, x ≠ 0 → lam ≤ β x x) →
      ((LinearMap.det (ε.toLinearMap ∘ₗ k) : ℤ) : ℝ) ^ 2 * lam ^ r ≤
        (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) := by
  intro r X₀ _ _ _ X _ _ _ b ε k β hsym hpos lam hlam hmin
  classical
  let e : Module.Basis (Fin r) ℤ X := b.map ε.symm
  have he : ∀ i, e i = ε.symm (b i) := fun i => by simp [e]
  let Gz : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => β (e i) (e j)
  let A : Matrix (Fin r) (Fin r) ℤ := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ k)
  let Mz : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => β (k (b i)) (k (b j))
  have hkb : ∀ j, k (b j) = ∑ i, A i j • e i := by
    intro j
    have h1 : ε (k (b j)) = ∑ i, A i j • b i := by
      simp only [A, LinearMap.toMatrix_apply]
      exact (b.sum_repr _).symm
    have h2 := congrArg ε.symm h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearEquiv.symm_apply_apply, map_sum, map_zsmul] at h2
    rw [h2]; simp [he]
  have hM : Mz = Aᵀ * Gz * A := by
    ext j l
    simp only [Mz, Gz, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hkb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]
  have hdetA : A.det = LinearMap.det (ε.toLinearMap ∘ₗ k) := LinearMap.det_toMatrix b _
  have hGs : Gzᵀ = Gz := by ext i j; simp [Gz, hsym]
  have hMs : Mzᵀ = Mz := by ext i j; simp [Mz, hsym]
  have hGq : ∀ z, 0 ≤ z ⬝ᵥ Gz *ᵥ z := fun z => by rw [gram_quad]; exact hpos _
  have hMq : ∀ z, 0 ≤ z ⬝ᵥ Mz *ᵥ z := fun z => by rw [gram_quad]; exact hpos _
  have hG := posSemidef_map_intCast Gz hGs hGq
  have hMp := posSemidef_map_intCast Mz hMs hMq
  have hmink : lam ^ r ≤ (r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det := by
    refine GlobalTheory.minkowski_det_bound_posSemidef r _ hG lam hlam fun z hz => ?_
    rw [← cast_quad, gram_quad]
    apply hmin
    intro h0
    apply hz
    have : e.equivFun.symm z = e.equivFun.symm 0 := by
      rw [map_zero, Module.Basis.equivFun_symm_apply]; exact h0
    exact e.equivFun.symm.injective this
  have hhad := _root_.GlobalTheory.posSemidef_real_det_le_prod_diag r _ hMp
  have hdetM : (Mz.map (Int.cast : ℤ → ℝ)).det =
      ((A.det : ℤ) : ℝ) ^ 2 * (Gz.map (Int.cast : ℤ → ℝ)).det := by
    have h1 : ∀ N : Matrix (Fin r) (Fin r) ℤ, (N.map (Int.cast : ℤ → ℝ)).det = ((N.det : ℤ) : ℝ) :=
      fun N => by
        rw [show (N.map (Int.cast : ℤ → ℝ)) = (Int.castRingHom ℝ).mapMatrix N from rfl,
          ← RingHom.map_det]; rfl
    rw [h1, h1, hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    push_cast; ring
  have hdiag : ∀ j, (Mz.map (Int.cast : ℤ → ℝ)) j j = (β (k (b j)) (k (b j)) : ℝ) := by
    intro j; simp [Mz]
  simp only [hdiag] at hhad
  rw [← hdetA]
  calc ((A.det : ℤ) : ℝ) ^ 2 * lam ^ r
      ≤ ((A.det : ℤ) : ℝ) ^ 2 * ((r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det) :=
        mul_le_mul_of_nonneg_left hmink (sq_nonneg _)
    _ = (r : ℝ) ^ r * (Mz.map (Int.cast : ℤ → ℝ)).det := by rw [hdetM]; ring
    _ ≤ (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) :=
        mul_le_mul_of_nonneg_left hhad (by positivity)

end GlobalTheory.LatIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivariance
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalDet

open GlobalTheory.DblScal
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem udat_mul {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R}
    {p q : UD σ J} (hp : p ∈ UDAt σ J ev) (hq : q ∈ UDAt σ J ev) : p * q ∈ UDAt σ J ev := by
  intro u hu
  have e : ((((p * q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) - 1 =
      ((((p : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) *
        (((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
      ((((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    simp [sub_mul]
  rw [e, smul_add, ← Matrix.smul_mul, hp u hu, hq u hu, Matrix.zero_mul, add_zero]

theorem udat_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R} :
    (1 : UD σ J) ∈ UDAt σ J ev := by
  intro u _
  simp

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (h : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := det_ne_zero_of_hasSig (h.sig (InfinitePlace.mk φ))
  intro e
  apply h0
  rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero]

theorem mulLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (dd : DblCo σ X W) (omd : DblRep σ (n := n) W),
    IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → LocOps omd v →
    ∀ ιd, IsLinD ψ dd t b c ιd → ∀ cd, IsShapeD omd t c ιd cd →
    cd 1 = 1 ∧ ∀ p ∈ UDAt σ W.J (evFin F v), ∀ q ∈ UDAt σ W.J (evFin F v), cd (p * q) = cd p * cd q := by
  intro F E _ _ _ _ _ σ ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨φ0, hφ0, hne⟩ : ∃ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ιd φ ≠ 0 := by
    have hmem : (intM (Fv F v) (Fin n) (Fin d ⊕ Fin d)).indicator (1 : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ) ∈
        SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) := indicator_intM_mem_SB
    obtain ⟨φ, hφ, he⟩ := hI.bij.surjOn hmem
    refine ⟨φ, hφ, fun h => ?_⟩
    have h0 := congrFun he 0
    rw [h, Set.indicator_of_mem (fun i j => by simp)] at h0
    simp at h0
  obtain ⟨Z, hZ⟩ : ∃ Z, ιd φ0 Z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have comp : ∀ p q : UD σ W.J, ∀ φ φ₁ φ₂ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ,
      Acts (evFin F v) (omd q) φ φ₁ → Acts (evFin F v) (omd p) φ₁ φ₂ → Acts (evFin F v) (omd (p * q)) φ φ₂ := by
    intro p q φ φ₁ φ₂ hq hp r hr
    have h1 := hq r hr
    have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, h1 ▸ hS.pres q _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1, hp r hr1]
  refine ⟨?_, ?_⟩
  · have hA : Acts (evFin F v) (omd 1) φ0 φ0 := fun r _ => by rw [map_one, Module.End.one_apply]
    have e := congrFun (hD 1 udat_one φ0 hφ0 φ0 hφ0 hA) Z
    simp only [map_one, Units.val_one, Matrix.mul_one, Pi.smul_apply, smul_eq_mul] at e
    exact (mul_eq_right₀ hZ).mp e.symm
  · intro p hp q hq
    obtain ⟨φ₁, hφ₁, h1⟩ := hL q hq φ0 hφ0
    obtain ⟨φ₂, hφ₂, h2⟩ := hL p hp φ₁ hφ₁
    have e1 := hD q hq φ0 hφ0 φ₁ hφ₁ h1
    have e2 := hD p hp φ₁ hφ₁ φ₂ hφ₂ h2
    have e3 := hD (p * q) (udat_mul hp hq) φ0 hφ0 φ₂ hφ₂ (comp p q φ0 φ₁ φ₂ h1 h2)
    have hG : GlobalTheory.SplitFlip.invT (locMatD t c (p * q)) =
        GlobalTheory.SplitFlip.invT (locMatD t c p) * GlobalTheory.SplitFlip.invT (locMatD t c q) := by
      rw [map_mul, map_mul]
    set G := GlobalTheory.SplitFlip.invT (locMatD t c (p * q))
    have hY := congrFun (e3.symm.trans e2) (Z * (G⁻¹).val)
    rw [e1] at hY
    simp only [Pi.smul_apply, smul_eq_mul] at hY
    have k1 : Z * (G⁻¹).val * G.val = Z := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have k2 : Z * (G⁻¹).val * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val * (GlobalTheory.SplitFlip.invT (locMatD t c q)).val = Z := by
      rw [Matrix.mul_assoc, ← Units.val_mul, ← hG, k1]
    rw [k1, k2, ← mul_assoc] at hY
    exact mul_right_cancel₀ hZ hY

end GlobalTheory.DblScalDet


open GlobalTheory.DblScalDet in
theorem GlobalTheory.DblScal.scalar_factors_through_det : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨h1, hmul⟩ := mulLaw F E σ B.ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  have hJ : W.J.det ≠ 0 := det_ne_zero_of_skew hP.skew
  have hinj := GlobalTheory.T.local_matrix_map_injective F E σ hP.base.cm d W.J hJ v t c
  have hsurj := GlobalTheory.T.local_matrix_map_surjective F E σ hP.base.cm d W.J hJ hP.skew.skew v t c
  have hex : ∀ A : GL (Fin d ⊕ Fin d) (Fv F v), ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = A :=
    fun A => hsurj (Set.mem_univ A)
  choose sec hsU hs using hex
  have hsm : ∀ A A', sec (A * A') = sec A * sec A' := fun A A' =>
    hinj (hsU _) (udat_mul (hsU A) (hsU A')) (by rw [hs, map_mul, hs, hs])
  have hs1 : sec 1 = 1 := hinj (hsU 1) udat_one (by rw [hs, map_one])
  let f : GL (Fin d ⊕ Fin d) (Fv F v) →* ℂˣ :=
    { toFun := fun A => ⟨cd (sec A), cd (sec A⁻¹),
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, mul_inv_cancel, hs1, h1],
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, inv_mul_cancel, hs1, h1]⟩
      map_one' := Units.ext (by simp only [hs1, h1, Units.val_one])
      map_mul' := fun A A' => Units.ext (by simp only [Units.val_mul]; rw [hsm, hmul _ (hsU _) _ (hsU _)]) }
  let e : Fin d ⊕ Fin d ≃ Fin (d + d) := finSumFinEquiv
  let rr : GL (Fin (d + d)) (Fv F v) →* GL (Fin d ⊕ Fin d) (Fv F v) :=
    Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e.symm).toMonoidHom
  have h2 : (2 : Fv F v) ≠ 0 := fun h => two_ne_zero (α := F) ((algebraMap F (Fv F v)).injective (by rw [map_ofNat, h, map_zero]))
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (k := Fv F v) h2 (f.comp rr)
  refine ⟨fun x => (χ x : ℂ), fun p hp => ?_⟩
  have hp' : sec (GlobalTheory.DblScal.locMatD t c p) = p := hinj (hsU _) hp (hs _)
  set A := GlobalTheory.DblScal.locMatD t c p
  let A' : GL (Fin (d + d)) (Fv F v) := Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e).toMonoidHom A
  have hA : rr A' = A := Units.ext (by ext i j; simp [rr, A'])
  have hdet : Matrix.GeneralLinearGroup.det A' = GlobalTheory.SplitFlip.gdet A :=
    Units.ext (by simp [A', GlobalTheory.SplitFlip.gdet, Matrix.det_reindex_self])
  have hf := hχ A'
  rw [MonoidHom.comp_apply, hA, hdet] at hf
  calc cd p = cd (sec A) := by rw [hp']
    _ = ((f A : ℂˣ) : ℂ) := rfl
    _ = _ := by rw [hf]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepFixesVacuumTensorSiegelParabolicIn
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDblPar

theorem parD_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.star_mem_schA_main _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen F E σ B a a' G X om om' hTr v w hin dd omd hdc hws R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := _root_.GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht
  have ha := GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace F E σ B a a' G X om om' hTr v w hin hT t htp
  have hb := GlobalTheory.T.local_theta_integral_at_inert_place F E σ B a a' G X om om' hTr v w hin hT t htp
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]

end GlobalTheory.InertDblPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldHomFlatSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem dualNumber_map_flat_surjective : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ ψ : DualNumber k →+* DualNumber K, ψ.comp (dnInl k) = (dnInl K).comp φ ∧ (dnFst K).comp ψ = φ.comp (dnFst k) ∧ Flat (spMap ψ) ∧ Surjective (spMap ψ) := by
  intro k K _ _ φ
  letI : Algebra k K := φ.toAlgebra
  let ψ₀ : DualNumber k →ₐ[k] DualNumber K :=
    DualNumber.lift ⟨(Algebra.ofId k (DualNumber K), DualNumber.eps),
      by simp, fun _ ↦ Commute.all _ _⟩
  have hψ₀ : ∀ x : DualNumber k, ψ₀ x = TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd) := by
    intro x
    rw [DualNumber.lift_apply_apply]
    ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let j : K →ₐ[k] DualNumber K := TrivSqZeroExt.inlAlgHom k K K
  let g : TensorProduct k (DualNumber k) K →ₐ[k] DualNumber K :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber K → TensorProduct k (DualNumber k) K := fun x ↦
    (1 : DualNumber k) ⊗ₜ[k] x.fst + (DualNumber.eps : DualNumber k) ⊗ₜ[k] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, g (h x) = x := by
    intro x
    simp only [h, g, map_add (f := _), Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀]
  have hhg : ∀ x, h (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber k) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[k] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add (f := _), hadd, hx, hy]
  have hbij : Function.Bijective g := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  refine ⟨ψ₀.toRingHom, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [hψ₀, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  · refine RingHom.ext fun x ↦ ?_
    simp [hψ₀]
  · have hc : ψ₀.toRingHom = g.toRingHom.comp (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)) := by
      refine RingHom.ext fun x ↦ ?_
      simp [g, j, Algebra.TensorProduct.algebraMap_apply]
    have hff : (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
    have h1 := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)))).2 hff
    have := h1.1
    have := h1.2
    let eR : TensorProduct k (DualNumber k) K ≃+* DualNumber K := (AlgEquiv.ofBijective g hbij).toRingEquiv
    have hi : IsIso (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map eR.toCommRingCatIso.hom))
    rw [hc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldPointMemOpenOfReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
namespace GlobalTheory.MBLow.TanGauge

theorem top_le_of_redE : ∀ (C : Type) [Field C] {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens),
    ⊤ ≤ (redE C ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U := by
  intro C _ X y U h q _
  have key : ∃ p : (Sp C : Scheme.{0}), (redE C) p = q := by
    have hsub : Subsingleton (PrimeSpectrum (DualNumber C)) := by
      refine ⟨fun a b => ?_⟩
      have aux : ∀ a : PrimeSpectrum (DualNumber C), ∀ x, x ∈ a.asIdeal ↔ x.fst = 0 := by
        intro a x
        constructor
        · intro hx
          by_contra hne
          exact a.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
        · intro hx
          refine a.2.mem_of_pow_mem 2 ?_
          have : x ^ 2 = 0 := by
            ext <;> simp [sq, hx]
          rw [this]; exact zero_mem _
      ext x; rw [aux, aux]
    exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C), hsub.elim _ _⟩
  obtain ⟨p, rfl⟩ := key
  exact h (x := p) trivial
end GlobalTheory.MBLow.TanGauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOneStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V V' : X.Opens, IsAffineOpen V → V ≤ V' → (∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) → V' = V := by
  first | exact @GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | exact GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | (intros; apply GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one <;> assumption)
end

