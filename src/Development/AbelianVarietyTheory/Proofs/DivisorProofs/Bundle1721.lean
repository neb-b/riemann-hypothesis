module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingEquivariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SiegelValGood

open scoped TensorProduct

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    Matrix.det_neg, Matrix.det_one] at h2
  intro h0
  rw [h0, mul_zero, zero_mul] at h2
  simp at h2
  exact absurd h2.symm (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mul_cA {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (h : UA σ J) :
    (mat h).det * cA σ (mat h).det = 1 := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h2 := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  have e1 : ((mat h).map (cA σ)).det = cA σ (mat h).det := (AlgHom.map_det (cA σ) _).symm
  have e2 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ J).symm
  rw [e1, e2] at h2
  have hu : IsUnit (inclR (F := F) (AF F) J.det) := (isUnit_iff_ne_zero.2 hJ).map _
  have h3 : (mat h).det * cA σ (mat h).det * inclR (F := F) (AF F) J.det = 1 * inclR (F := F) (AF F) J.det := by
    linear_combination h2
  exact hu.mul_left_injective h3

theorem piW_algebraMap {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  show splitProj τ (compFin F E v (a ⊗ₜ[F] (1 : E))) = _
  show splitProj τ (evFin F v a ⊗ₜ[F] (1 : E)) = _
  rw [splitProj_tmul, map_one, mul_one]

theorem at_mul {v : Pl (F := F)} {x : AE F E} (hx : At (evFin F v) x) (y : AE F E) : At (evFin F v) (x * y) := fun u hu => by
  rw [← smul_mul_assoc, hx u hu, zero_mul]

theorem at_add {v : Pl (F := F)} {x y : AE F E} (hx : At (evFin F v) x) (hy : At (evFin F v) y) : At (evFin F v) (x + y) :=
  fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

theorem at_det_sub_one {v : Pl (F := F)} {n : ℕ} {M : Matrix (Fin n) (Fin n) (AE F E)} (hM : At (evFin F v) (M - 1)) :
    At (evFin F v) (M.det - 1) := by
  intro u hu
  let I : Ideal (AE F E) := Ideal.span (Set.range fun p : Fin n × Fin n => (M - 1) p.1 p.2)
  have hdet : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
    have : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← map_one (Ideal.Quotient.mk I).mapMatrix,
        RingHom.mapMatrix_apply, Matrix.map_apply, Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨(i, j), rfl⟩
    rw [this, Matrix.det_one]
  have hle : I ≤ (Submodule.span (AE F E) {algebraMap (AF F) (AE F E) u}).annihilator := by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm, ← Algebra.smul_def]
    have := congrFun (congrFun (hM u hu) p.1) p.2
    simpa using this
  have := (Submodule.mem_annihilator_span_singleton _ _).1 (hle hdet)
  rw [Algebra.smul_def, mul_comm]
  rwa [smul_eq_mul] at this

theorem algebraMap_injective_AE : Function.Injective (algebraMap (AF F) (AE F E)) :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := AF F) (A := AF F) (B := E) (algebraMap F E).injective

theorem norm_det_eq_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (h : UA σ J) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (h : GL (Fin n) (AE F E))) = 1 := by
  apply Units.ext
  apply algebraMap_injective_AE (F := F) (E := E)
  show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) (mat h).det) = algebraMap (AF F) (AE F E) 1
  rw [GlobalTheory.Doubling.algebraMap_norm_eq hσ, map_one]
  exact det_mul_cA hJ h

theorem ratio_algebraMap_eq_one {X : Chars F E} {a a' : ℕ}
    (hα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α a')
    (hβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β a) (he : Even (a + a')) (u : (AF F)ˣ) :
    X.ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u) = 1 := by
  have h1 := hα u
  have h2 := hβ u
  show (X.α / X.β) _ = 1
  rw [MonoidHom.div_apply, div_eq_one]
  apply Circle.ext
  rw [h1, h2]
  split_ifs
  · rfl
  · have key : Even a ↔ Even a' := Nat.even_add.1 he
    by_cases ha : Even a
    · rw [ha.neg_one_pow, (key.1 ha).neg_one_pow]
    · rw [(Nat.not_even_iff_odd.1 ha).neg_one_pow, (Nat.not_even_iff_odd.1 (fun h => ha (key.2 h))).neg_one_pow]

theorem at_localIdele (v : Pl (F := F)) (x : (Fv F v)ˣ) :
    At (evFin F v) (algebraMap (AF F) (AE F E) (Neutral.B1.localIdele F v x : AF F) - 1) := by
  intro c hc
  have hs := Neutral.B1.localIdele_isSupportedAt F v x
  have key : c * ((Neutral.B1.localIdele F v x : AF F) - 1) = 0 := by
    apply Prod.ext
    · funext w
      show c.1 w * ((Neutral.B1.localIdele F v x : AF F).1 w - 1) = 0
      rw [hs.1 w, sub_self, mul_zero]
    · apply RestrictedProduct.ext
      intro P
      show c.2 P * ((Neutral.B1.localIdele F v x : AF F).2 P - 1) = 0
      by_cases hP : P = v
      · subst hP
        have : c.2 P = 0 := hc
        rw [this, zero_mul]
      · rw [hs.2 P hP, sub_self, mul_zero]
  rw [Algebra.smul_def, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, ← map_mul, key, map_zero]

end GlobalTheory.SiegelValGood

open GlobalTheory.SiegelValGood in
theorem GlobalTheory.SiegelValGood.siegel_factor_eq_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ g : GL (Fin a') (Fv F v),
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (chrW X.ν t (GlobalTheory.SplitFlip.gdet g) : ℂ) ^ 2 ∨
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (((chrW X.ν t (GlobalTheory.SplitFlip.gdet g))⁻¹ : ℂˣ) : ℂ) ^ 2 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t K hK g
  left
  have hσ : IsCMExt F E σ := hT.base.cm
  have hJ : G.V'.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (G.V'.J.map (B.emb w).1).det = (B.emb w).1 G.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  obtain ⟨hat, h1, h2⟩ := hK g
  set D := Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E)) with hD
  have hDv : (D : AE F E) = (mat (K g)).det := rfl
  have hN : Units.map (Algebra.norm (AF F) : AE F E →* AF F) D = 1 := norm_det_eq_one hσ hJ (K g)
  rw [hN, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one]
  have hpt : piW t (D : AE F E) = (GlobalTheory.SplitFlip.gdet g : Fv F v) := by
    rw [hDv, RingHom.map_det, RingHom.mapMatrix_apply, h1]; rfl
  have hJt : (G.V'.J.map t).det ≠ 0 := by
    have : (G.V'.J.map t).det = t G.V'.J.det := (AlgHom.map_det t _).symm
    rw [this]
    exact (map_ne_zero _).2 hJ
  have hgi : ((g⁻¹ : GL (Fin a') (Fv F v)) : Matrix (Fin a') (Fin a') (Fv F v)).det =
      (((GlobalTheory.SplitFlip.gdet g)⁻¹ : (Fv F v)ˣ) : Fv F v) := by
    rw [show (GlobalTheory.SplitFlip.gdet g)⁻¹ = Matrix.GeneralLinearGroup.det g⁻¹ from (map_inv _ _).symm]; rfl
  have hps : piW (t.comp σ) (D : AE F E) = (((GlobalTheory.SplitFlip.gdet g)⁻¹ : (Fv F v)ˣ) : Fv F v) := by
    rw [hDv, RingHom.map_det, RingHom.mapMatrix_apply, h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      Matrix.det_transpose, Ring.inverse_eq_inv, mul_right_comm, inv_mul_cancel₀ hJt, one_mul, hgi]
  set u := Neutral.B1.localIdele F v (GlobalTheory.SplitFlip.gdet g) with hu
  set zz : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u with hzz
  have hzt : ∀ τ : E →ₐ[F] Fv F v, piW τ (zz : AE F E) = (GlobalTheory.SplitFlip.gdet g : Fv F v) := fun τ => by
    show piW τ (algebraMap (AF F) (AE F E) (u : AF F)) = _
    rw [piW_algebraMap]
    exact Neutral.B1.localIdele_snd_self F v _
  have hzat : At (evFin F v) ((zz : AE F E) - 1) := at_localIdele v _
  have hνz : X.ν zz = 1 := ratio_algebraMap_eq_one hT.chars.resα hT.chars.resβ hT.geo.even u
  have hyat : At (evFin F v) (((D * zz : (AE F E)ˣ) : AE F E) - 1) := by
    have e : ((D * zz : (AE F E)ˣ) : AE F E) - 1 = ((D : AE F E) - 1) * zz + ((zz : AE F E) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    exact at_add (at_mul (at_det_sub_one hat) _) hzat
  have hy1 : piW (t.comp σ) ((D * zz : (AE F E)ˣ) : AE F E) = 1 := by
    rw [Units.val_mul, map_mul, hps, hzt, Units.inv_mul]
  have key := GlobalTheory.ChrLocal.chrW_piW_eq F E σ hσ X.ν v t (D * zz) hyat hy1
  have hsq : Units.map (piW t).toMonoidHom (D * zz) = GlobalTheory.SplitFlip.gdet g ^ 2 := by
    apply Units.ext
    show piW t ((D * zz : (AE F E)ˣ) : AE F E) = ((GlobalTheory.SplitFlip.gdet g ^ 2 : (Fv F v)ˣ) : Fv F v)
    rw [Units.val_mul, map_mul, hpt, hzt, Units.val_pow_eq_pow_val, sq]
  rw [hsq, map_pow, map_mul, hνz, mul_one] at key
  show ((X.ν D : Circle) : ℂ) = _
  rw [← Units.val_pow_eq_pow_val, key]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuousStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_normalizing_schrodinger_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl (F := F)) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  first | exact @GlobalTheory.ThK.ModelLocInt.exists_loc_schr | exact GlobalTheory.ThK.ModelLocInt.exists_loc_schr | (intros; apply GlobalTheory.ThK.ModelLocInt.exists_loc_schr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacterStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_unitary_standard_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @GlobalTheory.SplitScalar.splittings_differ_by_character | exact GlobalTheory.SplitScalar.splittings_differ_by_character | (intros; apply GlobalTheory.SplitScalar.splittings_differ_by_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaConvergenceOfSiegelSet
section
noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilThetaConv

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hwitt θ hθ ν hν Φ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram V)
  have hr : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := _root_.GlobalTheory.WittIdxBound.witt_frame_le_wittIdx D V r Xf Yf hW
  have hr' : r = 0 ∨ n + r < V.rank := by rcases hwitt with h | h <;> omega
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (GlobalTheory.Doubling.isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  have hΦc : Continuous Φ.1 := (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ V.rank n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ V.rank n Φ.1 Φ.2)).1
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.TorusBound.absTheta_le_torus D θ hθ V n r Xf Yf hW c hc (C₀ * (K : Set (GA D V))) (hC₀.mul hK) Φ
  have hI := _root_.GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt D.host.F V.rank r n c hc hr'
  calc GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1
      ≤ ∫⁻ g in GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K, GlobalTheory.SiegelFormula.absTheta V Φ.1 g ∂ν :=
        _root_.GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover D V n ν hν Φ.1 hΦc _ hcl.measurableSet hcov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
          ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (fun g => GlobalTheory.SiegelFormula.absTheta V Φ.1 g) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have e : p * a * k = a * (a⁻¹ * p * a * k) := by group
        rw [e]
        exact hC t ht a ha _ (Set.mul_mem_mul (hconj p hp t ht a ha) hk)
    _ = C₁ * (ENNReal.ofReal C * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
          ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hC0, mul_assoc]
    _ < ⊤ := by
        have := hI.ne
        finiteness

end GlobalTheory.WeilThetaConv

end
end

