module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestFamiliesProjectedTranslationOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField F] [NumberField E] in
theorem prod_tens_ext {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] {x y : (A × B) ⊗[F] E}
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz x, hz y, h1, h2]

theorem ae_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x y : AE F E}
    (hf : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y)
    (hi : ∀ (w : InfinitePlace F) (τ : EmbOver E w), piInf τ x = piInf τ y) : x = y := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y := by
    refine GlobalTheory.AutFunCompare.infTens_ext fun w => ?_
    obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have e : ∀ z : AE F E, infEmb τ (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)) = piInf τ z := fun z => by
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]; rfl
    rw [e, e]; exact hi w τ
  exact prod_tens_ext (A := Ainf F) (B := Af F) h1 hf

end GlobalTheory.TorusMat

namespace GlobalTheory.TorusMat

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) :
    piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
  simp

theorem piInf_infScale {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (s : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = s := by
  have := h.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  change infEmb τ (evInf F w (GlobalTheory.TorusTheta.infScale F s) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  have e := congrArg (fun p : mixedEmbedding.mixedSpace F => p.1 ⟨w, hr⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s))
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr]
  exact congrArg (fun x : ℝ => (x : ℂ)) (e.trans rfl)

theorem snd_infScale (s : ℝ) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

end Helpers

theorem isTorusElt_mat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  intro F E _ _ _ _ _ σ h n J r₀ Xf Yf t _ a ha
  let M : Matrix (Fin n) (Fin n) (AE F E) := ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
  let ψ : AE F E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have f1 : M.map ψ = 1 :=
    congrArg (fun u : GL (Fin n) (Af F ⊗[F] E) => (u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) (MonoidHom.mem_ker.1 ha.1)
  have f2 : ∀ s : Fin r₀ → ℝ, (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map ψ = 1 :=
    fun s => by
      rw [Matrix.diagonal_map (map_zero _)]
      simp only [ψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, snd_infScale, Matrix.diagonal_one]
  have g1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w), M.map (piInf τ) = GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) :=
    fun w τ => rfl
  have g2 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin r₀) E), (incM F Z).map (piInf τ) = Z.map τ.1 :=
    fun w τ Z => Matrix.ext fun i j => piInf_inclR τ (Z i j)
  have g3 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r₀ → ℝ),
      (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map (piInf τ) =
        Matrix.diagonal fun i => (s i : ℂ) := fun w τ s => by
    rw [Matrix.diagonal_map (map_zero _)]
    exact congrArg Matrix.diagonal (funext fun i => piInf_infScale h τ (s i))
  have key : ∀ {P Q : Matrix (Fin n) (Fin r₀) (AE F E)}, P.map ψ = Q.map ψ →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w), P.map (piInf τ) = Q.map (piInf τ)) → P = Q :=
    fun hf hi => Matrix.ext fun i j => ae_ext h (congrFun (congrFun hf i) j) fun w τ => congrFun (congrFun (hi w τ) i) j
  refine ⟨key ?_ fun w τ => ?_, key ?_ fun w τ => ?_, fun z hz hz' => funext fun i => ae_ext h ?_ fun w τ => ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 t, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).1]
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 (fun i => (t i)⁻¹), Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).2.1]
    congr 2
    funext i
    push_cast
    rfl
  · change ψ ((M *ᵥ _) i) = ψ _
    rw [RingHom.map_mulVec, f1, Matrix.one_mulVec]
    rfl
  · change piInf τ ((M *ᵥ _) i) = piInf τ _
    rw [RingHom.map_mulVec, g1]
    have e : (piInf τ ∘ fun i => inclR (F := F) (AF F) (z i)) = fun i => τ.1 (z i) := funext fun i => piInf_inclR τ (z i)
    rw [e, (ha.2 w τ).2.2 z hz hz', piInf_inclR]

end GlobalTheory.TorusMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositiveRealPlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealPlaceNorms

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField NumberField.InfinitePlace.Completion

theorem aeval_mulVec_of_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (z : ℂ)
    (h : A *ᵥ v = z • v) (p : ℂ[X]) : (aeval A p) *ᵥ v = p.eval z • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    have hk : (A ^ k) *ᵥ v = z ^ k • v := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      hk, smul_smul, eval_monomial]

theorem pos_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {v : Fin n → ℂ}
    (hv : v ≠ 0) {c : ℂ} (h : M *ᵥ v = c • v) : 0 < c := by
  have h1 := hM.dotProduct_mulVec_pos hv
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  have h2 : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hv
  rw [Complex.lt_def] at h1 h2 ⊢
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im] at a1 a2 b1 b2 ⊢
  rw [← b2] at a1 a2
  have hi : c.im = 0 := by
    have : c.im * (star v ⬝ᵥ v).re = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right b1.ne'
  refine ⟨?_, hi.symm⟩
  rw [hi] at a1
  have : 0 < c.re * (star v ⬝ᵥ v).re := by linarith
  exact (pos_iff_pos_of_mul_pos this).2 b1

theorem map_aeval {E : Type} [Field E] {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X]) (τ : E →+* ℂ) :
    (aeval γ m).map τ = aeval (γ.map τ) (m.map τ) := by
  rw [← RingHom.mapMatrix_apply, aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

section Fld

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)

theorem pos_at_embedding {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X])
    (hpos : ∀ τ : E →+* ℂ, ((aeval γ m).map τ).PosDef) (hdvd : Q.1 ∣ γ.charpoly)
    (x : plus Q) (hx : (x : Fld Q) = AdjoinRoot.mk Q.1 m) (φ : plus Q →+* ℂ) : 0 < φ x := by
  letI : Algebra (plus Q) ℂ := φ.toAlgebra
  haveI : Module.Finite (plus Q) (Fld Q) :=
    Module.Finite.of_restrictScalars_finite (maximalRealSubfield E) (plus Q) (Fld Q)
  haveI : Module.IsTorsionFree (plus Q) ℂ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (plus Q) (Fld Q) := DivisionSemiring.to_moduleIsTorsionFree
  let ρ : Fld Q →ₐ[plus Q] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hρx : ρ (x : Fld Q) = φ x := ρ.commutes x
  let τ : E →+* ℂ := (ρ : Fld Q →+* ℂ).comp (algebraMap E (Fld Q))
  have hev : ∀ p : E[X], (p.map τ).eval (ρ (AdjoinRoot.root Q.1)) = ρ (AdjoinRoot.mk Q.1 p) := by
    intro p
    rw [eval_map, ← AdjoinRoot.aeval_eq, aeval_def]
    exact (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) (ρ : Fld Q →+* ℂ) (AdjoinRoot.root Q.1)).symm
  set z := ρ (AdjoinRoot.root Q.1)
  have hroot : ((γ.map τ).charpoly).eval z = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    have h0 : (AdjoinRoot.mk Q.1 Q.1 : Fld Q) = 0 := AdjoinRoot.mk_self
    rw [Matrix.charpoly_map, hg, Polynomial.map_mul, eval_mul, hev, h0]
    exact mul_eq_zero_of_left (map_zero ρ) _
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hγv : (γ.map τ) *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hv0
    exact hv0.symm
  have hM : ((aeval γ m).map τ) *ᵥ v = φ x • v := by
    rw [map_aeval, aeval_mulVec_of_eigen _ v z hγv, hev, ← hx, hρx]
  exact pos_of_posDef (hpos τ) hv hM

end Fld

theorem exists_mul_self_of_pos {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (t : K)
    (ht : 0 < w.embedding t) : ∃ a : w.Completion, a * a = algebraMap K w.Completion t := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.1 ht
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  have hre : w.embedding t = ((w.embedding t).re : ℂ) := Complex.ext (by simp) (by simp [← h2])
  have key : ∃ a : w.Completion, extensionEmbedding w a = (Real.sqrt (w.embedding t).re : ℂ) := by
    by_cases hw : w.IsReal
    · refine ⟨(ringEquivRealOfIsReal hw).symm (Real.sqrt (w.embedding t).re), ?_⟩
      rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply,
        RingEquiv.apply_symm_apply]
    · exact surjective_extensionEmbedding_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  obtain ⟨a, ha⟩ := key
  refine ⟨a, (extensionEmbedding w).injective ?_⟩
  rw [map_mul, ha, ← Complex.ofReal_mul, Real.mul_self_sqrt h1.le, ← hre]
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
  change w.embedding t = extensionEmbedding w ((WithAbs.toAbs w.1 t : WithAbs w.1) : w.Completion)
  rw [extensionEmbedding_coe]
  simp

theorem exists_norm_at_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X],
    (∀ τ : E →+* ℂ, ((aeval γ.val m).map τ).PosDef) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r),
    Q.1 ∣ γ.val.charpoly →
    GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) =
      (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) →
    ∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q,
        z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ _ _ m hpos r Q hdvd hfix v
  let x : plus Q := ⟨AdjoinRoot.mk Q.1 m, hfix⟩
  obtain ⟨ψ, h1, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp (maximalRealSubfield E) (plus Q)
  have hroot : ∀ w : {w : InfinitePlace (plus Q) // w.comap (algebraMap (maximalRealSubfield E) (plus Q)) = v},
      ∃ a : w.1.Completion, a * a = algebraMap (plus Q) _ x := fun w =>
    exists_mul_self_of_pos w.1 x (pos_at_embedding Q γ.val m hpos hdvd x rfl w.1.embedding)
  choose a ha using hroot
  obtain ⟨b, hb'⟩ := (hb v).2 a
  have hb2 : b * b = 1 ⊗ₜ x := (hb v).1 (funext fun w => by
    have hw : ψ v w b = a w := congrFun hb' w
    simp only
    rw [map_mul, hw, ha, h1])
  refine ⟨inclPlus Q _ b, ?_⟩
  rw [GlobalTheory.TraceClasses.involBase_inclPlus, ← map_mul, hb2]
  rfl

end GlobalTheory.RealPlaceNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTrace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

noncomputable section

namespace GlobalTheory.TrMultSep

theorem separation_of_iwahoriTrace (hI : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace) (hE : GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate) :
    Separation := by
  intro D V T U hU μf hμ hK ν hν n Ws _ _ σs hσ a hyp
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨e, he, hP, hfam⟩ := _root_.GlobalTheory.TestFamTr.test_families D V T U hU μf hμ hK ν hν
  have hex : ∀ i, ∃ P : Ws i →ₗ[ℂ] Ws i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν (σs i) (finFn V e) P ∧
      FiniteDimensional ℂ (LinearMap.range P) := by
    intro i
    obtain ⟨c, A, hA, hAf⟩ := (_root_.GlobalTheory.FinTrace.hasTrace_finFn D V ν e he (Ws i) (σs i) (hσ.2.1 i)).1
    exact ⟨A, hA, hAf.1⟩
  choose P hPint using hex
  have hidem : ∀ i, P i ∘ₗ P i = P i := fun i => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).1
  have hne : ∀ i, HasTypeVec T (σs i) → P i ≠ 0 := fun i h => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).2 h
  intro i hi
  refine _root_.GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero (GfC V) n Ws σs hσ.1 hσ.2.2 P hidem (fun i => (hPint i).2) a ?_ i (hne i hi)
  intro g c hc
  obtain ⟨ff, hff, hffI, hffT, hffOp⟩ := hfam g
  have htr : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i) := fun i =>
    ⟨_, hffOp (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1, hc i⟩
  have hloc := fun i => _root_.GlobalTheory.LocCompFin.exists_locComp D V U.u (Ws i) (σs i) (hσ.1 i) (hσ.2.1 i)
  choose N instA instM π hπ using hloc
  letI : ∀ i, AddCommGroup (N i) := instA
  letI : ∀ i, Module ℂ (N i) := instM
  have hfac := fun i => _root_.GlobalTheory.PureTensorTrace.hasTrace_update_eq_const_mul D V U.u μf hμ hK ν hν (Ws i) (σs i) (hσ.2.1 i) (N i) (π i) (hπ i).1
    (hπ i).2.1 (hπ i).2.2 ff hff
  choose c' hc' using hfac
  have hd : ∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ,
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf U.u) (π i) (U.frame.cosetFn t) (b i)) →
      ∑ i, (a i * c' i) * b i = 0 := by
    intro t ht b hb
    have h := hyp (Function.update ff U.u (U.frame.cosetFn t)) (hffT t ht).1 (hffT t ht).2 (fun i => c' i * b i)
      (fun i => (hc' i _ (U.frame.cosetFn_mem t)).2 (b i) (hb i))
    simpa [mul_assoc] using h
  have hb := fun i => (hc' i (ff U.u) (hff.1 U.u)).1
  choose b hb using hb
  have key := _root_.GlobalTheory.IwahoriRel.relation_of_iwahoriTrace hI hE D V U (μf U.u) (hμ U.u) n N π (fun i => (hπ i).1) (fun i => (hπ i).2.1)
    (fun i => a i * c' i) hd (ff U.u) (hff.1 U.u) hffI b hb
  have hceq : ∀ i, c i = c' i * b i := by
    intro i
    have h := (hc' i (ff U.u) (hff.1 U.u)).2 (b i) (hb i)
    rw [Function.update_eq_self] at h
    exact (htr i).unique h
  simp_rw [hceq, ← mul_assoc]
  exact key

end GlobalTheory.TrMultSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem cA_eq_sigR (D : D7) (z : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = Formalism.L2.Theta.cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem triple_sum_comm_reverse {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem symp_eq_symplO : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y := by
  intro D S T JA JB ξ hA hB x y
  have hB' : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := D.host.F) (AF D.host.F) (D.host.xi0 * S.gram⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM D.host.F JA i k = incA D (T.gram k i) := by
    intro i k; subst hA; rfl
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.symplO Formalism.IndefR.Datum.hO
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [triple_sum_comm_reverse]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_sigR]
  calc ξ * (x i j * incA D (T.gram k i) * incM D.host.F JB j l * Formalism.L2.Theta.cA D (y k l))
      = x i j * incA D (T.gram k i) * (ξ * incM D.host.F JB j l) * Formalism.L2.Theta.cA D (y k l) := by ring
    _ = _ := by rw [hB']; ring

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetChar
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeTwist

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.TypeTame.invTranspose n g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [GlobalTheory.TypeTame.invTranspose, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem nabs_inv (x : kˣ) : GlobalTheory.SplitWeil.nabs k x⁻¹ = (GlobalTheory.SplitWeil.nabs k x)⁻¹ := by
  simp [GlobalTheory.SplitWeil.nabs]

theorem absPow_det_invTranspose (n : ℕ) (s : ℂ) (g : GL (Fin n) k) :
    detChar (Fin n) (absPow k s) (GlobalTheory.TypeTame.invTranspose n g) =
      detChar (Fin n) (absPow k (-s)) g := by
  ext
  have hp := GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g)
  simp only [detChar, absPow, MonoidHom.comp_apply, det_invTranspose]
  simp [nabs_inv, Complex.cpow_neg]

theorem twist_comp_invTranspose (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ) :
    (twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n) =
      twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))) := by
  ext g v
  simp only [MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, absPow_det_invTranspose]

end GlobalTheory.InvTransposeTwist

theorem GlobalTheory.InvTransposeTwist.main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  intro k _ _ _ _ n V _ _ π s
  rw [GlobalTheory.InvTransposeTwist.twist_comp_invTranspose]
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => rfl)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBall
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

namespace GlobalTheory.ChartDomain


open NumberField in
theorem _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := by
  intro E _ _ _ r X x z hx hz
  have hsmall : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    by_cases hr : (r : ℝ) = 0
    · simp [hr]
    · have hpos : 0 < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hpos.le
        _ = 1 / 100 := by field_simp
  exact (_root_.GlobalTheory.dmin_rmul_near_one X x hx (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) (norm_nonneg z) hsmall
    (fun τ a b => _root_.GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)).1

end GlobalTheory.ChartDomain
end

