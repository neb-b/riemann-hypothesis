module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterExtendsToIdeleClass
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ArchSignChar

def nrm : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)))
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem nrm_val (z : ℂˣ) : ((nrm z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_nrm (z : ℂˣ) : ‖((nrm z : ℂˣ) : ℂ)‖ = 1 := by
  rw [nrm_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_nrm : Continuous nrm := by
  have h0 : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)
  have hc : Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) :=
    Units.continuous_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) h0
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  exact hc.inv₀ fun z => div_ne_zero z.ne_zero (h0 z)

def normChar {R : Type} [CommRing R] (θ : R →+* ℂ) : Rˣ →* Circle :=
  GlobalTheory.unitaryCharToCircle (nrm.comp (Units.map θ.toMonoidHom)) fun _ => norm_nrm _

theorem normChar_val {R : Type} [CommRing R] (θ : R →+* ℂ) (x : Rˣ) :
    ((normChar θ x : Circle) : ℂ) = θ x / ((‖θ x‖ : ℝ) : ℂ) := rfl

theorem continuous_normChar {R : Type} [CommRing R] [TopologicalSpace R] (θ : R →+* ℂ) (hθ : Continuous θ) :
    Continuous (normChar θ) :=
  Continuous.subtype_mk (Units.continuous_val.comp (continuous_nrm.comp (Continuous.units_map _ hθ))) _

theorem ofReal_div_norm (r : ℝ) (hr : r ≠ 0) :
    ((r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ)) = if r < 0 then -1 else 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
  · rw [abs_of_pos (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hr)), div_self (Complex.ofReal_ne_zero.2 hr)]

theorem sq_eq_one (z : Circle) (h : z * z = 1) : z = 1 ∨ z = -1 := by
  have h3 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h3 with h4 | h4
  · exact Or.inl (Circle.ext h4)
  · exact Or.inr (Circle.ext (by rw [h4]; simp))

theorem exists_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) : ∃ θ : AF F ⊗[F] E →+* ℂ, Continuous θ ∧
      ∀ a : AF F, θ (algebraMap (AF F) (AF F ⊗[F] E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let τ : E →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let g0 : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
  let g : AF F →ₐ[F] ℂ := ⟨g0, fun x => by
    change InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (AF F) x).1 w) = _
    rw [AdeleRing.algebraMap_fst_def, InfiniteAdeleRing.algebraMap_apply]
    exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩
  let θ : AF F ⊗[F] E →+* ℂ := (Algebra.TensorProduct.productMap g τ).toRingHom
  have hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x := fun a x => rfl
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine ⟨θ, ?_, fun a => ?_⟩
  · refine IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_
    have : Continuous g0 := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
    refine this.congr fun a => ?_
    change _ = θ (a ⊗ₜ[F] 1)
    rw [hθ, map_one, mul_one]
  · change θ (a ⊗ₜ[F] 1) = _
    rw [hθ, map_one, mul_one]; rfl

def archIdele (F : Type) [Field F] [NumberField F] : ((w : InfinitePlace F) → (w.Completion)ˣ) →* (AF F)ˣ :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp (MulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.toMonoidHom)

def archPart {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) : (w : InfinitePlace F) → (w.Completion)ˣ :=
  MulEquiv.piUnits (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F) b).1

theorem eq_archIdele {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) :
    b = archIdele F (archPart b) := by
  apply Units.ext
  refine Prod.ext rfl ?_
  exact hb

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

theorem local_sign {K : Type} [Field K] {w : InfinitePlace K} (hw : w.IsReal) (χ : (w.Completion)ˣ →* Circle)
    (hχ : ∀ s, χ (s * s) = 1) (t : (w.Completion)ˣ) :
    χ t = if InfinitePlace.Completion.ringEquivRealOfIsReal hw (t : w.Completion) < 0 then χ (-1) else 1 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  have ht : e (t : w.Completion) ≠ 0 := (map_ne_zero e).2 t.ne_zero
  split_ifs with h
  · have hpos : 0 < -e t := neg_pos.2 h
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = -1 * (s * s) := by
      have hs0 : e.symm (Real.sqrt (-e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, map_mul, map_neg, map_one,
        RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
      ring
    rw [hs, map_mul, hχ, mul_one]
  · have hpos : 0 < e t := lt_of_le_of_ne (not_lt.1 h) (Ne.symm ht)
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = s * s := by
      have hs0 : e.symm (Real.sqrt (e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_mk0, map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
    rw [hs, hχ]

theorem eta_eq_prod {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (η : (AF F)ˣ →* Circle)
    (hsq : ∀ b, η (b * b) = 1) (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) [DecidableEq (InfinitePlace F)] :
    η b = ∏ w, if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0
      then η (archIdele F (Pi.mulSingle w (-1))) else 1 := by
  calc η b = η (archIdele F (archPart b)) := congrArg η (eq_archIdele b hb)
    _ = η (archIdele F (∏ w, Pi.mulSingle w (archPart b w))) := by rw [Finset.univ_prod_mulSingle]
    _ = ∏ w, η (archIdele F (Pi.mulSingle w (archPart b w))) := by rw [map_prod, map_prod]
    _ = _ := Finset.prod_congr rfl fun w _ =>
      local_sign (IsTotallyReal.isReal w) ((η.comp (archIdele F)).comp (MonoidHom.mulSingle (fun u : InfinitePlace F => (u.Completion)ˣ) w))
        (fun s => by
          change η (archIdele F (Pi.mulSingle w (s * s))) = 1
          rw [Pi.mulSingle_mul, map_mul]
          exact hsq _) (archPart b w)

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

theorem exists_arch_sign_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := by
  intro F E _ _ _ _ _ σ hcm η _ hsq
  classical
  haveI : IsTotallyReal F := hcm.1
  choose θ hθc hθ using fun w : InfinitePlace F => exists_coord (F := F) (E := E) w
  let c : InfinitePlace F → Circle := fun w => η (archIdele F (Pi.mulSingle w (-1)))
  let g : InfinitePlace F → ((AF F ⊗[F] E)ˣ →* Circle) := fun w => if c w = 1 then 1 else normChar (θ w)
  have hval : ∀ w b, normChar (θ w) (ideleMap F E b) =
      if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0 then -1 else 1 := by
    intro w b
    have hne : (b : AF F).1 w ≠ 0 := (archPart b w).ne_zero
    apply Circle.ext
    rw [normChar_val]
    have e1 : θ w ((ideleMap F E b : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
        ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) : ℝ) : ℂ) := by
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      exact hθ w b
    rw [e1, ofReal_div_norm _ ((map_ne_zero _).2 hne)]
    split_ifs <;> simp
  have hgc : ∀ w, Continuous (g w) := fun w => by
    by_cases h : c w = 1
    · simp only [g, h, if_true]; exact continuous_const
    · simp only [g, h, if_false]; exact continuous_normChar _ (hθc w)
  have happ : ∀ x, (∏ w, g w) x = ∏ w, g w x := fun x => MonoidHom.finsetProd_apply _ _ _
  have hc2 : ∀ w, c w = 1 ∨ c w = -1 := fun w => sq_eq_one _ (by simp only [c]; rw [← map_mul]; exact hsq _)
  refine ⟨∏ w, g w, ?_, fun b => ?_, fun b hb => ?_⟩
  · have : ⇑(∏ w, g w) = fun x => ∏ w, g w x := funext happ
    rw [this]; exact continuous_finsetProd _ fun w _ => hgc w
  · apply sq_eq_one
    rw [happ, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply, mul_one]
    · simp only [g, h, if_false]
      rw [hval]; split_ifs <;> simp
  · rw [happ, eta_eq_prod η hsq b hb]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply]
      change 1 = if _ then c w else 1
      rw [h]; split_ifs <;> rfl
    · have h' : c w = -1 := (hc2 w).resolve_left h
      simp only [g, h, if_false]
      rw [hval]
      change _ = if _ then c w else 1
      rw [h']

end GlobalTheory.ArchSignChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PairCoords

def pairBil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {d : ℕ}
    (K : Matrix (Fin d) (Fin d) S) : LinearMap.BilinForm R (Fin d → S) :=
  LinearMap.mk₂ R (fun b a => Algebra.trace R S (-∑ j, ∑ l, b j * K j l * c (a l)))
    (fun b b' a => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add, map_add (f := _)])
    (fun r b a => by
      simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, ← smul_neg, map_smul, smul_eq_mul])
    (fun b a a' => by
      simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, neg_add])
    (fun r b a => by
      simp only [Pi.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum, ← smul_neg, smul_eq_mul])

theorem pairBil_apply {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {d : ℕ}
    (K : Matrix (Fin d) (Fin d) S) (b a : Fin d → S) :
    pairBil c K b a = Algebra.trace R S (-∑ j, ∑ l, b j * K j l * c (a l)) := rfl

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CharZero F]

theorem eq_zero_of_pairBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {K : Matrix (Fin d) (Fin d) E}
    (hK : K.det ≠ 0) (b : Fin d → E) (hb : ∀ a, pairBil σ K b a = 0) : b = 0 := by
  have h1 : b ᵥ* K = 0 := by
    funext l
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    have := hb (Pi.single l (σ (-e)) : Fin d → E)
    rw [pairBil_apply] at this
    rw [Algebra.traceForm_apply, ← this]
    congr 1
    have hs : ∀ j, ∑ l', b j * K j l' * σ ((Pi.single l (σ (-e)) : Fin d → E) l') = b j * K j l * -e := fun j => by
      rw [Finset.sum_eq_single l]
      · simp [hσ]
      · intro l' _ h
        simp [Pi.single_apply, h]
      · simp
    simp only [hs, Matrix.vecMul, dotProduct, Pi.zero_apply, Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc b = b ᵥ* (K * K⁻¹) := by rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hK), Matrix.vecMul_one]
    _ = (b ᵥ* K) ᵥ* K⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

theorem nondegenerate_pairBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {K : Matrix (Fin d) (Fin d) E}
    (hK : K.det ≠ 0) : (pairBil σ K).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (fun b hb => eq_zero_of_pairBil σ hσ hK b hb)

end Field

end GlobalTheory.PairCoords

namespace GlobalTheory.PairCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_inclR (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem pairBil_incV (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (v w : Fin d → E) :
    pairBil (cA σ) (incM F K) (incV F v) (incV F w) = algebraMap F (AF F) (pairBil σ K v w) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [pairBil_apply, pairBil_apply, ← trace_inclR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [incV, incM, Matrix.map_apply, hc, map_mul, map_sum, map_neg]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.PairCoords

theorem GlobalTheory.PairCoords.exists_pair_coords : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → AE F E) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  intro F E _ _ _ _ _ σ d K hσ h2 hK hdet
  classical
  have hrk : Module.finrank F (Fin d → E) = 2 * d := by
    rw [Module.finrank_pi_fintype]
    simp [h2, mul_comm]
  let β : Module.Basis (Fin 2 × Fin d) F (Fin d → E) :=
    (Module.finBasisOfFinrankEq F (Fin d → E) hrk).reindex finProdFinEquiv.symm
  let hnd := GlobalTheory.PairCoords.nondegenerate_pairBil σ hσ hdet
  let β₂ := (GlobalTheory.PairCoords.pairBil σ K).dualBasis hnd β
  let e := TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin d => E)
  have hinc : ∀ v : Fin d → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v := fun v => by
    funext i
    rfl
  let B₁ := (β.baseChange (AF F)).map e
  let B₂ := (β₂.baseChange (AF F)).map e
  have hB₁ : ∀ l, B₁ l = incV F (β l) := fun l => by
    simp only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hB₂ : ∀ l, B₂ l = incV F (β₂ l) := fun l => by
    simp only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hk : ∀ k l, GlobalTheory.PairCoords.pairBil (cA σ) (incM F K) (B₂ k) (B₁ l) = if l = k then 1 else 0 := by
    intro k l
    rw [hB₁, hB₂, GlobalTheory.PairCoords.pairBil_incV, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a =
      Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) := by
    intro a b
    rw [← GlobalTheory.PairCoords.pairBil_apply]
    conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcc := GlobalTheory.PairCoords.cA_cA σ hσ
  have hK' : ∀ j l, cA σ (incM F K j l) = -incM F K l j := fun j l => by
    show inclR (F := F) (AF F) (σ (K j l)) = -inclR (F := F) (AF F) (K l j)
    rw [hK l j, map_neg]
  have h2' : ∀ a b : Fin d → AE F E, Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) =
      Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l)) := by
    intro a b
    let eA : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofBijective (cA σ) (Function.Involutive.bijective hcc)
    rw [← Algebra.trace_eq_of_algEquiv eA (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))]
    congr 1
    show _ = cA σ _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hcc, hK', ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hrat : ∀ (b : Module.Basis (Fin 2 × Fin d) F (Fin d → E)) (a : Fin d → E),
      ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k) := by
    intro b a
    funext k
    rw [← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
  exact ⟨B₁.equivFun, B₂.equivFun, h1, fun a b => (h1 a b).trans (h2' a b),
    fun a => ⟨_, hrat β a⟩, fun a => ⟨_, hrat β₂ a⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isProper_of_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H],
    IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  intro Ω _ _ H _ hP ξ hξ hrat
  obtain ⟨β, hβ⟩ := hrat
  obtain ⟨σ, j, r₂, rh, h1, h2, h3, h4, h5, h6⟩ := _root_.GlobalTheory.Nef.InfScale.scaling_expansion_infinity Ω
  have comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by rw [← Spec.map_comp]; rfl
  have compA : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
      {Z : Scheme.{0}} (h : Sp A ⟶ Z), spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by
    intros; rw [← Category.assoc, comp]
  have canc := (_root_.GlobalTheory.Nef.spMap_injective_cancel).1
  have cancS := (_root_.GlobalTheory.Nef.spMap_injective_cancel).2
  haveI := hP
  haveI : IsSeparated H.hom := inferInstance
  have sqr_hom : sqr H ≫ H.hom = H.hom := Over.w (𝟙 H * 𝟙 H)
  have hi : Function.Injective (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) :=
    IsFractionRing.injective _ _
  have ha : Function.Injective (algebraMap (RatFunc Ω) (LaurentSeries Ω)) := RingHom.injective _
  have hj : Function.Injective j := RingHom.injective _

  have hσ : spMap σ ≫ β = β ≫ sqr H := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [compA, ← h2, ← comp, Category.assoc, hβ, compA, h1, ← compA, hξ.scale, ← Category.assoc,
      ← Category.assoc, hβ]

  have hβb : β ≫ H.hom = spMap RatFunc.C := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, Category.comp_id, comp, comp, h6]
  have hsq : (spMap j ≫ β) ≫ H.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries Ω) (LaurentSeries Ω))) ≫ spMap PowerSeries.C := by
    rw [Category.assoc, hβb, comp, h5]; exact (comp _ _).symm
  have hE : ValuativeCriterion.Existence H.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed H.hom) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) H.hom).1
  let V : ValuativeCommSq H.hom :=
    { R := PowerSeries Ω
      K := LaurentSeries Ω
      i₁ := spMap j ≫ β
      i₂ := spMap PowerSeries.C
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l⟩⟩ := hE V
  have hζ1 : spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ l.l = spMap j ≫ β := l.fac_left
  have hζ2 : l.l ≫ H.hom = spMap PowerSeries.C := l.fac_right
  have hrC : (PowerSeries.rescale (2⁻¹ : Ω)).comp PowerSeries.C = PowerSeries.C := by
    refine RingHom.ext fun x => PowerSeries.ext fun n => ?_
    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with hn
    · subst hn; rw [pow_zero, _root_.one_mul]
    · rw [MulZeroClass.mul_zero]
  have hcc : (PowerSeries.constantCoeff (R := Ω)).comp (PowerSeries.rescale (2⁻¹ : Ω)) =
      PowerSeries.constantCoeff (R := Ω) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      _root_.one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hcC : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, PowerSeries.constantCoeff_C]; rfl

  have hζs : spMap (PowerSeries.rescale (2⁻¹ : Ω)) ≫ l.l = l.l ≫ sqr H := by
    refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hζ2, comp, hrC, sqr_hom, hζ2]
    · rw [compA, ← h3, ← comp, Category.assoc, hζ1, compA, h4, ← compA, hσ, ← Category.assoc,
        ← Category.assoc, hζ1]

  have hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((2⁻¹ : Ω) ^ n - 2) := by
    intro n hn
    rw [isUnit_iff_ne_zero, sub_ne_zero, inv_pow]
    intro h
    have h0 : (2 : Ω) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have e : (2 : Ω) ^ (n + 1) = 1 := by
      calc (2 : Ω) ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
        _ = 2 ^ n * (2 ^ n)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ h0
    have e' : (2 : ℕ) ^ (n + 1) = 1 := by exact_mod_cast e
    have : 1 < (2 : ℕ) ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hz := (_root_.GlobalTheory.Nef.triv_unique (Sp Ω) H Ω).2.1 (spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l)
    (by rw [Category.assoc, ← hζs, compA, hcc])
  have hzero : spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l = 𝟙 (Sp Ω) ≫ unitSec H := by
    rw [hz, Category.assoc (spMap _) l.l H.hom, hζ2, comp, hcC, show spMap (RingHom.id Ω) = 𝟙 (Sp Ω) from Spec.map_id _]
  have hζt : l.l = triv H (𝟙 (Sp Ω)) :=
    (_root_.GlobalTheory.Nef.triv_unique (Sp Ω) H Ω).2.2 inferInstance (2⁻¹) hunit (𝟙 _) l.l
      ⟨by rw [Category.comp_id]; exact hζ2, hzero, hζs⟩

  have hβu : β = spMap RatFunc.C ≫ unitSec H := by
    refine canc _ _ j hj _ _ _ ?_
    rw [← hζ1, hζt, triv, Category.id_comp, compA, ← h5, ← compA]
  refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
  · rw [hξ.base, triv_over]
  · rw [← hβ, hβu, compA, h6, triv, Category.id_comp, compA]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMemStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem : ∀ (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (w : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) → pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧ pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  first | exact @GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem | exact GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem | (intros; apply GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem <;> assumption)
end

