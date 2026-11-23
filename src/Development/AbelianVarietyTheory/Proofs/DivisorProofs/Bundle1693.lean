module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticCh
section
noncomputable section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

def mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) :
    ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) (x : κ → R) : mulQ χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulQ_neg_mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) : mulQ χ h (-A) (mulQ χ h A φ) = φ := by
  funext x
  rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulQ_schr {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (χ : AddChar R ℂ) (B : Matrix κ κ R)
    (hB : Bᵀ = B) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulQ χ (⅟2) (-B) (schr χ w φ) = schr χ (w.1, B *ᵥ w.1 + w.2) (mulQ χ (⅟2) (-B) φ) := by
  have hB' : (-B)ᵀ = -B := by rw [Matrix.transpose_neg, hB]
  funext x
  have key := quad_add (-B) hB' x w.1 w.2
  rw [Matrix.neg_mulVec, neg_neg] at key
  simp only [mulQ_apply, schr]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key]

theorem act_unip {F R κ : Type} [Field F] [CommRing R] [Algebra F R] [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F)
    (w : (κ → R) × (κ → R)) :
    act ((Matrix.fromBlocks 1 0 b 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) w =
      (w.1, b.map (algebraMap F R) *ᵥ w.1 + w.2) := by
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), act_fromBlocks]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def qI (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem eventually_integral (x : κ → AF F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun i => (x i).2.2

theorem finite_mulSupport {φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
  refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_integral x))).subset fun v hv => ?_
  intro h
  apply hv
  change φ v _ = 1
  rw [h.1, ind, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from h.2), Pi.one_apply]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulQ_mem_SB {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) {φ : (κ → K) → ℂ} (hφ : φ ∈ SB (κ → K)) :
    mulQ χ h A φ ∈ SB (κ → K) :=
  ⟨((GlobalTheory.SchrSBFin.isLocallyConstant_addChar χ hχ).comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem mulQ_bijOn {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) :
    Set.BijOn (mulQ χ h A) (SB (κ → K) : Set _) (SB (κ → K) : Set _) := by
  refine Set.InvOn.bijOn (f' := mulQ χ h (-A)) ⟨fun φ _ => mulQ_neg_mulQ χ h A φ, fun φ _ => ?_⟩
    (fun φ hφ => mulQ_mem_SB χ hχ h A hφ) (fun φ hφ => mulQ_mem_SB χ hχ h (-A) hφ)
  have := mulQ_neg_mulQ χ h (-A) φ
  rwa [neg_neg] at this

theorem quad_mem {v : Pl (F := F)} {h : Fv F v} (hh : h ∈ v.adicCompletionIntegers F) {A : Matrix κ κ (Fv F v)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) {x : κ → Fv F v} (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    quad h A x ∈ v.adicCompletionIntegers F := by
  unfold quad
  refine mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))

theorem invOf_two_eq (v : Pl (F := F)) : ⅟(2 : Fv F v) = algebraMap F (Fv F v) (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem eventually_mulQ_ind (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (b : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (ind κ v) = ind κ v := by
  filter_upwards [GlobalTheory.psiLoc_eventually_trivial_integers ψ hψ, eventually_algebraMap_mem_integers (2⁻¹ : F),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_algebraMap_mem_integers (b i j)] with v h1 h2 h3
  funext x
  rw [mulQ_apply]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hq : quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) x ∈ v.adicCompletionIntegers F :=
      quad_mem (show ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F by rw [invOf_two_eq]; exact h2) (fun i j => neg_mem (h3 i j)) hx
    rw [GlobalTheory.LatVac.psiAt_apply, h1 _ hq, one_mul]
  · rw [ind, Set.indicator_of_notMem (show x ∉ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), mul_zero]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem invOf_two_eq' (R : Type) [CommRing R] [Algebra F R] [Invertible (2 : R)] : ⅟(2 : R) = algebraMap F R (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem evFin_quad (b : Matrix κ κ F) (v : Pl (F := F)) (x : κ → AF F) :
    evFin F v (quad (⅟2) (-(b.map (algebraMap F (AF F)))) x) =
      quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) (fun i => evFin F v (x i)) := by
  have h : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    have hmap : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
      refine (invOf_eq_right_inv ?_).symm
      have hmul : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
      rwa [map_mul, map_ofNat] at hmul
    rw [hmap, invOf_eq_inv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [quad, dotProduct, Matrix.mulVec, map_sum, h]

theorem psi_quad_rat (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (ξ : κ → F) :
    ψ (quad (⅟2) (-(b.map (algebraMap F (AF F)))) (fun i => algebraMap F (AF F) (ξ i))) = 1 := by
  have h := map_quad (algebraMap F (AF F)) (2⁻¹ : F) (-b) ξ
  rw [Matrix.map_neg _ (map_neg _), ← invOf_two_eq'] at h
  rw [← h]
  exact hψ.2.1 _

theorem thetaSum_mulQ (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) Φ) = thetaSum F Φ := by
  unfold thetaSum
  congr 1
  funext ξ
  rw [mulQ_apply, psi_quad_rat ψ hψ b ξ, one_mul]

theorem archMul_neg_mul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : archMul h A y * archMul h (-A) y = 1 := by
  unfold archMul
  rw [← AddChar.map_add_eq_mul, quad_neg, map_neg, neg_neg, neg_add_cancel, AddChar.map_zero_eq_one]

theorem surjective_arch (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.Surjective (SchwartzMap.smulLeftCLM ℂ (archMul h A) : SInf F κ →L[ℂ] SInf F κ) := by
  intro f
  refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul h (-A)) f, ?_⟩
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul, smul_eq_mul, ← mul_assoc,
    archMul_neg_mul, one_mul]

theorem at_pairA (a : AF F) : At (evI F) (pairA F (fstA F a) 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem mulQ_pure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (f : SInf F κ)
    {φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ} (hφ : IsFam φ) :
    mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.smulLeftCLM ℂ
                   (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
        (fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (φ v)) := by
  funext x
  set Q := quad (⅟2) (-(b.map (algebraMap F (AF F)))) x with hQ
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local F ψ hψ.1 Q
  simp only [hQ, evFin_quad] at hfin hprod
  have harch : ψ (pairA F (fstA F Q) 0) =
      archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) := by
    rw [hψ.2.2 _ (at_pairA Q)]
    have e1 : evI F (pairA F (fstA F Q) 0) =
        quad (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) :=
      map_quad (qI F) _ _ x
    rw [e1, archMul, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [← hQ] at hprod
  change ψ Q * (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
    (SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
      (fun i => evI F (x i)) * ∏ᶠ v, (GlobalTheory.LatVac.psiAt ψ v (quad (⅟2) (-(b.map (algebraMap F (Fv F v))))
        (fun i => evFin F v (x i))) * φ v fun i => evFin F v (x i))
  rw [finprod_mul_distrib hfin (finite_mulSupport hφ x), SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    smul_eq_mul, hprod, harch]
  ring

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad archMul)


open scoped Classical in
theorem hasOp_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b → HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  intro F _ _ ψ hψ κ _ _ b hb
  have hB : ∀ (R : Type) [CommRing R] [Algebra F R], (b.map (algebraMap F R))ᵀ = b.map (algebraMap F R) :=
    fun R _ _ => by rw [← Matrix.transpose_map, hb]
  refine ⟨mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))), 1,
    SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))),
    fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))), one_ne_zero,
    surjective_arch _ _, fun v => mulQ_bijOn _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v) _ _, fun v w φ _ => ?_,
    eventually_mulQ_ind ψ hψ.1 b, fun f φ hφ => ⟨mulQ_pure ψ hψ b f hφ, fun w => ?_, ?_⟩⟩
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [thetaSum_mulQ ψ hψ b, one_mul]

end GlobalTheory.RatWeilUnip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationGeOfIntegralAtPrime
section
open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.FunObj.SqNum.MeanValLow

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : Formalism.PairingDivisionLocalBalance.Pl K) {a : 𝓞 K} (ha : a ∉ w.asIdeal) : Formalism.DivisionValues.vw w (a : K) = 0 := by
  classical
  have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact ha w.asIdeal.zero_mem
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
  by_contra h
  have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
    intro h0
    exact h (by rw [h0]; rfl)
  exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))

theorem vw_int_nonneg (w : Formalism.PairingDivisionLocalBalance.Pl K) (a : 𝓞 K) : 0 ≤ Formalism.DivisionValues.vw w (a : K) := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_mul (w : Formalism.PairingDivisionLocalBalance.Pl K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K w ((FractionalIdeal.spanSingleton_ne_zero_iff).2 ha)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hb)

theorem vw_pow (w : Formalism.PairingDivisionLocalBalance.Pl K) (a : K) (n : ℕ) : Formalism.DivisionValues.vw w (a ^ n) = n * Formalism.DivisionValues.vw w a := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem coeff_zero_mem (σ : K →+* ℂ) {δ : ℂ} (hδ : IsIntegral ℤ δ) {q : K[X]} (hq : IsMinPol σ δ q) :
    ∃ b : 𝓞 K, (b : K) = q.coeff 0 := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := ((algebraMap K ℂ).comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hi : IsIntegral (𝓞 K) δ := hδ.tower_top
  have e := minpoly.isIntegrallyClosed_eq_field_fractions' K hi
  refine ⟨(minpoly (𝓞 K) δ).coeff 0, ?_⟩
  rw [hq.eq_minpoly, e, coeff_map]

end GlobalTheory.FunObj.SqNum.MeanValLow


open GlobalTheory.FunObj.SqNum.MeanValLow in
theorem GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  intro K _ _ σ β p hp hβ c hc l hl w hw m ⟨n, hn, hint⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hn
    exact hl.one_lt.ne' hn
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hlm : (l : K) ^ m ≠ 0 := pow_ne_zero _ hl0
  set a : K := (n : K) * (l : K) ^ m * c with ha_def
  have ha : a ≠ 0 := mul_ne_zero (mul_ne_zero hnK hlm) hc
  have hδ : IsIntegral ℤ (σ a * β) := by
    have e : σ a * β = (n : ℂ) * ((l : ℂ) ^ m * (σ c * β)) := by
      simp only [a, map_mul, map_pow, map_natCast]; ring
    rw [e]; exact hint
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℤ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hK : IsIntegral K (σ a * β) := hδ.tower_top
  have hq : IsMinPol σ (σ a * β) (minpoly K (σ a * β)) :=
    ⟨minpoly.monic hK, minpoly.irreducible hK, minpoly.aeval K (σ a * β)⟩
  obtain ⟨b, hb⟩ := coeff_zero_mem σ hδ hq
  have eq := hp.scaleRoots_eq hq ha
  obtain ⟨hc0, hd⟩ := hp.ne_zero hβ
  rw [eq, coeff_scaleRoots, Nat.sub_zero] at hb
  have h0 : 0 ≤ Formalism.DivisionValues.vw w (p.coeff 0 * a ^ p.natDegree) := hb ▸ vw_int_nonneg w b
  rw [vw_mul w hc0 (pow_ne_zero _ ha), vw_pow, ha_def, vw_mul w (mul_ne_zero hnK hlm) hc,
    vw_mul w hnK hlm, vw_pow] at h0
  have hnw : (n : 𝓞 K) ∉ w.asIdeal := by
    intro hn'
    obtain ⟨x, y, e'⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e']
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hn')) (Ideal.mul_mem_left _ _ (by simpa using hw))
  have hvn : Formalism.DivisionValues.vw w (n : K) = 0 := by
    have := vw_eq_zero_of_notMem w hnw
    simpa using this
  rw [hvn] at h0
  have hdpos : (0 : ℝ) < p.natDegree := by exact_mod_cast Nat.pos_of_ne_zero hd
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  have h1 : (0 : ℝ) ≤ (Formalism.DivisionValues.vw w (p.coeff 0) : ℝ) + p.natDegree * ((m : ℝ) * Formalism.DivisionValues.vw w (l : K) + Formalism.DivisionValues.vw w c) := by
    have := (Int.cast_le (R := ℝ)).2 h0
    push_cast at this
    linarith
  have h2 : -((m : ℝ) * Formalism.DivisionValues.vw w (l : K) + Formalism.DivisionValues.vw w c) ≤ (Formalism.DivisionValues.vw w (p.coeff 0) : ℝ) / p.natDegree := by
    rw [le_div_iff₀ hdpos]; linarith
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedProjectionPreservesSchwartzAdm
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def finRepl (v : Pl (F := F)) (z : κ → Af F) (x : κ → Fv F v) : κ → Af F :=
  fun i => z i - GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) + GlobalTheory.AdelicU.singleFin v (x i)

def finProj (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (g : (κ → Af F) → ℂ) :
    (κ → Af F) → ℂ :=
  fun z => φ₀ (fun i => evalV F v (z i)) * l fun x => g (finRepl v z x)

theorem evalV_finRepl (v : Pl (F := F)) (z : κ → Af F) (x : κ → Fv F v) (i : κ) :
    evalV F v (finRepl v z x i) = x i := by
  simp [finRepl, GlobalTheory.AdelicU.evalV_singleFin_self]

theorem finRepl_finRepl (v : Pl (F := F)) (z : κ → Af F) (x : κ → Fv F v) :
    finRepl v (finRepl v z x) (fun i => evalV F v (z i)) = z := by
  funext i
  have := evalV_finRepl v z x i
  simp only [finRepl] at this ⊢
  rw [this]; abel

theorem continuous_finRepl (v : Pl (F := F)) :
    Continuous fun p : (κ → Af F) × (κ → Fv F v) => finRepl v p.1 p.2 := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.1 i := (continuous_apply i).comp continuous_fst
  have h2 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.2 i := (continuous_apply i).comp continuous_snd
  exact (h1.sub ((GlobalTheory.AdelicU.continuous_singleFin v).comp ((RestrictedProduct.continuous_eval v).comp h1))).add
    ((GlobalTheory.AdelicU.continuous_singleFin v).comp h2)

theorem finProj_mem_SB [Fintype κ] (v : Pl (F := F)) {φ₀ : (κ → Fv F v) → ℂ} (hφ₀ : φ₀ ∈ SB (κ → Fv F v))
    (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    finProj v φ₀ l g ∈ SB (κ → Af F) := by
  have : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have he : Continuous fun z : κ → Af F => fun i => evalV F v (z i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hs : Continuous fun z : κ → Af F => fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) :=
    continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp
      ((RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro z₀
    let δ : (κ → Af F) → (κ → Af F) := fun z =>
      (z₀ - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z₀ i))) -
        (z - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)))
    have hδ : Filter.Tendsto δ (nhds z₀) (nhds 0) := by
      have hc : Continuous δ := continuous_const.sub (continuous_id.sub hs)
      simpa [δ] using hc.tendsto z₀
    have hφe : ∀ᶠ z in nhds z₀, φ₀ (fun i => evalV F v (z i)) = φ₀ (fun i => evalV F v (z₀ i)) :=
      (hφ₀.1.comp_continuous he).eventually_eq z₀
    filter_upwards [hδ.eventually (GlobalTheory.SBConv.eventually_translate hg), hφe] with z hz h1
    simp only [finProj]
    rw [h1]
    congr 2
    funext x
    have e : finRepl v z x = finRepl v z₀ x - δ z := by
      funext i; simp only [finRepl, δ, Pi.sub_apply]; abel
    rw [e, hz]
  · refine HasCompactSupport.intro ((hg.2.isCompact.prod hφ₀.2.isCompact).image (continuous_finRepl v)) ?_
    intro z hz
    by_contra h
    apply hz
    simp only [finProj] at h
    have h1 : φ₀ (fun i => evalV F v (z i)) ≠ 0 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    obtain ⟨x, hx⟩ : ∃ x, g (finRepl v z x) ≠ 0 := by
      by_contra hc
      push Not at hc
      apply h2
      have : (fun x => g (finRepl v z x)) = 0 := funext hc
      rw [this, map_zero]
    refine ⟨(finRepl v z x, fun i => evalV F v (z i)), ⟨subset_tsupport _ hx, subset_tsupport _ h1⟩, ?_⟩
    exact finRepl_finRepl v z x

theorem proj_pureA [Fintype κ] (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    proj v φ₀ l (pureA F f g) = pureA F f (finProj v φ₀ l g) := by
  funext y
  have e : (fun x => pureA F f g (repl v y x)) =
      f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) • fun x => g (finRepl v (fun i => (y i).2) x) := by
    funext x
    have a1 : ∀ i, (repl v y x i).1 = (y i).1 := fun i => by
      show (y i).1 - (0 : Ainf F) + 0 = (y i).1
      rw [sub_zero, add_zero]
    have a2 : ∀ i, (repl v y x i).2 = finRepl v (fun i => (y i).2) x i := fun i => rfl
    show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (repl v y x i).1) * g (fun i => (repl v y x i).2) = _
    simp only [a1, a2, Pi.smul_apply, smul_eq_mul]
  rw [proj_apply, e, map_smul]
  simp only [pureA, finProj, smul_eq_mul]
  change φ₀ (fun i => evalV F v (y i).2) * _ = _
  ring

theorem proj_schA_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  intro F _ _ κ _ v φ₀ hφ₀ l
  refine ⟨fun Φ hΦ => ?_, fun L hL => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      rw [proj_pureA]
      exact Submodule.subset_span ⟨f, _, finProj_mem_SB v hφ₀ l hg, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · intro g hg
    obtain ⟨T, hT⟩ := hL _ (finProj_mem_SB v hφ₀ l hg)
    exact ⟨T, fun f => by rw [LinearMap.comp_apply, proj_pureA, hT]⟩

end GlobalTheory.MixedForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovolStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.glOne_finvol | exact GlobalTheory.GLOneVol.glOne_finvol | (intros; apply GlobalTheory.GLOneVol.glOne_finvol <;> assumption)
end

