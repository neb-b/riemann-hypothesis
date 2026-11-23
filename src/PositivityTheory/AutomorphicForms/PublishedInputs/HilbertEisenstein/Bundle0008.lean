module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0004
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.OpenKernelHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open UpperTheory.HilbertEisensteinWeightOne.LibOpenLevel

namespace UpperTheory.HilbertEisensteinWeightOne.OpenKernelEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem le_exp_neg_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.2 (by omega)

theorem val_le_of_mem {w : HeightOneSpectrum (𝓞 F)} : ∀ (c : ℕ) {z : w.adicCompletionIntegers F},
    z ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c →
    Valued.v (z : w.adicCompletion F) ≤ WithZero.exp (-(c : ℤ))
  | 0, z, _ => by
    simpa using (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).1 z.2
  | c + 1, z, hz => by
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on (C := fun z : w.adicCompletionIntegers F =>
      Valued.v (z : w.adicCompletion F) ≤ WithZero.exp (-((c + 1 : ℕ) : ℤ))) hz (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · have h1 := val_le_of_mem c ha
      have h2 : Valued.v (b : w.adicCompletion F) < 1 :=
        (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).1 hb
      show Valued.v ((a : w.adicCompletion F) * b) ≤ _
      rw [map_mul, show (-((c + 1 : ℕ) : ℤ)) = -(c : ℤ) + -1 by push_cast; ring, WithZero.exp_add]
      exact mul_le_mul' h1 (le_exp_neg_one h2)
    · show Valued.v ((x : w.adicCompletion F) + y) ≤ _
      exact Valuation.map_add_le _ hx hy

def Cond (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) (a : Fin 2 → w.adicCompletion F) : Prop :=
  Valued.v (a 0) ≤ WithZero.exp (-(c : ℤ)) ∧ Valued.v (a 1 - 1) ≤ WithZero.exp (-(c : ℤ))

theorem cond_mul {w : HeightOneSpectrum (𝓞 F)} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w c)
    {a : Fin 2 → w.adicCompletion F} (ha : Cond w c a) : Cond w c (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) := by
  obtain ⟨h, hh, rfl⟩ := hg
  set I := IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c
  have hrow : ![(0 : (w.adicCompletionIntegers F) ⧸ I), 1] ᵥ*
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I) h : Matrix (Fin 2) (Fin 2) _) = ![0, 1] := hh
  have e0 : Ideal.Quotient.mk I ((h : Matrix (Fin 2) (Fin 2) _) 1 0) = 0 := by
    have := congrFun hrow 0
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have e1 : Ideal.Quotient.mk I ((h : Matrix (Fin 2) (Fin 2) _) 1 1) = 1 := by
    have := congrFun hrow 1
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have h10 := val_le_of_mem c (Ideal.Quotient.eq_zero_iff_mem.1 e0)
  have h11 := val_le_of_mem c (Ideal.Quotient.eq.1 (e1.trans (map_one _).symm))
  have hint : ∀ i j, Valued.v (((h : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)) i j : w.adicCompletionIntegers F) :
      w.adicCompletion F) ≤ 1 :=
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).1
      ((h : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)) i j).2
  have he : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)
  have ha1 : Valued.v (a 1) ≤ 1 := by
    have : a 1 = (a 1 - 1) + 1 := by ring
    rw [this]
    exact Valuation.map_add_le _ (ha.2.trans he) (by simp)
  have mle : ∀ {x y : w.adicCompletion F} {e f : WithZero (Multiplicative ℤ)}, Valued.v x ≤ e → Valued.v y ≤ f → Valued.v (x * y) ≤ e * f :=
    fun hx hy => by rw [map_mul]; exact mul_le_mul' hx hy
  set G : Matrix (Fin 2) (Fin 2) (w.adicCompletion F) :=
    ((Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers F).subtype h : GL (Fin 2) (w.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion F))
  have hG : ∀ i j, G i j = (((h : Matrix (Fin 2) (Fin 2) _) i j : w.adicCompletionIntegers F) : w.adicCompletion F) :=
    fun _ _ => rfl
  constructor
  · have e : (a ᵥ* G) 0 = a 0 * G 0 0 + a 1 * G 1 0 := by simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e, hG, hG]
    refine Valuation.map_add_le _ ?_ ?_
    · simpa using mle ha.1 (hint 0 0)
    · simpa using mle ha1 h10
  · have e : (a ᵥ* G) 1 - 1 = a 0 * G 0 1 + (a 1 - 1) * G 1 1 + (G 1 1 - 1) := by
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]; ring
    rw [e, hG, hG]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · simpa using mle ha.1 (hint 0 1)
    · simpa using mle ha.2 (hint 1 1)
    · exact h11

theorem pInf_vecMul (x : Fin 2 → Ad F) (k : GL (Fin 2) (Af F)) (j : Fin 2) :
    UpperTheory.V.TR.pInf F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) j) = UpperTheory.V.TR.pInf F (x j) := by
  rw [RingHom.map_vecMul]
  have e : (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) = 1 :=
    congrArg Units.val (UpperTheory.V.TR.pInf_finGL k)
  rw [e, Matrix.vecMul_one]
  rfl

theorem pLoc_vecMul (x : Fin 2 → Ad F) (k : GL (Fin 2) (Af F)) (w : HeightOneSpectrum (𝓞 F)) (j : Fin 2) :
    pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) j)) =
      ((fun i => pLoc F w (pFin F (x i))) ᵥ*
        (Matrix.GeneralLinearGroup.map (pLoc F w) k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) j := by
  rw [RingHom.map_vecMul]
  have e : (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = k :=
    congrArg Units.val (pFin_finGL k)
  rw [e, RingHom.map_vecMul]
  rfl

theorem cond_glob {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) {x : Fin 2 → Ad F}
    (hx : ∀ w, Valued.v (pLoc F w (pFin F (x 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (x 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) :
    ∀ w, Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤
          WithZero.exp (-(c w : ℤ)) := fun w => by
  have := cond_mul (mem_Kc.1 hk w) (a := fun i => pLoc F w (pFin F (x i))) (hx w)
  rw [pLoc_vecMul, pLoc_vecMul]
  exact this

open Classical in
theorem phi_vecMul {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (x : Fin 2 → Ad F) :
    Phi c (x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) = Phi c x := by
  have hinv : (x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) ᵥ* (finGL F 2 k⁻¹ : Matrix (Fin 2) (Fin 2) (Ad F)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
  have key : (∀ w, Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤
        WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤
          WithZero.exp (-(c w : ℤ))) ↔
      (∀ w, Valued.v (pLoc F w (pFin F (x 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (x 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) := by
    refine ⟨fun h => ?_, cond_glob hk⟩
    have := cond_glob (inv_mem hk) h
    rwa [hinv] at this
  simp only [Phi, pInf_vecMul]
  exact congrArg _ (if_congr key rfl rfl)

theorem det_mem {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (v : HeightOneSpectrum (𝓞 F)) :
    pLoc F v ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F) ∈ v.adicCompletionIntegers F := by
  obtain ⟨h, -, he⟩ := mem_Kc.1 hk v
  have e2 : (pLoc F v).mapMatrix (k : Matrix (Fin 2) (Fin 2) (Af F)) =
      (v.adicCompletionIntegers F).subtype.mapMatrix (h : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)) :=
    (congrArg Units.val he).symm
  have e : pLoc F v ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F) =
      (v.adicCompletionIntegers F).subtype (h : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.map_det, e2]
  rw [e]
  exact SetLike.coe_mem _

theorem module_finGL {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) :
    (IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det (finGL F 2 k)) : ℝ) = 1 := by
  rw [UpperTheory.V.TR.det_finGL, IdeleGroup.ideleModule_apply]
  have h1 : IdeleGroup.infiniteModule (finId F (Matrix.GeneralLinearGroup.det k) : IdeleGroup F) = 1 := by
    unfold IdeleGroup.infiniteModule
    refine Finset.prod_eq_one fun w _ => ?_
    have e : ((finId F (Matrix.GeneralLinearGroup.det k) : IdeleGroup F) : Ad F).1 = 1 := by
      change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
      simp
    rw [e, show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]
  have h2 : IdeleGroup.finiteModule (finId F (Matrix.GeneralLinearGroup.det k) : IdeleGroup F) = 1 := by
    refine IdeleGroup.finiteModule_eq_one_of_mem ((IdeleGroup.mem_standardOpenSubgroup F).2 fun v => ⟨?_, ?_⟩)
    · change pLoc F v ((1 : Af F) - 1 + (Matrix.GeneralLinearGroup.det k : Af F)) ∈ _
      rw [sub_self, zero_add]
      exact det_mem hk v
    · change pLoc F v ((1 : Af F) - 1 + (Matrix.GeneralLinearGroup.det k⁻¹ : Af F)) ∈ _
      rw [sub_self, zero_add]
      exact det_mem (inv_mem hk) v
  rw [h1, h2, mul_one]

theorem absD_mul {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (g : GA F 2) :
    absD (g * finGL F 2 k) = absD g := by
  unfold absD
  rw [map_mul, map_mul, Positive.val_mul, module_finGL hk, mul_one]

theorem thetaS_mul {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (h : GA F 2) :
    thetaS (Phi c) (h * finGL F 2 k) = thetaS (Phi c) h := by
  simp only [thetaS, Units.val_mul, ← Matrix.vecMul_vecMul, phi_vecMul hk]

theorem eis_glob {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (g : GA F 2) :
    Eis ω (Phi c) (g * finGL F 2 k) = Eis ω (Phi c) g := by
  have e : ∀ t u, eisInt ω (Phi c) (g * finGL F 2 k) t u = eisInt ω (Phi c) g t u := fun t u => by
    unfold eisInt
    rw [← mul_assoc, thetaS_mul hk, absD_mul hk]
  simp only [Eis, e]

end UpperTheory.HilbertEisensteinWeightOne.OpenKernelEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne

theorem open_kernel_holds : SPois → SInt → SSmooth → SOpen := by
  intro _ _ _ F _ _ _ ω c hH hs
  exact LibOpenLevel.isOpen_stab_of_glob hH _ fun k hk g => OpenKernelEisenstein.eis_glob (LibOpenLevel.mem_Kc.2 hk) g

end UpperTheory.HilbertEisensteinWeightOne
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinInvModuleSectionMul
section
noncomputable section

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def mn (M : Matrix (Fin 2) (Fin 2) (Ad F)) : ℝ := ∑ i, ∑ j, ‖UpperTheory.V.TR.pInf F (M i j)‖

theorem pLoc_pFin_algebraMap (w : HeightOneSpectrum (𝓞 F)) (x : F) :
    pLoc F w (pFin F (algebraMap F (Ad F) x)) = algebraMap F (w.adicCompletion F) x := rfl

theorem pFin_moduleSection_mul (t : {r : ℝ // 0 < r}) (a : Ideles F) :
    pFin F ((moduleSection (w0 F) t * a : Ideles F) : Ad F) = pFin F (a : Ad F) := by
  rw [Units.val_mul, map_mul]
  have h1 : pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
    rw [coe_moduleSection]; rfl
  rw [h1, one_mul]

theorem pFin_inv_moduleSection_mul (t : {r : ℝ // 0 < r}) (a : Ideles F) :
    pFin F (((moduleSection (w0 F) t * a)⁻¹ : Ideles F) : Ad F) = pFin F ((a⁻¹ : Ideles F) : Ad F) := by
  rw [mul_inv, ← map_inv, pFin_moduleSection_mul]

theorem rowA_eq (ξ : Fin 2 → F) (z : Ideles F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)) (hM : M * M' = 1) :
    rowA ξ = (rowA ξ ᵥ* ((z : Ad F) • M)) ᵥ* (((z⁻¹ : Ideles F) : Ad F) • M') := by
  rw [Matrix.vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul, hM,
    Matrix.vecMul_one]

theorem fin_part {e : HeightOneSpectrum (𝓞 F) → ℤ} (D : 𝓞 F)
    (hD : ∀ w, ∀ x : w.adicCompletion F, Valued.v x ≤ WithZero.exp (e w) →
      Valued.v (algebraMap F (w.adicCompletion F) (D : F) * x) ≤ 1)
    {K : Set (Ideles F)} (hK : IsCompact K) (Mf' : Matrix (Fin 2) (Fin 2) (Af F)) (hD0 : D ≠ 0) :
    ∃ D' : 𝓞 F, D' ≠ 0 ∧ ∀ a ∈ K, ∀ t : {r : ℝ // 0 < r}, ∀ (ξ : Fin 2 → F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)),
      M * M' = 1 → M'.map (pFin F) = Mf' →
      boxP e (rowA ξ ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M)) →
      ∀ j, ∃ r : 𝓞 F, (D' : F) * ξ j = r := by
  classical
  set S : Set (Af F) := ⋃ i : Fin 2, ⋃ j : Fin 2,
    (fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j) '' K with hSdef
  have hS : IsCompact S := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image ?_
    have hc : Continuous fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) :=
      (continuous_snd : Continuous (Prod.snd : InfiniteAdeleRing F × Af F → Af F)).comp
        (Units.continuous_coe_inv (M := Ad F))
    exact hc.mul continuous_const
  obtain ⟨D1, hD10, hD1⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  refine ⟨D * D1, mul_ne_zero hD0 hD10, fun a ha t ξ M M' hM hMf hbox j => ?_⟩
  set z : Ideles F := moduleSection (w0 F) t * a
  set v := rowA ξ ᵥ* ((z : Ad F) • M)
  have hrow := congrFun (rowA_eq ξ z M M' hM) j
  have hval : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (w.adicCompletion F) (((D * D1 : 𝓞 F) : F) * ξ j)) ≤ 1 := by
    intro w
    have h1 : algebraMap F (w.adicCompletion F) (ξ j) =
        ∑ i, pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j)) := by
      rw [← pLoc_pFin_algebraMap]
      change pLoc F w (pFin F (rowA ξ j)) = _
      rw [hrow]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pFin_inv_moduleSection_mul]
      congr 2
      rw [← hMf]
      rfl
    rw [map_mul, h1, Finset.mul_sum]
    refine Valuation.map_sum_le _ fun i _ => ?_
    have hA : Valued.v (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) ≤ 1 :=
      hD w _ (hbox w i)
    have hs : pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j ∈ S := by
      rw [hSdef]
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨a, ha, rfl⟩⟩⟩
    have hB : Valued.v (algebraMap F (w.adicCompletion F) (D1 : F) *
        (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) ≤ 1 := by
      have := hD1 _ hs w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact this
    have hc : ((D * D1 : 𝓞 F) : F) = (D : F) * (D1 : F) := by simp
    have key : algebraMap F (w.adicCompletion F) ((D * D1 : 𝓞 F) : F) *
        (pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) =
        (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) *
          (algebraMap F (w.adicCompletion F) (D1 : F) *
            (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) := by
      rw [hc, map_mul]
      ring
    rw [key, map_mul]
    exact (mul_le_mul' hA hB).trans_eq (one_mul 1)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
    (((D * D1 : 𝓞 F) : F) * ξ j) fun w =>
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans_le (hval w)
  exact ⟨r, hr.symm⟩

theorem entry_le_mn (B : Matrix (Fin 2) (Fin 2) (Ad F)) (i j : Fin 2) :
    ‖UpperTheory.V.TR.pInf F (B i j)‖ ≤ mn B := by
  unfold mn
  calc ‖UpperTheory.V.TR.pInf F (B i j)‖ ≤ ∑ j', ‖UpperTheory.V.TR.pInf F (B i j')‖ :=
        Finset.single_le_sum (f := fun j' => ‖UpperTheory.V.TR.pInf F (B i j')‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖UpperTheory.V.TR.pInf F (B i' j')‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖UpperTheory.V.TR.pInf F (B i' j')‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem mn_nonneg (B : Matrix (Fin 2) (Fin 2) (Ad F)) : 0 ≤ mn B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem mn_transpose (B : Matrix (Fin 2) (Fin 2) (Ad F)) : mn B.transpose = mn B := by
  unfold mn
  rw [Finset.sum_comm]
  rfl

theorem mn_mul_le_left (A B : Matrix (Fin 2) (Fin 2) (Ad F)) (H : ℝ)
    (hA : ∀ i k, ‖UpperTheory.V.TR.pInf F (A i k)‖ ≤ H) : mn (A * B) ≤ 8 * H * mn B := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hA 0 0)
  have h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn B := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖UpperTheory.V.TR.pInf F (A i k * B k j)‖ ≤ ∑ _k : Fin 2, H * mn B :=
          Finset.sum_le_sum fun k _ => by
            rw [map_mul]
            exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (entry_le_mn B k j) (norm_nonneg _) hH)
      _ = 2 * H * mn B := by simp [Finset.sum_const]; try ring
  calc mn (A * B) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 2 * H * mn B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 8 * H * mn B := by simp [Finset.sum_const]; try ring

theorem mn_mul_le_right (A B : Matrix (Fin 2) (Fin 2) (Ad F)) (H : ℝ)
    (hB : ∀ k j, ‖UpperTheory.V.TR.pInf F (B k j)‖ ≤ H) : mn (A * B) ≤ 8 * H * mn A := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hB 0 0)
  have h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn A := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖UpperTheory.V.TR.pInf F (A i k * B k j)‖ ≤ ∑ _k : Fin 2, H * mn A :=
          Finset.sum_le_sum fun k _ => by
            rw [map_mul, mul_comm H]
            exact (norm_mul_le _ _).trans (mul_le_mul (entry_le_mn A i k) (hB k j) (norm_nonneg _) (mn_nonneg A))
      _ = 2 * H * mn A := by simp [Finset.sum_const]; try ring
  calc mn (A * B) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 2 * H * mn A :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 8 * H * mn A := by simp [Finset.sum_const]; try ring

theorem norm_pInf_infGL_le (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i k : Fin 2) :
    ‖UpperTheory.V.TR.pInf F (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i k)‖ ≤
      UpperTheory.V.TR.height y := by
  have := Matrix.GeneralLinearGroup.map_apply (UpperTheory.V.TR.pInf F) i k (UpperTheory.V.TR.infGL F 2 y)
  rw [UpperTheory.V.TR.pInf_infGL] at this
  rw [← this]
  have h1 : ‖(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i k‖ ≤
      ‖UpperTheory.V.TR.toL (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))‖ :=
    (norm_le_pi_norm _ k).trans (norm_le_pi_norm _ i)
  have h2 := norm_nonneg (UpperTheory.V.TR.toL ((y⁻¹ : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))
  unfold UpperTheory.V.TR.height
  linarith

theorem height_inv (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : UpperTheory.V.TR.height y⁻¹ = UpperTheory.V.TR.height y := by
  unfold UpperTheory.V.TR.height
  rw [inv_inv]
  ring

theorem mn_bound (g : GA F 2) : ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F),
    mn ((g * UpperTheory.V.TR.infGL F 2 y)⁻¹ : GA F 2).val ≤ Cm * UpperTheory.V.TR.height y ∧
    mn (g * UpperTheory.V.TR.infGL F 2 y : GA F 2).val.transpose ≤ Cm * UpperTheory.V.TR.height y := by
  refine ⟨8 * (mn (g⁻¹ : GA F 2).val + mn (g : GA F 2).val),
    mul_nonneg (by norm_num) (add_nonneg (mn_nonneg _) (mn_nonneg _)), fun y => ⟨?_, ?_⟩⟩
  · have hH := one_le_height y
    rw [mul_inv_rev, ← map_inv, Units.val_mul]
    refine (mn_mul_le_left _ _ _ fun i k => (norm_pInf_infGL_le y⁻¹ i k).trans (height_inv y).le).trans ?_
    nlinarith [mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]
  · have hH := one_le_height y
    rw [mn_transpose, Units.val_mul]
    refine (mn_mul_le_right _ _ _ fun k j => norm_pInf_infGL_le y k j).trans ?_
    nlinarith [mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth
end
end

