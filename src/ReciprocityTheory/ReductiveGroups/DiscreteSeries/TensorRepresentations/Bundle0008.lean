module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TensorV
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockE
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefDTensActPow
section
noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def coefAm (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (g⁻¹)ᵀ g

def coefBm (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (-Xᵀ) X

theorem coefD_Am_exp (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    coefAm dual (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp ((s : ℂ) • coefBm dual X) := by
  cases dual
  · rfl
  · simp only [coefAm, coefBm, cond_true]
    rw [← Matrix.exp_neg, ← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_neg, Matrix.transpose_smul, smul_neg]

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def coefPm (B : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => ∑ d, B c d • LinearMap.proj d

theorem coefPm_apply (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → M) (c : Fin n) :
    coefPm B u c = ∑ d, B c d • u d := by
  simp [coefPm, LinearMap.sum_apply]

theorem coefPm_pow (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (u : Fin n → M) (c : Fin n) :
    ((coefPm (M := M) B) ^ j) u c = ∑ d, (B ^ j) c d • u d := by
  induction j generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, coefPm_apply, pow_succ']
    simp_rw [ih, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

theorem coefD_diag_pow (A : Module.End ℂ M) (k : ℕ) (u : Fin n → M) (c : Fin n) :
    ((diagOp (n := n) A) ^ k) u c = (A ^ k) (u c) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, diagOp_coord, ← Module.End.mul_apply, ← pow_succ]

theorem coefD_comm (A : Module.End ℂ M) (B : Matrix (Fin n) (Fin n) ℂ) :
    Commute (coefPm (M := M) B) (diagOp A) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, coefPm_apply, diagOp_coord, map_sum, map_smul]

theorem coefD_sum_ite (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = x then f x y else 0) = ∑ y, f c y := by
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem coefD_sum_ite' (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = y then f x y else 0) = ∑ x, f x c := by
  simp [Finset.sum_ite_eq]

theorem coefD_tensAct_eq (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (tensF dual E) X = coefPm (coefBm dual X) + diagOp (actM E X) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  simp only [actM, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, coefPm_apply, diagOp_coord, Pi.add_apply]
  cases dual
  · simp only [tensF, cond_false, coefBm, tensV_coord, smul_add, Finset.sum_add_distrib, smul_ite,
      smul_zero, coefD_sum_ite]
    rw [add_comm]
  · simp only [tensF, cond_true, coefBm, tensVd_coord, smul_sub, Finset.sum_sub_distrib, smul_ite,
      smul_zero, coefD_sum_ite', Matrix.neg_apply, Matrix.transpose_apply, neg_smul,
      Finset.sum_neg_distrib]
    abel

theorem coefD_tensAct_pow (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (u : Fin n → M) (c : Fin n) :
    ((actM (tensF dual E) X) ^ m) u c = ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) •
      ∑ d, ((coefBm dual X) ^ kl.1) c d • ((actM E X) ^ kl.2) (u d) := by
  rw [coefD_tensAct_eq, (coefD_comm (actM E X) (coefBm dual X)).add_pow', LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, Module.End.mul_apply,
    coefPm_pow]
  simp_rw [coefD_diag_pow]

end Alg

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

def coefTG (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, coefAm dual g c d • σ g (f d)

theorem coefD_tensGrp_eq (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    coefTG dual σ g f c = ∑ d, coefAm dual g c d • σ g (f d) := rfl

theorem coefD_comb (s : ℂ) (m : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (L : Fin n → Fin n → ℕ → ℂ) :
    s ^ m / (m.factorial : ℂ) * ∑ c, ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) *
        ∑ d, (B ^ kl.1) c d * L c d kl.2 =
      ∑ c, ∑ d, ∑ kl ∈ antidiagonal m,
        s ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * (s ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← mul_assoc, ← hkl, coefC_choose_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem coefD_taylor (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (Λ : (Fin n → H) →L[ℂ] ℂ) (w : Fin n → D) (s : ℝ)
    (hb : ∀ d, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) (w d) : D) : H)‖ ≤ a m) ∧
      Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
        Λ (fun c => ((((actM (tensF dual E) X) ^ m) w c : D) : H)))
      (Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H)))) := by
  set lc : Fin n → (H →L[ℂ] ℂ) := fun c => Λ.comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) c)
  have hΛ : ∀ u : Fin n → H, Λ u = ∑ c, lc c (u c) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  set B := coefBm dual X
  set Y := actM E X
  set L : Fin n → Fin n → ℕ → ℂ := fun c d k => lc c ((((Y ^ k) (w d) : D) : H))

  have hpair : ∀ c d, HasSum (fun m => ∑ kl ∈ antidiagonal m,
      (s : ℂ) ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * ((s : ℂ) ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2))
      (coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
    intro c d
    obtain ⟨a, ha, hs⟩ := hb d
    have hA := coefC_exp_entry_hasSum B s c d
    rw [← coefD_Am_exp] at hA
    have hA' := coefC_exp_entry_summable B s c d
    have horb := hasSum_orbit_of_bound hσ hD hX (w d) a ha 0 s (by simpa using hs)
    rw [exp_zero_smul, hσ.1.1] at horb
    have horb' := horb.mapL (lc c)
    have hσs : HasSum (fun k : ℕ => (s : ℂ) ^ k / (k.factorial : ℂ) * L c d k)
        (lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
      refine horb'.congr_fun fun k => ?_
      simp only [L, Y, ContinuousLinearMap.one_apply, map_smul, smul_eq_mul, sub_zero]
      push_cast
      ring
    have hσ' : Summable fun k : ℕ => ‖(s : ℂ) ^ k / (k.factorial : ℂ) * L c d k‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hs.mul_left ‖lc c‖)
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have h1 : ‖L c d k‖ ≤ ‖lc c‖ * a k := ((lc c).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (ha k) (norm_nonneg _))
      calc |s| ^ k / (k.factorial : ℝ) * ‖L c d k‖ ≤ |s| ^ k / (k.factorial : ℝ) * (‖lc c‖ * a k) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖lc c‖ * (a k * |s| ^ k / (k.factorial : ℝ)) := by ring
    have hmul := coefC_hasSum_mul hA hσs hA' hσ'
    exact hmul
  have htot := hasSum_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) =>
    hasSum_sum fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) => hpair c d
  have hR : Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H))) =
      ∑ c, ∑ d, coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H)) := by
    rw [hΛ]
    refine Finset.sum_congr rfl fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coefD_tensGrp_eq, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hR]
  refine htot.congr_fun fun m => ?_
  rw [hΛ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefD_tensAct_pow, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul]
  rw [← coefD_comb]

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem lowFock_exists (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E)
    {lam : Fin n → ℝ} (hlam : StrictAnti lam) {V : Submodule ℂ N} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    ∃ x ∈ tensFock (n := n) V, x ∈ physicalSubspace ε ∧ x ≠ 0 ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) x := by
  have hK : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  set S0 := lowerWedgeAlt ε
  have hw : ∀ a, (lfMat ε a a).mulVec (Pi.single S0 (1 : ℂ)) =
      (((rhoHol ε - rhoN ε) a : ℝ) : ℂ) • Pi.single S0 1 :=
    fun a => lfMat_mulVec_single ε a a S0 _ (lowerWedge_weight ε a)
  have hl : ∀ a b, b < a → ε a = ε b → (lfMat ε a b).mulVec (Pi.single S0 (1 : ℂ)) = 0 := by
    intro a b hba he
    have h0 : sgE ε cpFock cmFock a b (fockBasis n S0.1) = (0 : ℂ) • fockBasis n S0.1 := by
      rw [zero_smul]; exact lowerWedge_killed_by_lowering ε hba he
    simpa using lfMat_mulVec_single ε a b S0 0 h0
  have hne : (Pi.single S0 (1 : ℂ) : LfIdx ε → ℂ) ≠ 0 := by
    intro h
    have := congrFun h S0
    simp at this
  obtain ⟨x, hxV, hx0, hxw, hxh⟩ :=
    HW.parthasarathy_tensor_matrix ε hK hV (lfMat_kRel ε) (fun a b h => lfMat_conjTranspose ε h) hne hw hl
      (lf_dom hlam hK hV)
  have hwt : lowK ε lam + (rhoHol ε - rhoN ε) = lam - rhoC ε + rhoHol ε := by
    funext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  refine ⟨lfLift ε x, lfLift_mem_tensFock ε hxV, lfLift_mem_physSub ε x, lfLift_ne_zero ε hx0, ?_⟩
  rw [← hwt]
  exact lfLift_isKHWVec ε hxw hxh

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeB
section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.UnitB

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

theorem sg_mul_self (ε : Fin n → Bool) (c : Fin n) : sg ε c * sg ε c = 1 := by
  unfold sg
  split_ifs <;> norm_num

theorem star_sg (ε : Fin n → Bool) (c : Fin n) : star (sg ε c) = sg ε c := by
  unfold sg
  split_ifs <;> simp

theorem norm_sg (ε : Fin n → Bool) (c : Fin n) : ‖sg ε c‖ = 1 := by
  unfold sg
  split_ifs <;> simp

theorem Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sg ε) := rfl

def wt (dual : Bool) (ε : Fin n → Bool) (ξ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : ℂ :=
  cond dual (sg ε c * star (x ξ c)) (x ξ c)

theorem norm_wt (dual : Bool) (ε : Fin n → Bool) (ξ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    ‖wt dual ε ξ x c‖ = ‖x ξ c‖ := by
  cases dual
  · rfl
  · simp only [wt, cond_true, norm_mul, norm_sg, norm_star, one_mul]

theorem norm_entry_le (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖x i j‖ ≤ Real.sqrt (S7.hs x) := by
  have h1 : ‖x i j‖ ^ 2 ≤ ∑ j', ‖x i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖x i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖x i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖x i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖x i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : ‖x i j‖ ^ 2 ≤ S7.hs x := by
    simp only [S7.hs, Formalism.REAL.hs]
    exact h1.trans h2
  have h4 := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (norm_nonneg _)] at h4

theorem continuous_wt (dual : Bool) (ε : Fin n → Bool) (ξ c : Fin n) :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => wt dual ε ξ x c) := by
  have he : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => x ξ c) :=
    (continuous_apply c).comp (continuous_apply ξ)
  cases dual
  · exact he
  · exact continuous_const.mul he.star

def wtLin (dual : Bool) (ε : Fin n → Bool) (ξ c : Fin n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ where
  toFun x := wt dual ε ξ x c
  map_add' x y := by cases dual <;> simp [wt, mul_add]
  map_smul' r x := by
    cases dual <;> simp [wt, Complex.real_smul, Complex.conj_ofReal]; ring

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def cf (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) (ξ : Fin n)
    (F : Fin n → H) : Formalism.REAL.UJ ε → ℂ :=
  fun g => ∑ c, wt dual ε ξ (Formalism.MainNotions.S.umat g) c * inner ℂ y (σ (Formalism.MainNotions.S.umat g) (F c))

theorem cf_add (dual : Bool) (y : H) (ξ : Fin n) (F F' : Fin n → H) :
    cf dual ε σ y ξ (F + F') = cf dual ε σ y ξ F + cf dual ε σ y ξ F' := by
  funext g
  simp only [cf, Pi.add_apply, map_add (f := _), inner_add_right, mul_add, Finset.sum_add_distrib]

theorem cf_smul (dual : Bool) (y : H) (ξ : Fin n) (a : ℂ) (F : Fin n → H) :
    cf dual ε σ y ξ (a • F) = a • cf dual ε σ y ξ F := by
  funext g
  simp only [cf, Pi.smul_apply, map_smul, inner_smul_right, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := (hσ.2.2 v).comp_continuous continuous_umat fun g => g.2

theorem continuous_cf (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H) :
    Continuous (cf dual ε σ y ξ F) := by
  unfold cf
  exact continuous_finsetSum _ fun c _ => ((continuous_wt dual ε ξ c).comp continuous_umat).mul
    (continuous_const.inner (continuous_orbit hσ (F c)))

theorem memLp_cf (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H)
    (hW : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ y (σ (Formalism.MainNotions.S.umat g) (F c)))
      2 (Formalism.REAL.muG ε)) :
    MemLp (cf dual ε σ y ξ F) 2 (Formalism.REAL.muG ε) := by
  unfold cf
  refine MeasureTheory.memLp_finsetSum _ fun c _ => ?_
  refine MemLp.of_le (hW c) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (((continuous_wt dual ε ξ c).comp continuous_umat).mul
      (continuous_const.inner (continuous_orbit hσ (F c)))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_wt]
    exact mul_le_mul_of_nonneg_right (norm_entry_le _ ξ c) (norm_nonneg _)

end Rep

end ReciprocityTheory.ChartRestriction.DS.UnitB
end
end

