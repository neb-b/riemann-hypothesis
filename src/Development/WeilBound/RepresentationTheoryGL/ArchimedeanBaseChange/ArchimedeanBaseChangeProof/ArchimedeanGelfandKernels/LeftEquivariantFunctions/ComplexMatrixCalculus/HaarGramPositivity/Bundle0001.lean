module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.ContDiffOnMatrixIff
section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxe

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem contDiff_entry (i : ι) (j : κ) : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i j) := by
  have h1 : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i) := contDiff_pi.mp contDiff_id i
  exact contDiff_pi.mp h1 j

theorem contDiffOn_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (f : E → Matrix ι κ ℂ) : ContDiffOn ℝ ∞ f s ↔ ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s := by
  constructor
  · intro h i j
    exact contDiffOn_pi.mp (contDiffOn_pi.mp h i) j
  · intro h
    exact contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => h i j

theorem contDiff_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Matrix ι κ ℂ) : ContDiff ℝ ∞ f ↔ ∀ i j, ContDiff ℝ ∞ (fun x => f x i j) := by
  constructor
  · intro h i j
    exact contDiff_pi.mp (contDiff_pi.mp h i) j
  · intro h
    exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j

theorem contDiff_det : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have e : (fun x : Matrix ι ι ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x; exact Matrix.det_apply' x
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry _ _)

theorem contDiff_adjugate : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.adjugate) := by
  rw [contDiff_matrix_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  refine contDiff_det.comp ?_
  rw [contDiff_matrix_iff]
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_det_ne : IsOpen {x : Matrix ι ι ℂ | x.det ≠ 0} :=
  isOpen_ne_fun (contDiff_det (ι := ι)).continuous continuous_const

theorem contDiffOn_inv : ContDiffOn ℝ ∞ (fun x : Matrix ι ι ℂ => x⁻¹) {x | x.det ≠ 0} := by
  have h : ∀ x ∈ {x : Matrix ι ι ℂ | x.det ≠ 0}, x⁻¹ = (x.det)⁻¹ • x.adjugate := fun x _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContDiffOn.congr ?_ h
  rw [contDiffOn_matrix_iff]
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (contDiff_det.contDiffOn.inv fun x hx => hx).mul (contDiff_matrix_iff _ |>.mp contDiff_adjugate i j).contDiffOn

def entL (a : ι) (k : κ) : Matrix ι κ ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap { toFun := fun x => x a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem entL_apply (a : ι) (k : κ) (x : Matrix ι κ ℂ) : entL a k x = x a k := rfl

theorem hasFDerivAt_inv_one :
    HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹) (-ContinuousLinearMap.id ℝ (Matrix ι ι ℂ)) 1 := by
  have hd : DifferentiableAt ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 :=
    (contDiffOn_inv.contDiffAt (isOpen_det_ne.mem_nhds (by simp))).differentiableAt (by simp)
  have hL := hd.hasFDerivAt
  set L := fderiv ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 with hLdef
  suffices hLe : L = -ContinuousLinearMap.id ℝ (Matrix ι ι ℂ) by rwa [hLe] at hL
  have hev : ∀ a b : ι, (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b) =ᶠ[nhds 1] fun _ => (1 : Matrix ι ι ℂ) a b := by
    intro a b
    filter_upwards [isOpen_det_ne.mem_nhds (show (1 : Matrix ι ι ℂ).det ≠ 0 by simp)] with x hx
    rw [Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)]
  have hent : ∀ a b : ι, HasFDerivAt (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b)
      (∑ k, ((1 : Matrix ι ι ℂ) a k • (entL k b).comp L + ((1 : Matrix ι ι ℂ)⁻¹ k b) • entL a k)) 1 := by
    intro a b
    simp only [Matrix.mul_apply]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k (x : Matrix ι ι ℂ) => x a k * x⁻¹ k b) fun k _ => ?_
    have h1 : HasFDerivAt (fun x : Matrix ι ι ℂ => x a k) (entL a k) 1 := (entL a k).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹ k b) ((entL k b).comp L) 1 := (entL k b).hasFDerivAt.comp 1 hL
    exact h1.mul h2
  ext X i j
  have h0 := (hent i j).unique ((hasFDerivAt_const ((1 : Matrix ι ι ℂ) i j) (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq (hev i j))
  have h0X := congrArg (fun T : Matrix ι ι ℂ →L[ℝ] ℂ => T X) h0
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, entL_apply, smul_eq_mul, inv_one,
    ContinuousLinearMap.zero_apply, Finset.sum_add_distrib] at h0X
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq'] at h0X
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Matrix.neg_apply]
  linear_combination h0X

end PositivityTheory.RgBcC.Cxe
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.EpowMulOfKill
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxeeig

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem inf_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  show (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1) ≤ ⊤)

theorem diffAt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : DifferentiableAt ℝ f g :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hg)

theorem rd_std (F : Mat n → ℂ) (g X : Mat n) : Rd X F g = fderiv ℝ F g (g * X) := rfl

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

theorem rd_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) := by
  exact (hf.fderiv_of_isOpen isOpen_GLs inf_add_one_le).clm_apply (mulR X).contDiff.contDiffOn

theorem eu_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (b c : Fin n) : ContDiffOn ℝ ∞ (Eu s b c f) (GLs n) := by
  unfold Eu
  exact ((rd_contDiffOn hf _).add ((rd_contDiffOn hf _).const_smul _)).const_smul _

theorem epow_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) : ∀ m b c, ContDiffOn ℝ ∞ (Epow s m b c f) (GLs n) := by
  intro m
  induction m with
  | zero =>
    intro b c
    simp only [Epow]
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    intro b c
    have e : Epow s (m + 1) b c f = fun x => ∑ d, Eu s b d (Epow s m d c f) x := by
      funext x; simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun d _ => eu_contDiffOn (ih d c) s b d

theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f₁ f₂ : Mat n → V} {g : Mat n}
    (h : f₁ =ᶠ[𝓝 g] f₂) (s : Bool) (b c : Fin n) : Eu s b c f₁ g = Eu s b c f₂ g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h.fderiv_eq]

theorem eu_mul {F a : Mat n → ℂ} {g : Mat n} (hF : DifferentiableAt ℝ F g) (ha : DifferentiableAt ℝ a g)
    (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => F x * a x) g = F g * Eu s b c a g + a g * Eu s b c F g := by
  have hm : fderiv ℝ (fun x => F x * a x) g = F g • fderiv ℝ a g + a g • fderiv ℝ F g :=
    (hF.hasFDerivAt.fun_mul ha.hasFDerivAt).fderiv
  have key : ∀ X : Mat n, Rd X (fun x => F x * a x) g = F g * Rd X a g + a g * Rd X F g := by
    intro X
    rw [rd_std, rd_std, rd_std, hm]
    simp [smul_eq_mul]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, smul_eq_mul]
  ring

theorem eu_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (ψ : ι → Mat n → ℂ) (v : ι → V)
    {g : Mat n} (hψ : ∀ i, DifferentiableAt ℝ (ψ i) g) (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => ∑ i, ψ i x • v i) g = ∑ i, Eu s b c (ψ i) g • v i := by
  have key : ∀ X : Mat n, Rd X (fun x => ∑ i, ψ i x • v i) g = ∑ i, Rd X (ψ i) g • v i := by
    intro X
    simp only [rd_std]
    have h : HasFDerivAt (fun x => ∑ i, ψ i x • v i) (∑ i, (fderiv ℝ (ψ i) g).smulRight (v i)) g :=
      HasFDerivAt.fun_sum fun i _ => (hψ i).hasFDerivAt.smul_const (v i)
    unfold Rd
    rw [h.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul _ (Rd (Matrix.single b c Complex.I) (ψ i) g), ← add_smul, smul_smul]
  congr 1

theorem epow_mul_of_kill {F G : Mat n → ℂ} (hF : ContDiffOn ℝ ∞ F (GLs n)) (hG : ContDiffOn ℝ ∞ G (GLs n)) (s : Bool)
    (hk : ∀ g ∈ GLs n, ∀ b c, Eu s b c F g = 0) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => F x * G x) g = F g * Epow s m b c G g := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have he : Epow s m d c (fun x => F x * G x) =ᶠ[𝓝 g] fun x => F x * Epow s m d c G x :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
    rw [eu_congr he, eu_mul (diffAt hF hg) (diffAt (epow_contDiffOn hG s m d c) hg), hk g hg, mul_zero, add_zero]

theorem epow_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ι → Mat n → ℂ) (v : ι → V)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (GLs n)) (s : Bool) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => ∑ i, φ i x • v i) g = ∑ i, Epow s m b c (φ i) g • v i := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply]
    have step : ∀ d, Eu s b d (Epow s m d c fun x => ∑ i, φ i x • v i) g =
        ∑ i, Eu s b d (Epow s m d c (φ i)) g • v i := by
      intro d
      have he : (Epow s m d c fun x => ∑ i, φ i x • v i) =ᶠ[𝓝 g] fun x => ∑ i, Epow s m d c (φ i) x • v i :=
        Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
      rw [eu_congr he, eu_sum_smul _ _ (fun i => diffAt (epow_contDiffOn (hφ i) s m d c) hg)]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]

end PositivityTheory.RgBcC.Cxeeig

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC.Cxeeig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eigProd : EigProd := by
  intro n χ ι V _ _ _ h a v hh ha hhe hae
  have hφ : ∀ i, ContDiffOn ℝ ∞ (fun x => h i x * a i x) (GLs n) := fun i => (hh i).mul (ha i)
  intro s m g hg
  have hsum : gel s m (fun x => ∑ i, (h i x * a i x) • v i) g =
      ∑ i, gel s m (fun x => h i x * a i x) g • v i := by
    simp only [gel, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun b _ => epow_sum_smul (fun i x => h i x * a i x) v hφ s m b b g hg, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
  have hone : ∀ i, gel s m (fun x => h i x * a i x) g = GlobalTheory.Dec.gelfVal (χ s) m * (h i g * a i g) := by
    intro i
    cases s with
    | true =>
      have e : (fun x => h i x * a i x) = fun x => a i x * h i x := by funext x; ring
      simp only [gel, Finset.sum_apply]
      rw [e, Finset.sum_congr rfl fun b _ => epow_mul_of_kill (ha i) (hh i) true (fun g hg b c => (hae i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hhe i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
    | false =>
      simp only [gel, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun b _ => epow_mul_of_kill (hh i) (ha i) false (fun g hg b c => (hhe i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hae i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hone i, smul_smul]

end PositivityTheory.RgBcC
end
end

