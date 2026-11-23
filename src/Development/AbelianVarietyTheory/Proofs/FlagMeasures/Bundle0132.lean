module

public import Mathlib
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace GlobalTheory.SmoothVecMod

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]

section Gen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (h : ∀ g, inUJ ε g → f' g = f g) : SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (h g hgJ).trans (hfF g hg hgJ)⟩

lemma smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) : SmoothOnGV ε (fun g => f g + c • f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c), ?_⟩
  intro x hx hxJ
  show f x + c • f' x = F x + c • F' x
  rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]

lemma smooth_zero : SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma rdV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

lemma eabV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b f g = EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [rdV_congr h h1 hg, rdV_congr h h2 hg]

lemma eabV_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n) :
    SmoothOnGV ε (EabV ε a b f) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  exact smooth_comb (rdSmoothV_of vector_right_derivative_extends n ε E f _ hf h1)
    (rdSmoothV_of vector_right_derivative_extends n ε E f _ hf h2) Complex.I

lemma eabV_comb {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun g => f g + c • f' g) g = EabV ε a b f g + c • EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [(rdLinV_of vector_right_derivative_extends n ε E f f' _ _ 0 c g hf hf' h1 h1 hg).2.2,
    (rdLinV_of vector_right_derivative_extends n ε E f f' _ _ 0 c g hf hf' h2 h2 hg).2.2]
  module

lemma hasDerivAt_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) (RdV X f 1) 0 := by
  obtain ⟨U, F, hU, hg, hF, hfF⟩ := hf 1 inUJ_one
  have hγ := hasDerivAt_mul_exp_smul_zero (1 : Matrix (Fin n) (Fin n) ℂ) X
  have hγ0 : (1 : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (1 * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F 1 (1 * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (1 * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, 1 * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    rw [Matrix.one_mul] at ht ⊢
    exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)
  rw [vector_right_derivative_extends n ε E f F U 1 X hU hg inUJ_one hF hfF hX]
  exact hcomp.congr_of_eventuallyEq hev

end Gen

section Rep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma rep_rdV (hσ : IsURepOn (UJset ε) σ) {u : H} (hu : SmoothOnGV ε (fun g => σ g u))
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    σ g (RdV X (fun x => σ x u) 1) = RdV X (fun x => σ x u) g := by
  rw [(rdVPair_of vector_right_derivative_extends n ε H H (σ g) _ X 1 hu hX inUJ_one).2,
    rdV_congr (f' := fun x => σ (g * x) u) (fun x hx => by
      rw [hσ.1.2 g hg x hx]; rfl) hX inUJ_one,
    vector_right_derivative_left_invariant n H (fun x => σ x u) X g 1, Matrix.mul_one]

lemma rep_eabV (hσ : IsURepOn (UJset ε) σ) {u : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (EabV ε a b (fun x => σ x u) 1) = EabV ε a b (fun x => σ x u) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add (f := _), map_smul, rep_rdV hσ hu h1 hg, rep_rdV hσ hu h2 hg]

lemma rep_inner (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (u v : H) : ⟪σ g u, σ g v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

lemma rep_skew (hσ : IsURepOn (UJset ε) σ) {u v : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (hv : SmoothOnGV ε (fun g => σ g v)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ⟪RdV X (fun x => σ x u) 1, v⟫_ℂ = -⟪u, RdV X (fun x => σ x v) 1⟫_ℂ := by
  have h := (hasDerivAt_rdV hu hX).inner ℂ (hasDerivAt_rdV hv hX)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) u,
      σ (NormedSpace.exp ((t : ℂ) • X)) v⟫_ℂ) = fun _ => ⟪u, v⟫_ℂ := by
    funext t
    exact rep_inner hσ (exp_indefinite_unitary_holds n ε X hX t) u v
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const _ _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply] at h0
  linear_combination h0

lemma rep_unit (hσ : IsURepOn (UJset ε) σ) {u v : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (hv : SmoothOnGV ε (fun g => σ g v)) (a b : Fin n) :
    ⟪EabV ε a b (fun x => σ x u) 1, v⟫_ℂ =
      (sgn ε a b : ℂ) * ⟪u, EabV ε b a (fun x => σ x v) 1⟫_ℂ := by
  obtain ⟨k1, k2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [inner_add_left, inner_smul_left, rep_skew hσ hu hv k1, rep_skew hσ hu hv k2]
  have hab := p0auxiliary_theta_single ε a b
  have hba := p0auxiliary_theta_single ε b a
  have hs : sgn ε b a = sgn ε a b := by unfold sgn; by_cases h : ε a = ε b <;> simp [h, eq_comm]
  rw [hs] at hba
  by_cases h : ε a = ε b
  · have h1 : sgn ε a b = 1 := by simp [sgn, h]
    rw [h1] at hab hba
    have c1 : cpart1 ε (Matrix.single b a 1) = -cpart1 ε (Matrix.single a b 1) := by
      unfold cpart1; rw [hab, hba]; simp only [Complex.ofReal_one, one_smul]; module
    have c2 : cpart2 ε (Matrix.single b a 1) = cpart2 ε (Matrix.single a b 1) := by
      unfold cpart2; rw [hab, hba]; simp only [Complex.ofReal_one, one_smul]; rw [add_comm]
    rw [c1, c2, p0auxiliary_rdV_neg, h1, inner_add_right, inner_smul_right, inner_neg_right]
    simp [Complex.conj_I]
  · have h1 : sgn ε a b = -1 := by simp [sgn, h]
    rw [h1] at hab hba
    have c1 : cpart1 ε (Matrix.single b a 1) = cpart1 ε (Matrix.single a b 1) := by
      unfold cpart1; rw [hab, hba]; push_cast; module
    have c2 : cpart2 ε (Matrix.single b a 1) = -cpart2 ε (Matrix.single a b 1) := by
      unfold cpart2; rw [hab, hba]; push_cast; module
    rw [c1, c2, p0auxiliary_rdV_neg, h1, inner_add_right, inner_smul_right, inner_neg_right]
    simp [Complex.conj_I]
    ring

def smoothVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {u | SmoothOnGV ε (fun g => σ g u)}
  zero_mem' := smooth_congr smooth_zero (fun g _ => map_zero _)
  add_mem' := fun hu hv => smooth_congr (smooth_comb hu hv 1) (fun g _ => by simp)
  smul_mem' := fun c _ hu => smooth_congr (smooth_comb smooth_zero hu c) (fun g _ => by simp)

def unitAct (hσ : IsURepOn (UJset ε) σ) (a b : Fin n) : Module.End ℂ (smoothVec ε σ) where
  toFun u := ⟨EabV ε a b (fun x => σ x u) 1,
    smooth_congr (eabV_smooth u.2 a b) (fun _ hg => rep_eabV hσ u.2 a b hg)⟩
  map_add' u v := by
    apply Subtype.ext
    have h := eabV_comb u.2 v.2 1 a b (inUJ_one (ε := ε))
    simp only [one_smul] at h
    simpa using h
  map_smul' c u := by
    apply Subtype.ext
    have h := eabV_comb smooth_zero u.2 c a b (inUJ_one (ε := ε))
    have h0 : EabV ε a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : H)) 1 = 0 := by
      simp [EabV, EcV, RdV]
    simp only [zero_add, h0] at h
    simpa using h

lemma unitAct_coe (hσ : IsURepOn (UJset ε) σ) (a b : Fin n) (u : smoothVec ε σ) :
    (unitAct hσ a b u : H) = EabV ε a b (fun x => σ x u) 1 := rfl

end Rep

theorem smoothVec_unitary_module : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∃ (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs), (∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g := by
  intro n ε H _ _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  refine ⟨smoothVec ε σ, unitAct hσ, fun _ => Iff.rfl, ?_, ?_, ?_, key⟩
  · intro a b c d
    ext u
    have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
      (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
      n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
    rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
    split_ifs <;> simp [unitAct_coe]
  · intro a b x y
    exact rep_unit hσ x.2 y.2 a b
  · intro X hX u
    have h := ecSumV_of (rdLinV_of vector_right_derivative_extends) n ε H (fun g => σ g u) X 1 u.2 inUJ_one
    obtain ⟨c1, c2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    have h0 : RdV (0 : Matrix (Fin n) (Fin n) ℂ) (fun g => σ g u) 1 = 0 := by simp [RdV]
    unfold EcV at h
    rw [c1, c2, h0, smul_zero, add_zero] at h
    have e : ((∑ a, ∑ b, X a b • unitAct hσ a b u : smoothVec ε σ) : H) =
        RdV X (fun g => σ g u) 1 := by
      rw [h]
      simp [unitAct_coe]
    rw [e]
    exact hasDerivAt_rdV u.2 hX

end GlobalTheory.SmoothVecMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqrtNsqLeOfAbsLe
section
open Formalism.REAL Finset
open scoped InnerProductSpace

namespace GlobalTheory.AlgStep

theorem sqrt_nsq_eq_norm {n : ℕ} (u : Fin n → ℝ) :
    Real.sqrt (nsq u) = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [nsq, dot, sq]

theorem sqrt_nsq_add_le {n : ℕ} (u v : Fin n → ℝ) :
    Real.sqrt (nsq (u + v)) ≤ Real.sqrt (nsq u) + Real.sqrt (nsq v) := by
  simp only [sqrt_nsq_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

theorem nsq_nonneg' {n : ℕ} (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg (u a)

theorem sum_range_sub_sq (c : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (c - (i : ℝ)) * (c - (i : ℝ)) =
      n * c ^ 2 - c * n * (n - 1) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem nsq_rho_le {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε + rhoN ε) ≤ (n : ℝ) ^ 3 / 12 := by
  have h : nsq (rhoC ε + rhoN ε) =
      ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)))]
    unfold nsq dot
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, half_sum_roots_standard n ε a]
  rw [h, sum_range_sub_sq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem casK_form_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (M : ℝ) (hfin : FiniteDimensional ℂ S)
    (hr : KRel ε F) (hu : KUnit ε F) (hS : KStable ε F S)
    (hw : ∀ (μ : Fin n → ℝ), ∀ x ∈ S, x ≠ 0 → KHighest ε F μ x → ckv ε μ ≤ M) :
    ∀ y ∈ S, (⟪y, CasK ε F y⟫_ℂ).re ≤ M * ‖y‖ ^ 2 := by
  intro y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := kDecomp V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => kCasSpan V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2

theorem sqrt_nsq_le_of_abs_le {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (h : ∀ a, |lam a| ≤ b ^ 2) :
    Real.sqrt (nsq lam) ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 := by
  have h1 : nsq lam ≤ (n : ℝ) * (b ^ 2) ^ 2 := by
    have : ∑ a : Fin n, lam a * lam a ≤ ∑ _a : Fin n, (b ^ 2) ^ 2 := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    simpa [nsq, dot] using this
  rw [← Real.sqrt_eq_rpow]
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (sq_nonneg b)]

end GlobalTheory.AlgStep

namespace GlobalTheory

open GlobalTheory.AlgStep

theorem algebraic_step_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (b : ℝ),
    GlRel E → IsUnitary ε E → KindA ε E lam u → (∀ a, |lam a| ≤ b ^ 2) →
    ∀ (j : ℕ), ∀ x ∈ pfil ε E u j,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 * ‖x‖ ^ 2 := by
  intro V _ _ n ε E lam u b hg hu hk hb j x hx
  obtain ⟨hhi, hcas, hfin⟩ := hk
  obtain ⟨-, -, hst, -, hcyc, -, hfd⟩ := pfilFacts V n ε E u hg
  set L := Real.sqrt (nsq lam) with hL
  set A := Real.sqrt (nsq (rhoN ε)) + Real.sqrt 2 * j with hA
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by positivity
  have hK := casK_form_le V n ε E (pfil ε E u j) ((L + A) ^ 2) (hfd hfin j) (glRel_kRel ε E hg)
    (isUnitary_kUnit ε E hu) (hst j) (by
      intro μ y hy hy0 hyh
      have h1 := GlobalTheory.KTypeSteps.ktypes_within_steps V n ε E (LamOf ε lam) u hg hu hhi hfin j μ y hy hy0 hyh
      have h2 : μ + rhoC ε = (lam + rhoN ε) + (μ - LamOf ε lam) := by
        unfold LamOf; ring
      have h3 : Real.sqrt (nsq (μ + rhoC ε)) ≤ L + A := by
        rw [h2]
        have := sqrt_nsq_add_le (lam + rhoN ε) (μ - LamOf ε lam)
        have := sqrt_nsq_add_le lam (rhoN ε)
        linarith
      have h4 := (Real.sqrt_le_iff.mp h3).2
      have h5 := nsq_nonneg' (rhoC ε)
      unfold ckv
      linarith) x hx
  have hC : Cas E x = ((cvalR ε lam : ℝ) : ℂ) • x := casOnCyc V n E _ u hg hcas x (hcyc j hx)
  have hS := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hu)
  have hxx : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [Complex.ofReal_re, LinearMap.sub_apply, two_smul, LinearMap.add_apply, hC, inner_sub_right,
    inner_add_right, inner_smul_right, hxx, ← Complex.ofReal_mul, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re] at hS
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have har := rhoN_norm_le_and_casimir_arith.2 L A n hL0 hA0 hn
  have hr := rhoN_norm_le_and_casimir_arith.1 n ε
  have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
  have hLb := sqrt_nsq_le_of_abs_le lam b hb
  have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hj : Real.sqrt 2 * j ≤ 3 / 2 * j := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg j)
  have hle : L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
    linarith
  have hsq : (L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hL2 : L ^ 2 = nsq lam := Real.sq_sqrt (nsq_nonneg' lam)
  have hrho := nsq_rho_le ε
  have hc : 2 * (L + A) ^ 2 - cvalR ε lam ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 := by
    unfold cvalR
    linarith
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
  rw [hS]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformiserProductTypePrimes
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.TypePrimeProduct

theorem natPrime_not_mem_of_other (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hO : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := by
    have := hZ.map (Int.castRingHom (𝓞 F))
    simpa using this
  obtain ⟨a, b, hab⟩ := hO
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem isUnit_natCast_of_not_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∉ v.asIdeal) :
    IsUnit ((q : ℕ) : v.adicCompletionIntegers F) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hq] at h
  simpa using h

theorem main_two (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal)
    (hm : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p : ℕ) : v.adicCompletionIntegers F)}) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p * q : ℕ) : v.adicCompletionIntegers F)} ∧
      ((p * q : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hqv := natPrime_not_mem_of_other F v hp hq hpq hpv
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit (isUnit_natCast_of_not_mem F v q hqv)]
  · rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hpv

end GlobalTheory.St.G.TypePrimeProduct


open GlobalTheory.St.G.TypePrimeProduct in
theorem GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  intro F _ _ gp hgp hne i v hv hm
  fin_cases i
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 0) (hgp 1) hne hv hm
    exact ⟨h1, h2, gp 1, (hgp 1).pos, rfl⟩
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 1) (hgp 0) hne.symm hv hm
    rw [mul_comm (gp 0)]
    exact ⟨h1, h2, gp 0, (hgp 0).pos, rfl⟩
end

