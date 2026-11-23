module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) :
    actM E Z x ∈ S := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num
    have h2 : Z a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h2).resolve_right hne
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : ε a = ε b
  · exact S.smul_mem _ (hS a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact S.zero_mem

theorem actM_pow_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ S := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_of_isKStableSub_inK hS hZ ih

theorem exists_norm_actM_pow_le_of_isKStableSub {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    (hSf : FiniteDimensional ℂ S) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ S := hSf
  let g : S →ₗ[ℂ] S := (actM E Z).restrict (fun x hx => actM_mem_of_isKStableSub_inK hS hZ hx)
  let gL : S →L[ℂ] S := LinearMap.toContinuousLinearMap g
  refine ⟨‖gL‖, norm_nonneg _, ?_⟩
  have key : ∀ y : S, ‖actM E Z (y : D)‖ ≤ ‖gL‖ * ‖y‖ := fun y => gL.le_opNorm y
  intro x hx m
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := actM_pow_mem_of_isKStableSub_inK hS hZ hx m
    have h1 := key ⟨_, hm⟩
    rw [pow_succ', Module.End.mul_apply]
    calc ‖actM E Z (((actM E Z) ^ m) x)‖ ≤ ‖gL‖ * ‖((actM E Z) ^ m) x‖ := h1
      _ ≤ ‖gL‖ * (‖gL‖ ^ m * ‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖gL‖ ^ (m + 1) * ‖x‖ := by ring

theorem kStable_of_isKStableSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hk : IsKStableSub ε E S) :
    ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v := by
  intro g hg v hv
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hk hS hZ
  have hs : Summable fun m : ℕ => (C ^ m * ‖v‖) * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    simp only [sub_zero, abs_one, one_pow, mul_one]
    exact ((Real.summable_pow_div_factorial C).mul_right ‖v‖).congr fun m => by ring
  have h := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply, Complex.ofReal_one, one_smul] at h
  haveI : FiniteDimensional ℂ S := hS
  have hT : IsClosed ((S.map D.subtype : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : σ (NormedSpace.exp Z) (v : H) ∈ S.map D.subtype := by
    refine hT.mem_of_tendsto h.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ ⟨_, actM_pow_mem_of_isKStableSub_inK hk hZ hv m, rfl⟩
  obtain ⟨w, hwS, hw⟩ := hmem
  exact ⟨w, hwS, hw⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def bwtDiag (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem bwtDiag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) : inG ε (bwtDiag θ) := by
  show (bwtDiag θ)ᴴ * Jm ε + Jm ε * bwtDiag θ = 0
  rw [bwtDiag, Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext i
  by_cases hε : ε i = true <;> simp [hε, Complex.conj_I] <;> ring_nf

theorem bwt_exp (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • bwtDiag θ) =
      Matrix.diagonal (fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I)) := by
  have h : (t : ℂ) • bwtDiag θ = Matrix.diagonal (fun a => (t : ℂ) * ((θ a : ℂ) * Complex.I)) := by
    rw [bwtDiag]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  rw [h, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.exp_def]
  dsimp only
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

theorem bwt_diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
    simp
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem bwt_actM_diag (E : Fin n → Fin n → Module.End ℂ M) (d : Fin n → ℂ) :
    actM E (Matrix.diagonal d) = ∑ a, d a • E a a := by
  simp [actM, Matrix.diagonal_apply, ite_smul]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem bwt_actM_apply (θ : Fin n → ℝ) (v : D) :
    ((actM E (bwtDiag θ) v : D) : H) = ∑ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) := by
  rw [bwtDiag, bwt_actM_diag]
  simp

private theorem exp_smul_bwtDiag_mem_UJset (ε : Fin n → Bool) (θ : Fin n → ℝ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • bwtDiag θ) ∈ UJset ε := by
  have hK := bwt_diag_mem_Kset ε (fun a => s * θ a)
  obtain ⟨hu, hc⟩ := hK
  rw [bwt_exp]
  have hu' := Matrix.mem_unitaryGroup_iff'.1 hu
  have hJJ : Jm ε = Formalism.REAL.Jm ε := rfl
  show inUJ ε _
  unfold inUJ
  rw [hJJ, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu',
    Matrix.one_mul]

private theorem apply_one_eq_exp_smul_of_hasDerivAt_smul {F : ℝ → H} {c : ℂ} (hF : ∀ s, HasDerivAt F (c • F s) s) :
    F 1 = Complex.exp c • F 0 := by
  have hG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • F t) 0 s := by
    intro s
    have h1 := (((hasDerivAt_id' s).ofReal_comp).mul_const (-c)).cexp
    refine (h1.smul (hF s)).congr_deriv ?_
    rw [smul_smul, ← add_smul]
    simp
  have hconst := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) 1 0
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Complex.exp_add]
  simp

private theorem hasDerivAt_of_shift_of_hasDerivAt_zero {G : ℝ → H} {L : H} (T : ℝ → (H →L[ℂ] H))
    (hG0 : HasDerivAt G L 0) (hshift : ∀ s t, G (s + t) = T s (G t)) (s : ℝ) :
    HasDerivAt G (T s L) s := by
  have h1 := ((T s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG0
  have h2 : HasDerivAt (fun t => G (s + t)) (T s L) 0 := by
    convert h1 using 1 <;> first | rfl | (funext t; exact hshift s t)
  have h3 : HasDerivAt (fun t => G (s + t)) (T s L) (s - s) := by rwa [sub_self]
  have h4 := HasDerivAt.scomp (h := fun x : ℝ => x - s) s h3 ((hasDerivAt_id' s).sub_const s)
  convert h4 using 1 <;> first | (funext x; simp) | simp

theorem isWtOn_iff (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (v : D) (μ : Fin n → ℝ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ (v : H) ↔ ∀ a, E a a v = ((μ a : ℝ) : ℂ) • v := by
  constructor
  · intro hw a
    have hder := hD.deriv _ (bwtDiag_inG ε (Pi.single a 1)) v
    have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag (Pi.single a 1))) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have h := hw (fun b => t * (Pi.single a (1 : ℝ) : Fin n → ℝ) b) (bwt_diag_mem_Kset ε _)
      rw [bwt_exp, h]
      congr 2
      simp [Pi.single_apply] <;> ring
    rw [hfun, bwt_actM_apply] at hder
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := ((((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const
        ((μ a : ℂ) * Complex.I)).cexp).smul_const (v : H)
      convert this using 1
      simp
    have heq := hder.unique hexp
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at heq
    simp only [Pi.single_eq_same, Complex.ofReal_one, one_mul] at heq
    apply Subtype.ext
    have h2 : Complex.I • ((E a a v : D) : H) = Complex.I • (((μ a : ℝ) : ℂ) • (v : H)) := by
      rw [heq, smul_smul, mul_comm]
    exact smul_right_injective H Complex.I_ne_zero h2
  · intro hE θ _
    have hlam : ((actM E (bwtDiag θ) v : D) : H) =
        (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H) := by
      rw [bwt_actM_apply]
      have hterm : ∀ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) =
          (((θ a : ℂ) * Complex.I) * (μ a : ℂ)) • (v : H) := by
        intro a
        rw [hE a, Submodule.coe_smul, smul_smul]
      rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h0 := hD.deriv _ (bwtDiag_inG ε θ) v
    rw [hlam] at h0
    have hshift : ∀ s t : ℝ, σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ)) (v : H) =
        σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H)) := by
      intro s t
      have hmul : NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ) =
          NormedSpace.exp ((s : ℂ) • bwtDiag θ) * NormedSpace.exp ((t : ℂ) • bwtDiag θ) := by
        rw [Complex.ofReal_add, add_smul]
        exact Matrix.exp_add_of_commute _ _ (((Commute.refl (bwtDiag θ)).smul_left _).smul_right _)
      rw [hmul, hσ.1.2 _ (exp_smul_bwtDiag_mem_UJset ε θ s) _ (exp_smul_bwtDiag_mem_UJset ε θ t)]
      rfl
    have hF : ∀ s : ℝ, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) •
          σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (v : H)) s := by
      intro s
      have := hasDerivAt_of_shift_of_hasDerivAt_zero (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ))) h0 hshift s
      rwa [map_smul] at this
    have hode := apply_one_eq_exp_smul_of_hasDerivAt_smul hF
    have e1 : NormedSpace.exp (((1 : ℝ) : ℂ) • bwtDiag θ) =
        Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
      rw [bwt_exp]
      simp
    have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • bwtDiag θ) = 1 := by simp
    rw [e1, e0, hσ.1.1] at hode
    simpa using hode

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rregRep_umat_inj (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem rregRep_rreg_umat (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  rw [rreg, dite_eq_left h]
  exact congrArg (rregG ε) (rregRep_umat_inj ε h.choose_spec)

theorem rregRep_rregG_apply (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y)
      (measurePreserving_mul_right ε y) f := by
  rw [rregG, dite_eq_left (measurePreserving_mul_right ε y)]
  rfl

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ε i <;> simp [h]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc] at hg'
  simp only [Matrix.mul_assoc]
  rw [hg', Jm_mul_selfDiscreteSeriesExistence]

private theorem mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have hl := Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg
  first
  | exact mul_eq_one_comm.mp hl
  | (rw [← Matrix.inv_eq_left_inv hl]
     exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl))

theorem rregRep_range (ε : Fin n → Bool) :
    Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) = UJset ε := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hg
    exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε hg,
      Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg⟩, hg⟩, rfl⟩

theorem rregRep_mem (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have h2 : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := by
    rw [rregRep_range ε]
    exact hg
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩

theorem rregRep_one (ε : Fin n → Bool) : rreg ε 1 = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) := rfl
  rw [h1, rregRep_rreg_umat]
  ext1 f
  rw [rregRep_rregG_apply, ContinuousLinearMap.one_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε 1)] with x hx
  rw [hx]
  simp

theorem rregRep_mul (ε : Fin n → Bool) (a b : Formalism.REAL.UJ ε) :
    rregG ε (a * b) = (rregG ε a).comp (rregG ε b) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, rregRep_rregG_apply, rregRep_rregG_apply,
    rregRep_rregG_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε (a * b)),
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * b)
        (measurePreserving_mul_right ε b) f) (measurePreserving_mul_right ε a),
    (measurePreserving_mul_right ε a).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε b))] with x h1 h2 h3
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3, mul_assoc]

theorem rregRep_cont (ε : Fin n → Bool) (v : L2 ε) :
    Continuous (fun y : Formalism.REAL.UJ ε => rregG ε y v) := by
  haveI : SMulInvariantMeasure (Formalism.REAL.UJ ε)ᵐᵒᵖ (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) := by
    refine ⟨fun c s hs => ?_⟩
    first
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs.nullMeasurableSet
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by first | simp | exact ENNReal.ofNat_ne_top⟩
  have he : (fun y : Formalism.REAL.UJ ε => rregG ε y v) =
      fun y => (DomMulAct.mk (MulOpposite.op y)) • v := by
    funext y
    rw [rregRep_rregG_apply]
    rfl
  rw [he]
  have hm : Continuous (fun y : Formalism.REAL.UJ ε => DomMulAct.mk (MulOpposite.op y)) := by
    first
    | exact DomMulAct.continuous_mk.comp MulOpposite.continuous_op
    | exact DomMulAct.mkHomeomorph.continuous.comp MulOpposite.continuous_op
    | fun_prop
  haveI : OpensMeasurableSpace (Formalism.REAL.UJ ε)ᵐᵒᵖ :=
    ⟨MeasurableSpace.generateFrom_le fun s hs =>
      (IsOpen.preimage MulOpposite.continuous_op hs).measurableSet⟩
  exact hm.smul continuous_const

theorem rreg_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (rreg ε) := by
  unfold IsURepOn
  refine ⟨⟨rregRep_one ε, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := rregRep_mem ε ha
    obtain ⟨yb, rfl⟩ := rregRep_mem ε hb
    have hab : Formalism.MainNotions.S.umat ya * Formalism.MainNotions.S.umat yb = Formalism.MainNotions.S.umat (ya * yb) := rfl
    rw [hab, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_mul]
  · intro g hg v
    obtain ⟨y, rfl⟩ := rregRep_mem ε hg
    rw [rregRep_rreg_umat, rregRep_rregG_apply]
    exact Lp.norm_compMeasurePreserving v _
  · intro v
    obtain ⟨φ, hφc, hφ⟩ : ∃ φ : UJset ε → Formalism.REAL.UJ ε, Continuous φ ∧
        ∀ g : UJset ε, Formalism.MainNotions.S.umat (φ g) = g :=
      ⟨fun g => ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ),
          Formalism.REAL.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε,
          mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε g.2, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε g.2⟩, g.2⟩,
        by
          apply Continuous.subtype_mk
          rw [Units.continuous_iff]
          constructor
          · exact continuous_subtype_val
          · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul
              continuous_const,
        fun g => rfl⟩
    have he : ∀ g : UJset ε, rreg ε (g : Matrix (Fin n) (Fin n) ℂ) v = rregG ε (φ g) v := by
      intro g
      rw [← hφ g, rregRep_rreg_umat]
    rw [continuousOn_iff_continuous_restrict]
    convert (rregRep_cont ε v).comp hφc using 1
    funext g
    exact he g

end ReciprocityTheory.ChartRestriction.DS
end
end

