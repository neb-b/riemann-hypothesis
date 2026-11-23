module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CompactLoweringSpanDiagStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemTensorFockOfCoeffs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysApplySingle
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceEqTraceRestrictOfRangeLe

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DiracSquareMemLayer
section
noncomputable section

open MvPolynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def entVar (g : Matrix (Fin n) (Fin n) ℂ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

abbrev EntIdx (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

theorem totalDegree_bind_le_of_linear {ι : Type*} (f : ι → MvPolynomial ι ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (Q : MvPolynomial ι ℂ) : (bind₁ f Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m i) (hf i)

def trF (g : Matrix (Fin n) (Fin n) ℂ) : EntIdx n → MvPolynomial (EntIdx n) ℂ :=
  Sum.elim (fun x => ∑ l, C (g x.1 l) * X (Sum.inl (l, x.2)))
    (fun x => ∑ l, C (star (g x.1 l)) * X (Sum.inr (l, x.2)))

theorem trF_totalDegree (g : Matrix (Fin n) (Fin n) ℂ) (i : EntIdx n) : (trF g i).totalDegree ≤ 1 := by
  classical
  rcases i with x | x <;>
  · simp only [trF, Sum.elim_inl, Sum.elim_inr]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

theorem eval_trF (g h : Matrix (Fin n) (Fin n) ℂ) (i : EntIdx n) :
    eval (entVar h) (trF g i) = entVar (g * h) i := by
  rcases i with x | x
  · simp [trF, entVar, Matrix.mul_apply]
  · simp [trF, entVar, Matrix.mul_apply, star_sum]

theorem eval_mul_eq_bind₁ (g h : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (EntIdx n) ℂ) :
    eval (entVar (g * h)) P = eval (entVar h) (bind₁ (trF g) P) := by
  have := eval₂Hom_bind₁ (RingHom.id ℂ) (entVar h) (trF g) P
  simp only [coe_eval₂Hom] at this
  rw [show eval (entVar h) (bind₁ (trF g) P) = eval₂ (RingHom.id ℂ) (entVar h) (bind₁ (trF g) P) from rfl, this]
  show eval₂ (RingHom.id ℂ) _ P = eval₂ (RingHom.id ℂ) _ P
  congr 1
  funext i
  exact (eval_trF g h i).symm

def wtM (m : EntIdx n →₀ ℕ) : Fin n → ℝ := fun a =>
  ∑ j, (((m (Sum.inr (a, j)) : ℕ) : ℝ) - ((m (Sum.inl (a, j)) : ℕ) : ℝ))

def dTor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem eval_monomial_tor (θ : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℂ) (m : EntIdx n →₀ ℕ) :
    eval (entVar (star (dTor θ) * h)) (monomial m 1) =
      Complex.exp (((∑ a, wtM m a * θ a : ℝ) : ℂ) * Complex.I) * eval (entVar h) (monomial m 1) := by
  classical
  set s : EntIdx n → ℝ := Sum.elim (fun x => -θ x.1) (fun x => θ x.1) with hs
  have hst : ∀ t : ℝ, star (Complex.exp ((t : ℂ) * Complex.I)) = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [← starRingEnd_apply, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  have hent : ∀ i, entVar (star (dTor θ) * h) i = Complex.exp ((s i : ℂ) * Complex.I) * entVar h i := by
    intro i
    rcases i with x | x
    · simp only [entVar, Sum.elim_inl, hs, dTor, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Pi.star_apply]
      rw [hst]
    · simp only [entVar, Sum.elim_inr, hs, dTor, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Pi.star_apply, star_mul', star_star]
  simp only [eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [hent, mul_pow, Finset.prod_mul_distrib]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [wtM, hs, Sum.elim_inl, Sum.elim_inr]
  push_cast
  rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ProdModeCharExp
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_diagE (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) =
      E a b (tcoef ((fockBasis n).coord s) y) +
        tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [diagE, sgE_cpT, eT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
      LinearMap.id_apply, map_add, tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, map_smul]
  | add y y' hy hy' =>
    rw [map_add (f := _), map_add (f := _), hy, hy', map_add (f := _), map_add (f := _), map_add (f := _)]
    abel

theorem tco_diagE_wt (E : Fin n → Fin n → Module.End ℂ N) (a : Fin n)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a y) =
      E a a (tcoef ((fockBasis n).coord s) y) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
  rw [tco_diagE, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a a) y]
  congr 1
  rw [Finset.sum_eq_single s]
  · simp [fockBasis_wt]
  · intro b _ hb
    simp [fockBasis_wt, Finsupp.single_apply, hb]
  · simp

end T

theorem modeChar_exp (θ : Fin n → ℝ) (x : Fin n × Fin n) :
    modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, modeWt ε x a * θ a : ℝ) : ℂ) * Complex.I) := by
  unfold modeChar modeWt
  by_cases h : IsPhys ε x
  · rw [if_pos h, if_pos (show ε x.1 = true ∧ ε x.2 = false from h), Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [root, Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [if_neg h, if_neg (show ¬(ε x.1 = true ∧ ε x.2 = false) from h)]
    simp

theorem prod_modeChar_exp (θ : Fin n → ℝ) (s : Finset (Fin (n * n))) :
    ∏ m ∈ s, modeChar ε (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) (finProdFinEquiv.symm m) =
      Complex.exp (((∑ a, fockWt ε s a * θ a : ℝ) : ℂ) * Complex.I) := by
  simp only [modeChar_exp]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  simp only [fockWt, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem diag_mem_Kset' (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε :=
  bwt_diag_mem_Kset ε θ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem wK_diag_wt (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)} (hy : ∀ a, diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y)
    (θ : Fin n → ℝ) :
    wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y := by
  apply coordH_injective
  funext s
  rw [map_smul, Pi.smul_apply, coordH_apply, coordH_apply, tco_wK]
  rw [Finset.sum_eq_single s]
  · rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, prod_modeChar_exp]
    have hts : ∀ a, E a a (tcoef ((fockBasis n).coord s) y) =
        (((μ - fockWt ε s) a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) y := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hy a)
      rw [tco_diagE_wt, map_smul] at h
      rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hw := (isWtOn_iff hσ hD (tcoef ((fockBasis n).coord s) y) (μ - fockWt ε s)).2 hts θ
      (bwt_diag_mem_Kset ε θ)
    rw [Submodule.coe_smul]
    change _ • σ _ _ = _
    rw [hw, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  · intro b _ hb
    rw [ff_diag, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_neg hb, smul_zero, zero_smul]
  · simp

theorem bwtDiag_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) : inK ε (bwtDiag θ) := by
  refine ⟨bwtDiag_inG ε θ, ?_⟩
  unfold bwtDiag Jm
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  ring

theorem wK_congr (hD : IsDerivedOn ε σ D E) {k k' : Matrix (Fin n) (Fin n) ℂ} (h : k = k')
    (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) (y : TensorProduct ℂ D (Fock n)) :
    wK hD hk y = wK hD hk' y := by
  subst h
  rfl

theorem diagE_wt_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {μ : Fin n → ℝ}
    {y : TensorProduct ℂ D (Fock n)}
    (hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) y = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y)
    (a : Fin n) : diagE ε (eT E) cpT cmT a a y = ((μ a : ℝ) : ℂ) • y := by
  set θ : Fin n → ℝ := Pi.single a 1 with hθ
  have hX := bwtDiag_inK ε θ
  have hcurve : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) =
      Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I) • coordH y := by
    intro t
    rw [wK_congr hD (bwt_exp θ t) _ (diag_mem_Kset' ε (fun b => t * θ b)), hy, map_smul]
    congr 4
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)]
    simp [hθ]
    ring
  have hder1 : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have he : HasDerivAt (fun t : ℝ => Complex.exp (((t * μ a : ℝ) : ℂ) * Complex.I))
      (((μ a : ℝ) : ℂ) * Complex.I) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((t * μ a : ℝ) : ℂ)) ((1 * μ a : ℝ) : ℂ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const (μ a)).ofReal_comp
    have h2 := (h1.mul_const Complex.I).cexp
    convert h2 using 1
    simp
  have hder2 := he.smul_const (coordH y)
  rw [funext hcurve] at hder1
  have heq := hder1.unique hder2
  have h2 : actM (diagE ε (eT E) cpT cmT) (bwtDiag θ) y = (((μ a : ℝ) : ℂ) * Complex.I) • y :=
    coordH_injective (by rw [heq, map_smul])
  rw [bwtDiag, bwt_actM_diag, LinearMap.sum_apply,
    Finset.sum_eq_single a (fun b _ hb => by simp [hθ, Pi.single_apply, hb]) (by simp)] at h2
  simp only [hθ, Pi.single_eq_same, Complex.ofReal_one, one_mul, LinearMap.smul_apply] at h2
  have h3 := congrArg (fun v => (-Complex.I) • v) h2
  simp only [smul_smul] at h3
  have hI : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hI' : -Complex.I * (((μ a : ℝ) : ℂ) * Complex.I) = ((μ a : ℝ) : ℂ) := by
    linear_combination (-((μ a : ℝ) : ℂ)) * Complex.I_mul_I
  rw [hI, one_smul, hI'] at h3
  exact h3

section Orth

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem kLow_wt_eq_lowWt {A : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))}
    (hK : Formalism.REAL.KRel ε A)
    (hA : ∀ (a : Fin n) (y y' : TensorProduct ℂ M (Fock n)), tform (A a a y) y' = tform y (A a a y'))
    {γ : Fin n → ℝ} {z : TensorProduct ℂ M (Fock n)} (hz : IsKHWVec ε A γ z)
    {y : TensorProduct ℂ M (Fock n)} (hy : y ∈ kLowSpan ε A z) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, A a a y = ((μ a : ℝ) : ℂ) • y) :
    ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ μ = lowWt γ l := by
  by_contra hne
  push Not at hne
  have horth : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → tform y (lowWord A z l) = 0 := by
    intro l hl
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ lowWt γ l a := by
      by_contra h
      push Not at h
      exact hne l hl (funext h)
    have h1 := hA a y (lowWord A z l)
    rw [hμ a, lowerWord_weight hK hz.1 l hl a, tensorForm_smul_left, tform_smul_right, Complex.star_def,
      Complex.conj_ofReal] at h1
    have h2 : (((μ a : ℝ) : ℂ) - ((lowWt γ l a : ℝ) : ℂ)) * tform y (lowWord A z l) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h) ha
    · exact h
  have hall : ∀ w ∈ kLowSpan ε A z, tform y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact horth l hl
    | zero => simp [tform]
    | add x x' _ _ hx hx' => rw [tform_add_right, hx, hx', add_zero]
    | smul c x _ hx => rw [tform_smul_right, hx, mul_zero]
  have := tform_self_re_pos hy0
  rw [hall y hy] at this
  simp at this

end Orth

theorem cdom_lowWt (γ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) → Formalism.MainNotions.S.CDom ε (lowWt γ l) γ := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [lowWt]⟩
  | cons p l ih =>
    intro hl
    obtain ⟨c, hc, heq⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨c0, d0⟩ := p
    have hp : IsKLow ε (c0, d0) := hl _ (List.mem_cons_self ..)
    refine ⟨fun a b => c a b + if a = d0 ∧ b = c0 then 1 else 0, ?_, ?_⟩
    · intro a b h
      by_cases h' : a = d0 ∧ b = c0
      · obtain ⟨rfl, rfl⟩ := h'
        exact ⟨hp.1, hp.2.symm⟩
      · dsimp only at h
        rw [if_neg h', add_zero] at h
        exact hc a b h
    · have hs : (∑ a, ∑ b, (((if a = d0 ∧ b = c0 then 1 else 0 : ℕ)) : ℝ) • Formalism.REAL.root a b) =
          Formalism.REAL.root d0 c0 := by
        rw [Finset.sum_eq_single d0 (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [ha]) (by simp),
          Finset.sum_eq_single c0 (fun b _ hb => by simp [hb]) (by simp)]
        simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, hs, ← heq, lowWt]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, root, Formalism.REAL.root]
      ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TensFockInfPhysSub
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Supp

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_physSub_zero {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ physicalSubspace ε) {s : Finset (Fin (n * n))}
    {m : Fin (n * n)} (hm : m ∈ s) (hnp : ¬IsPhys ε (finProdFinEquiv.symm m)) :
    tcoef ((fockBasis n).coord s) y = 0 := by
  set x := finProdFinEquiv.symm m with hxdef
  have h0 : cmT (N := N) x.1 x.2 y = 0 := (mem_physicalSubspace_iff ε y).1 hy x.1 x.2 hnp
  have h1 : tcoef ((fockBasis n).coord s) (cpT (N := N) x.1 x.2 (cmT x.1 x.2 y)) = 0 := by
    rw [h0, map_zero, map_zero]
  change tcoef ((fockBasis n).coord s) (LinearMap.lTensor N (cpFock x.1 x.2)
    (LinearMap.lTensor N (cmFock x.1 x.2) y)) = 0 at h1
  have hxs : finProdFinEquiv x ∈ s := by
    rw [hxdef, Equiv.apply_symm_apply]
    exact hm
  rwa [tcoef_lTensor, tcoef_lTensor, LinearMap.comp_assoc, gc_coord_num, ite_eq_left hxs, one_smul] at h1

theorem tensFock_inf_physSub (L : Submodule ℂ N) :
    tensFock (n := n) L ⊓ physicalSubspace ε = LinearMap.range (TensorProduct.map L.subtype (physFock ε).subtype) := by
  apply le_antisymm
  · rintro y ⟨hyT, hyP⟩
    have hmem : ∀ s, tcoef ((fockBasis n).coord s) y ∈ L := fun s => tcoef_mem hyT _
    refine ⟨∑ S : LfIdx ε, (⟨tcoef ((fockBasis n).coord S.1) y, hmem S.1⟩ : L) ⊗ₜ
      (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [TensorProduct.map_tmul, Submodule.coe_subtype]
    symm
    calc y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := tcoef_expand y
      _ = ∑ s ∈ univ.filter (fun s => s ⊆ lfPhysModes ε),
          tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with h
        · rfl
        · obtain ⟨m, hm, hmp⟩ := Finset.not_subset.1 h
          have hnp : ¬IsPhys ε (finProdFinEquiv.symm m) := by
            simpa [lfPhysModes, IsPhys] using hmp
          rw [tco_physSub_zero hyP hm hnp, TensorProduct.zero_tmul]
      _ = ∑ S : LfIdx ε, tcoef ((fockBasis n).coord S.1) y ⊗ₜ fockBasis n S.1 :=
        Finset.sum_subtype _ (fun s => by simp) _
  · rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨TensorProduct.map LinearMap.id (physFock ε).subtype x, ?_⟩
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      rfl
    · show _ ∈ physicalSubspace ε
      rw [mem_physicalSubspace_iff]
      intro j b hjb
      induction x using TensorProduct.inductionOn with
      | tmul l f =>
        have hf := f.2
        simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hf
        simp only [TensorProduct.map_tmul, cmT, LinearMap.id_apply, Submodule.coe_subtype, hf j b hjb,
          TensorProduct.tmul_zero]
      | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]

end Supp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem str_tensFock_physSub (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {L : Submodule ℂ D} [FiniteDimensional ℂ L] (hL : ∀ x ∈ L, sigD hD hk x ∈ L)
    (hY0 : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace ε, (gradT ∘ₗ wK hD hk) y ∈ tensFock L ⊓ physicalSubspace ε) :
    LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD hk).restrict hY0) =
      LinearMap.trace ℂ L ((sigD hD hk).restrict hL) * physDet ε k := by
  set Φ := TensorProduct.map L.subtype (physFock ε).subtype with hΦ
  have hinj : Function.Injective Φ :=
    TensorProduct.map_injective_of_flat_flat _ _ L.injective_subtype (physFock ε).injective_subtype
  let e : TensorProduct ℂ L (physFock ε) ≃ₗ[ℂ] ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε) :=
    (LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ (tensFock_inf_physSub L).symm)
  have he : ∀ x, ((e x : ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)) : TensorProduct ℂ D (Fock n)) = Φ x :=
    fun x => rfl
  set sL := (sigD hD hk).restrict hL
  set fP := (CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)
  have hsq : ∀ x, (gradT ∘ₗ wK hD hk) (Φ x) = Φ (TensorProduct.map sL fP x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l f => rfl
    | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]
  have hconj : (gradT ∘ₗ wK hD hk).restrict hY0 = e.conj (TensorProduct.map sL fP) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [LinearEquiv.conj_apply_apply, he, LinearMap.restrict_apply]
    show (gradT ∘ₗ wK hD hk) (y : TensorProduct ℂ D (Fock n)) = _
    rw [← hsq, ← he, LinearEquiv.apply_symm_apply]
  have : FiniteDimensional ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', ← strPhys_eq_trace, strPhys_eq_physDet]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

