module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsPairs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0002
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

theorem contDiff_of_differentiable_fd {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {F : W → ℂ} (hF : Differentiable ℂ F) (k : ℕ) : ContDiff ℂ k F := by
  classical
  set e := Module.finrank ℂ W
  let L : W ≃L[ℂ] (Fin e → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [e])
  have hg : Differentiable ℂ (F ∘ L.symm) := hF.comp L.symm.differentiable
  have ha := ReciprocityTheory.AnForm.Osgood.osgood e Set.univ (F ∘ L.symm) isOpen_univ hg.differentiableOn
  have hc : ContDiff ℂ k (F ∘ L.symm) :=
    contDiff_iff_contDiffAt.2 fun x => (ha x (Set.mem_univ x)).contDiffAt
  have hF' : F = (F ∘ L.symm) ∘ L := by
    funext w
    simp
  rw [hF']
  exact hc.comp L.contDiff

theorem polyDeriv_sum {σ W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (s : Finset ι) (c : ι → ℂ) (F : ι → W → ℂ)
    (hF : ∀ i ∈ s, ∀ k : ℕ, ContDiff ℂ k (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x := by
  unfold polyDeriv
  have hD : ∀ N : ℕ, iteratedFDeriv ℂ N (fun w => ∑ i ∈ s, c i * F i w) x =
      ∑ i ∈ s, c i • iteratedFDeriv ℂ N (F i) x := by
    intro N
    show iteratedFDeriv ℂ N (fun w => ∑ i ∈ s, c i • F i w) x = _
    rw [iteratedFDeriv_sum (fun i hi => (hF i hi N).const_smul (c i)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact iteratedFDeriv_const_smul_apply (a := c i) (hF i hi N).contDiffAt
  simp only [hD, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  ring

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace PT

variable (X : PT E)

theorem fd_eq (n : ℕ) : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
  ext v
  simp [PT.fd, Set.mem_pi]

theorem isBounded_fd (n : ℕ) : Bornology.IsBounded (X.fd n) := by
  rw [fd_eq]
  exact Bornology.IsBounded.pi fun _ => ZSpan.fundamentalDomain_isBounded X.b

theorem integrableOn_fd {n : ℕ} {g : (Fin n → Vsp X.dim) → ℂ} (hg : Continuous g) :
    IntegrableOn g (X.fd n) := by
  exact (hg.continuousOn.integrableOn_compact (X.isBounded_fd n).isCompact_closure).mono_set
    subset_closure

theorem continuous_weight (q n : ℕ) :
    Continuous fun v : Fin n → Vsp X.dim => (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by
  have hc : ∀ (k : Fin n) (i : Idx X.dim), Continuous fun v : Fin n → Vsp X.dim => v k i :=
    fun k i => (EuclideanSpace.proj i).continuous.comp (continuous_apply k)
  have hHC : Continuous fun v : Fin n → Vsp X.dim => HC v v := by
    unfold HC Hf
    exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun i _ =>
      (hc k i).mul (Complex.continuous_conj.comp (hc k i))
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp hHC)))

theorem l2_sum_eq_sum_norm_sq_of_orthogonal {n : ℕ} (q : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → (Fin n → Vsp X.dim) → ℂ) (he : ∀ i ∈ s, Continuous (e i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → X.l2ip q (e i) (e j) = 0) :
    X.l2 q (fun v => ∑ i ∈ s, c i * e i v) = ∑ i ∈ s, ‖c i‖ ^ 2 * X.l2 q (e i) := by
  classical
  have hwc := X.continuous_weight q n
  have hpt : ∀ (G : (Fin n → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim), X.ptN2 q G v =
      (G v * (starRingEnd ℂ) (G v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)).re := by
    intro G v
    simp only [PT.ptN2]
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hint : ∀ G H : (Fin n → Vsp X.dim) → ℂ, Continuous G → Continuous H →
      MeasureTheory.IntegrableOn (fun v => G v * (starRingEnd ℂ) (H v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)) (X.fd n) :=
    fun G H hG hH => X.integrableOn_fd ((hG.mul (Complex.continuous_conj.comp hH)).mul hwc)
  have hA : ∀ G : (Fin n → Vsp X.dim) → ℂ, Continuous G → X.l2 q G = (X.l2ip q G G).re := by
    intro G hG
    simp only [PT.l2, PT.l2ip, MeasureTheory.setAverage_eq]
    simp_rw [hpt G]
    rw [Complex.smul_re]
    congr 1
    first
      | exact integral_re (hint G G hG hG)
      | simpa using integral_re (hint G G hG hG)
  have hsum_int : ∀ v : Fin n → Vsp X.dim,
      (∑ i ∈ s, c i * e i v) * (starRingEnd ℂ) (∑ i ∈ s, c i * e i v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) *
        (e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have hterm : ∀ i ∈ s, ∀ j ∈ s, MeasureTheory.IntegrableOn (fun v => (c i * (starRingEnd ℂ) (c j)) *
      (e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ))) (X.fd n) :=
    fun i hi j hj => (hint (e i) (e j) (he i hi) (he j hj)).const_mul _
  have hB : ∫ v in X.fd n, (∑ i ∈ s, c i * e i v) * (starRingEnd ℂ) (∑ i ∈ s, c i * e i v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) *
        ∫ v in X.fd n, e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by
    simp_rw [hsum_int]
    rw [MeasureTheory.integral_finsetSum _ fun i hi =>
      MeasureTheory.integrable_finsetSum _ fun j hj => hterm i hi j hj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finsetSum _ fun j hj => hterm i hi j hj]
    refine Finset.sum_congr rfl fun j _ => ?_
    first
      | exact MeasureTheory.integral_const_mul _ _
      | exact MeasureTheory.integral_mul_left _ _
  have hF : Continuous (fun v => ∑ i ∈ s, c i * e i v) :=
    continuous_finsetSum _ fun i hi => continuous_const.mul (he i hi)
  have hip : X.l2ip q (fun v => ∑ i ∈ s, c i * e i v) (fun v => ∑ i ∈ s, c i * e i v) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * X.l2ip q (e i) (e j) := by
    simp only [PT.l2ip, MeasureTheory.setAverage_eq]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    first
      | (simp only [Complex.real_smul]; ring)
      | rw [mul_smul_comm]
  have hdiag : ∀ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * X.l2ip q (e i) (e j) =
      (c i * (starRingEnd ℂ) (c i)) * X.l2ip q (e i) (e i) := by
    intro i hi
    refine Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => absurd hi h)
    rw [horth i hi j hj (Ne.symm hji), mul_zero]
  rw [hA _ hF, hip, Finset.sum_congr rfl hdiag, Complex.re_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hA _ (he i hi), Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

end PT

theorem iOf (hJ : JStatement) (hN : NStatement) : IStatement := by
  unfold IStatement
  intro E _ _ _ X n nb bs hbs P π hπ s hs hs0 K hK
  obtain ⟨hmem, horth, hl2, hspan⟩ := hN E X P.q n π P.hq hπ s hs hs0 K hK
  obtain ⟨F, hF, hF1, hJF⟩ := hJ E X n nb bs hbs P
  have hUd : ∀ b ∈ K, Differentiable ℂ (X.U P.q b (s0 X π s)) := fun b hb => (hmem b hb).1
  have hUc : ∀ b ∈ K, Continuous (X.U P.q b (s0 X π s)) := fun b hb => (hUd b hb).continuous
  have hFspan := hspan hF
  rw [Finsupp.mem_span_image_iff_linearCombination] at hFspan
  obtain ⟨l, hl, hlF⟩ := hFspan
  have hsub : l.support ⊆ K := by
    have h := (Finsupp.mem_supported ℂ l).1 hl
    exact Finset.coe_subset.1 h
  have hFsum : F = fun v => ∑ b ∈ K, l b * X.U P.q b (s0 X π s) v := by
    rw [← hlF, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l hsub (fun b a => a • X.U P.q b (s0 X π s))
        (fun b _ => zero_smul ℂ _)]
    funext v
    simp [Finset.sum_apply, smul_eq_mul]
  have hl2F : X.l2 P.q F = ∑ b ∈ K, ‖l b‖ ^ 2 * X.l2 1 s ^ n := by
    rw [hFsum, X.l2_sum_eq_sum_norm_sq_of_orthogonal P.q K l (fun b => X.U P.q b (s0 X π s)) hUc
      (fun b hb b' hb' hne => horth b hb b' hb' hne)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hl2 b hb]
  have hpd : polyDeriv (P1 bs) dir F 0 =
      ∑ b ∈ K, l b * polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0 := by
    rw [hFsum]
    exact polyDeriv_sum _ _ K l (fun b => X.U P.q b (s0 X π s))
      (fun b hb k => contDiff_of_differentiable_fd (hUd b hb) k) 0
  have hS : X.l2 1 s ^ n * ∑ b ∈ K, ‖l b‖ ^ 2 = 1 := by
    rw [← hF1, hl2F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hSnn : 0 ≤ ∑ b ∈ K, ‖l b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hLpos : 0 < X.l2 1 s ^ n := by
    rcases le_or_gt (X.l2 1 s ^ n) 0 with h | h
    · nlinarith
    · exact h
  have hnorm : ‖polyDeriv (P1 bs) dir F 0‖ ≤
      ∑ b ∈ K, ‖l b‖ * ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ := by
    rw [hpd]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq K (fun b => ‖l b‖)
    (fun b => ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖)
  have h1 : ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 ≤ (∑ b ∈ K, ‖l b‖ ^ 2) *
      ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2 := by
    refine le_trans ?_ hcs
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc P.Jbound n * X.l2 1 s ^ n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 * X.l2 1 s ^ n :=
        mul_le_mul_of_nonneg_right hJF hLpos.le
    _ ≤ ((∑ b ∈ K, ‖l b‖ ^ 2) *
          ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2) * X.l2 1 s ^ n :=
        mul_le_mul_of_nonneg_right h1 hLpos.le
    _ = ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2 := by
        rw [mul_comm (∑ b ∈ K, ‖l b‖ ^ 2), mul_assoc, mul_comm (∑ b ∈ K, ‖l b‖ ^ 2), hS, mul_one]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

def DimStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q : ℕ), 1 ≤ q →
    FiniteDimensional ℂ (Y.Sec q) ∧ Module.finrank ℂ (Y.Sec q) ≤ q ^ Fintype.card ι

theorem dim : DimStatement :=
  fun _ _ Y q hq => DimC.dim_core Y q hq

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
section
namespace ReciprocityTheory.ChartRestriction.G.I2.Ext

theorem all : All :=
  ⟨Formalism.LatticeBaseChangeAlt.packingCount, Formalism.LatticeBaseChangeAlt.gaussian_tail_bound, Formalism.LatticeBaseChangeAlt.ballVolume, Formalism.LatticeBaseChangeAlt.gHadamard,
    Formalism.LatticeBaseChangeAlt.nearestPlane, Formalism.LatticeBaseChangeAlt.cauchyBinetMax, Formalism.LatticeBaseChangeAlt.detPerturbation,
    Formalism.LatticeBaseChangeAlt.detPerturbNumeric, Formalism.LatticeBaseChangeAlt.detProductRest⟩

end ReciprocityTheory.ChartRestriction.G.I2.Ext
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma Hf_eq_inner {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, mul_comm]

lemma Hf_add_left {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

lemma Hf_zero_left {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : Hf 0 v = 0 := by
  simp [Hf]

open Classical in
def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

open Classical in
lemma prj_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    prj σ v i = if i.1 = σ then v i else 0 := rfl

lemma prj_inPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : InPart σ (prj σ v) := by
  intro j hj
  rw [prj_apply, if_neg hj]

lemma Hf_prj_right {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {v : Vsp dim} (hv : InPart σ v) (x : Vsp dim) :
    Hf v (prj σ x) = Hf v x := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_apply]
  split_ifs with h
  · rfl
  · rw [hv i h, zero_mul, zero_mul]

lemma norm_prj_le {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : ‖prj σ v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [prj_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero]
    positivity

lemma ne_conj [IsCMField E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hc := NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk σ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  exact hc (ComplexEmbedding.isReal_iff.mpr h)

open Classical in
def Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then c * v i else
    if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> ring
  map_smul' a v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

open Classical in
lemma Mc_apply {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) (i : Idx dim) :
    Mc σ c v i = if i.1 = σ then c * v i else
      if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0 := rfl

lemma real_inner_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v w : Vsp dim) :
    inner ℝ (Mc σ c v) w = inner ℝ v (Mc σ ((starRingEnd ℂ) c) w) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Mc_apply, Mc_apply]
  split_ifs <;> simp only [Complex.inner, map_mul, Complex.conj_conj, mul_zero, zero_mul,
    map_zero] <;> ring_nf

lemma prj_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) :
    prj σ (Mc σ c v) = c • prj σ v := by
  ext i
  rw [prj_apply, PiLp.smul_apply, prj_apply, Mc_apply, smul_eq_mul]
  split_ifs <;> simp

lemma prj_eq_Mc [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) :
    prj σ v = (1 / 2 : ℂ) • (Mc σ 1 v - Complex.I • Mc σ Complex.I v) := by
  ext i
  simp only [prj_apply, PiLp.smul_apply, PiLp.sub_apply, Mc_apply, smul_eq_mul, map_one,
    Complex.conj_I]
  split_ifs
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring_nf
    rw [Complex.I_sq]
    ring
  · ring

lemma isU_add {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim}
    (hu : IsU I x u) (hv : IsU I y v) : IsU I (x + y) (u + v) :=
    ⟨add_mem hu.1 hv.1, fun a ha => by
      rw [inner_add_left, hu.2 a ha, hv.2 a ha, Hf_add_left, Complex.add_im]⟩

lemma isU_neg {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim}
    (hu : IsU I x u) : IsU I (-x) (-u) :=
    ⟨neg_mem hu.1, fun a ha => by
      have hn : Hf (-x) a = -Hf x a := by simp [Hf, Finset.sum_neg_distrib]
      rw [inner_neg_left, hu.2 a ha, hn, Complex.neg_im]⟩

lemma isU_zero {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 :=
    ⟨zero_mem _, fun a _ => by rw [inner_zero_left, Hf_zero_left, Complex.zero_im]⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure TorusAt (X : Data E r) (x : Frame X.Ψ r) where
  T : PT E
  φ : (Fin r → E) →+ Vsp T.dim
  sg : ℝ
  sg_pm : sg = 1 ∨ sg = -1

  dim_pos : ∀ τ : X.Ψ, T.dim τ.1 = X.p0
  dim_neg : ∀ τ : X.Ψ, T.dim (ComplexEmbedding.conjugate τ.1) = r - X.p0

  e : X.Ψ → Fin r → (Fin r → ℂ)
  e_orth : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0
  e_flag : ∀ τ (i : ℕ) (hi : i ≤ r),
    Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) =
      Submodule.span ℂ (Set.range fun a : Fin i => col (mat x τ) (Fin.castLE hi a))

  coord_pos : ∀ (τ : X.Ψ) (a : Fin (T.dim τ.1)) (v : Fin r → E),
    (φ v) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      hermC τ.1 X.Gm (Data.emb τ.1 v) (e τ (Fin.castLE (by rw [dim_pos τ]; exact X.p0_le) a))
  coord_neg : ∀ (τ : X.Ψ) (a : Fin (T.dim (ComplexEmbedding.conjugate τ.1))) (v : Fin r → E),
    (φ v) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      (starRingEnd ℂ) (-hermC τ.1 X.Gm (Data.emb τ.1 v)
        (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (dim_neg τ); have := X.p0_le; omega⟩))
  lat : ∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y
  act_eq : ∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)
  im_eq : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
    sg * ((Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) : ℚ) : ℝ)

  w0 : 𝓞 E
  eps_eq : ∀ v ∈ X.Λ, (T.eps (φ v) : ℝ) = Real.cos (Real.pi * (Hf (φ v) (φ ((w0 : E) • v))).im)

  s : (Fin 1 → Vsp T.dim) → ℂ
  s_mem : s ∈ T.Sec 1 1
  s_ne : s ≠ 0

def TorusAtExistsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ φ : X.Λ →+ ℤ, ∃ u ∈ X.Λ, ∀ v : X.Λ,
      (φ v : ℚ) = Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (v : Fin r → E))) →
    ∀ w0 : 𝓞 E, (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) →
    ∀ x ∈ X.dom, ∃ A : TorusAt X x, A.w0 = w0

def TorusAtIsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (A : TorusAt X x), IsTorusAt X x A.T

end

end ReciprocityTheory.ChartRestriction.G.I2
end

