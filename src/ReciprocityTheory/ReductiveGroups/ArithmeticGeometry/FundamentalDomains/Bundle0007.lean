module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

section onetau

variable (ξ : Fin r → E) (τ : X.Ψ)

private theorem flowMat_mulVec' (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v - (I * X.c τ * s * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  ext a
  simp only [Matrix.mulVec, dotProduct, flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hermC_sub_const_smul_right (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (w v e : Fin r → ℂ) (k : ℂ) :
    hermC σ G w (v - k • e) = hermC σ G w v - conj k * hermC σ G w e := by
  simp only [hermC, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
  ring

lemma flow_fix (s : ℂ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (emb τ.1 ξ) = 0) :
    Matrix.mulVec (X.flowMat ξ τ s) v = v := by
  rw [flowMat_mulVec', hv, mul_zero, zero_smul, sub_zero]

lemma hC_right_flow (s : ℂ) (y v : Fin r → ℂ) (hy : hermC τ.1 X.Gm y (emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm y (Matrix.mulVec (X.flowMat ξ τ s) v) = hermC τ.1 X.Gm y v := by
  rw [flowMat_mulVec', hermC_sub_const_smul_right, hy, mul_zero, sub_zero]

lemma col_flow (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (a : Fin r) :
    col (mat (X.flow ξ s x) τ) a = Matrix.mulVec (X.flowMat ξ τ (s τ)) (col (mat x τ) a) := by
  ext k
  rfl

lemma mulVec_lin (M : Matrix (Fin r) (Fin r) ℂ) {n : ℕ} (β : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    Matrix.mulVec M (∑ a, β a • v a) = ∑ a, β a • Matrix.mulVec M (v a) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]

lemma ppos_flow {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom)
    (u : Fin r → ℂ) (hu : hermC τ.1 X.Gm u (emb τ.1 ξ) = 0)
    (hp : hermC τ.1 X.Gm (X.ppos x τ u) (emb τ.1 ξ) = 0) :
    X.ppos (X.flow ξ s x) τ u = X.ppos x τ u := by
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a with hα
  have hpx : X.ppos x τ u = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hT : ∑ a, α a • col (mat (X.flow ξ s x) τ) (Fin.castLE X.p0_le a) = X.ppos x τ u := by
    simp only [col_flow]
    rw [← mulVec_lin, ← hpx, flow_fix X ξ τ _ _ hp]
  rw [← hT]
  apply ppos_eq_of X (X.flow ξ s x) τ (gramPos_det_ne X hxs τ) u α
  intro b
  rw [hT, col_flow, hC_right_flow]
  · exact ppos_orth X x τ (gramPos_det_ne X hx τ) u b
  · rw [hC_sub_left, hu, hp, sub_zero]

end onetau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermEqZeroOfTraceFormVanish
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

lemma mem_orthogonal_lattice_iff {r : ℕ} (X : Data E r) (ξ v : Fin r → E) :
    v ∈ X.Λp ξ ↔ v ∈ X.Λ ∧ herm X.Gm v ξ = 0 := by first | exact Iff.rfl | simp [Data.Λp, Data.hermL]

lemma integer_smul_eq_coe_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  first
    | rfl
    | (funext i; simp [Algebra.smul_def])

lemma trace_form_integer_smul {r : ℕ} (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E)
    (β : 𝓞 E) :
    EFf ξ0 G x (β • y) = Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) := by
  unfold EFf herm
  rw [integer_smul_eq_coe_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_eq_zero_of_trace_form_vanish {r : ℕ} (ξ0 : E) (hξ0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) (h : ∀ β : 𝓞 E, EFf ξ0 G x (β • y) = 0) : herm G x y = 0 := by
  have hb : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) = 0 := fun β =>
    (trace_form_integer_smul ξ0 G x y β).symm.trans (h β)
  have hinv : ∀ a : E, cc (cc a) = a := by
    have h2 := pow_orderOf_eq_one (NumberField.IsCMField.complexConj E)
    rw [NumberField.IsCMField.orderOf_complexConj, pow_two] at h2
    intro a
    have := congrArg (fun σ => σ a) h2
    simpa [cc] using this
  have hw : ∀ w : E, Algebra.trace ℚ E (w * (-ξ0 * herm G x y)) = 0 := by
    intro w
    rw [← hinv w, ← (NumberField.integralBasis E).sum_repr (cc w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cc, map_sum, map_rat_smul, Finset.sum_mul, smul_mul_assoc, LinearMap.map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [NumberField.integralBasis_apply]
    have := hb ((NumberField.RingOfIntegers.basis E) i)
    simp only [cc] at this
    rw [smul_eq_zero]
    exact Or.inr this
  have hz : -ξ0 * herm G x y = 0 := by
    have hnd := traceForm_nondegenerate ℚ E
    have hw' : ∀ w : E, Algebra.traceForm ℚ E (-ξ0 * herm G x y) w = 0 := fun w => by
      rw [Algebra.traceForm_apply, mul_comm]
      exact hw w
    first
      | exact hnd _ hw'
      | exact hnd.1 _ hw'
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd (neg_eq_zero.1 h1) hξ0
  · exact h1

theorem hermitian_dual_lattice_identity : PerfectPairingQuotient (E := E) := by
  intro r X ξ hξ
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hsm : ∀ (β : 𝓞 E) v, v ∈ X.Λp ξ → β • v ∈ X.Λp ξ := by
    intro β v hv
    rw [mem_orthogonal_lattice_iff] at hv ⊢
    refine ⟨X.Λ.smul_mem β hv.1, ?_⟩
    rw [integer_smul_eq_coe_smul, herm_smul_left, hv.2, mul_zero]
  have hξp : ξ ∈ X.Λp ξ := (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hξΛ, hξξ⟩
  constructor
  · intro φ hφ
    have : Module.Finite (𝓞 E) ↥X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
    have : Module.Finite ℤ ↥X.Λ := Module.Finite.trans (𝓞 E) ↥X.Λ
    let f : ↥X.Λ →ₗ[ℤ] E := ((X.hermL ξ).comp X.Λ.subtype.toAddMonoidHom).toIntLinearMap
    have hf : ∀ m : ↥X.Λ, f m = herm X.Gm (m : Fin r → E) ξ := fun m => rfl
    let P := LinearMap.ker f
    have : Module.IsTorsionFree ℤ (↥X.Λ ⧸ P) := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro n q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective P q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker,
        map_zsmul] at hq
      rcases smul_eq_zero.mp hq with h | h
      · exact Or.inl h
      · exact Or.inr ((Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_ker.mpr h))
    obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
    have hsq : ∀ q, P.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
    have hρ : ∀ m : ↥X.Λ, m - s (P.mkQ m) ∈ P := by
      intro m
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change P.mkQ m - P.mkQ (s (P.mkQ m)) = 0
      rw [hsq, sub_self]
    let ψ : ↥X.Λ →+ ℤ :=
      { toFun := fun m => φ ⟨((m - s (P.mkQ m) : ↥X.Λ) : Fin r → E),
          (mem_orthogonal_lattice_iff _ _ _).mpr ⟨(m - s (P.mkQ m)).2, LinearMap.mem_ker.mp (hρ m)⟩⟩
        map_zero' := by
          rw [← map_zero φ]; congr 1; ext1; simp
        map_add' := by
          intro a b
          rw [← map_add φ]; congr 1; ext1
          simp only [map_add (f := _)]
          push_cast
          abel }
    obtain ⟨x, hxΛ, hx⟩ := X.EF_perf ψ
    have hval : ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm x ν := by
      intro ν
      have hν := (mem_orthogonal_lattice_iff _ _ _).mp ν.2
      have hP : (⟨ν, hν.1⟩ : ↥X.Λ) ∈ P := by rw [LinearMap.mem_ker, hf]; exact hν.2
      have hmk : P.mkQ (⟨ν, hν.1⟩ : ↥X.Λ) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hP
      have hψ : ψ ⟨ν, hν.1⟩ = φ ν := by
        show φ _ = φ ν
        congr 1; ext1
        simp [hmk]
      rw [← hψ]; exact hx ⟨ν, hν.1⟩
    have hxξ : herm X.Gm x ξ = 0 := by
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      have hmem := hsm β ξ hξp
      have h0 := hφ ⟨β • ξ, hmem⟩ ⟨(β : E), integer_smul_eq_coe_smul β ξ⟩
      have h1 := hval ⟨β • ξ, hmem⟩
      rw [h0] at h1
      simpa using h1.symm
    exact ⟨⟨x, (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hxΛ, hxξ⟩⟩, hval⟩
  · intro μ hμ
    apply exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ0
    intro y hy
    have horth : ∀ ν ∈ X.Λp ξ, herm X.Gm μ ν = 0 := by
      intro ν hν
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      exact hμ ⟨β • ν, hsm β ν hν⟩
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem (F := E) X.Λ (x := y)
      (by rw [X.Λ_span]; exact Submodule.mem_top)
    have hdyp : d • y ∈ X.Λp ξ := by
      rw [mem_orthogonal_lattice_iff]
      refine ⟨hdy, ?_⟩
      rw [integer_smul_eq_coe_smul, herm_smul_left, hy, mul_zero]
    have h2 := horth _ hdyp
    rw [integer_smul_eq_coe_smul, herm_smul_right] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by simpa using hd)
    · exact h

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralTraceNormBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds

open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

lemma cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma cc_two : cc (2 : E) = 2 := by
  unfold cc
  exact map_ofNat _ 2

lemma inner_iota_eq_trace (x y : E) :
    inner ℝ (iota E x) (iota E y) = (1 / 2 : ℝ) * (Algebra.trace ℚ E (x * cc y) : ℝ) := by
  rw [inner_iota, ← sum_re_eq_trace]
  apply Finset.sum_congr rfl
  intro w _
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj]


variable (E) in
noncomputable def ed : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate (K := ℚ) (L := E)) (integralBasis E)

lemma trace_ed (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (integralBasis E i * ed E j) = if i = j then 1 else 0 := by
  rw [← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm ℚ) _ i j


variable (E) in
noncomputable def bd (j : Free.ChooseBasisIndex ℤ (𝓞 E)) : VS E := iota E (2 * cc (ed E j))

lemma inner_bas_bd (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    inner ℝ (bas E i) (bd E j) = if i = j then 1 else 0 := by
  rw [bas_apply, bd, inner_iota_eq_trace, cc_mul, cc_cc, cc_two]
  have h2 : integralBasis E i * (2 * ed E j) = (2 : ℚ) • (integralBasis E i * ed E j) := by
    rw [Algebra.smul_def, map_ofNat]
    ring
  rw [h2, LinearMap.map_smul, trace_ed]
  split_ifs <;> norm_num

lemma trace_int (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed E j) * (γ : E)) = m := by
  obtain ⟨m, hm⟩ : ∃ m : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
      (γ : E) = ∑ i, m i • integralBasis E i := by
    refine ⟨(RingOfIntegers.basis E).repr γ, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr γ]
    simp [integralBasis_apply]
  have key : ∀ j i, Algebra.trace ℚ E ((c j • ed E j) * (m i • integralBasis E i)) =
      if i = j then ((c j * m i : ℤ) : ℚ) else 0 := by
    intro j i
    rw [smul_mul_smul_comm, map_zsmul, mul_comm (ed E j), trace_ed]
    split_ifs <;> simp
  refine ⟨∑ j, c j * m j, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hm, Finset.sum_mul_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, key]
  simp [Finset.sum_ite_eq']

lemma norm_discr (β : E) (hβ : β ≠ 0)
    (hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * (γ : E)) = m) :
    1 ≤ |(Algebra.norm ℚ β : ℝ)| * dE E := by
  choose m hm using fun i j => hint (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
  have hbB : ∀ i, integralBasis E i = ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [integralBasis_apply]
  have hP : Matrix.of (fun i j => ((m i j : ℤ) : ℚ)) =
      Algebra.traceMatrix ℚ (integralBasis E) * Algebra.leftMulMatrix (integralBasis E) β := by
    ext i j
    rw [Matrix.of_apply, ← hm i j, Matrix.mul_apply]
    have e : β * ((RingOfIntegers.basis E i * RingOfIntegers.basis E j : 𝓞 E) : E) =
        integralBasis E i * (β * integralBasis E j) := by
      rw [hbB, hbB]
      push_cast
      ring
    rw [e]
    conv_lhs => rw [← (integralBasis E).sum_repr (β * integralBasis E j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    ring
  have h1 : ((Matrix.of m).det : ℚ) = (Matrix.of (fun i j => ((m i j : ℤ) : ℚ))).det := by
    rw [show ((Matrix.of m).det : ℚ) = (Int.castRingHom ℚ) (Matrix.of m).det from rfl,
      RingHom.map_det]
    rfl
  have hdet : ((Matrix.of m).det : ℚ) = (NumberField.discr E : ℚ) * Algebra.norm ℚ β := by
    rw [h1, hP, Matrix.det_mul, NumberField.coe_discr, Algebra.discr_def,
      Algebra.norm_eq_matrix_det (integralBasis E)]
  have hN0 : Algebra.norm ℚ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
  have hD0 : (NumberField.discr E : ℚ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hZ : (Matrix.of m).det ≠ 0 := by
    intro h
    have h0 : ((Matrix.of m).det : ℚ) = 0 := by rw [h]; simp
    rw [hdet] at h0
    exact mul_ne_zero hD0 hN0 h0
  have hR : ((Matrix.of m).det : ℝ) =
      ((NumberField.discr E : ℤ) : ℝ) * ((Algebra.norm ℚ β : ℚ) : ℝ) := by
    have h2 := congrArg (Rat.cast : ℚ → ℝ) hdet
    simp only [Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2
  unfold dE
  rw [← abs_mul, mul_comm, ← hR]
  exact_mod_cast Int.one_le_abs hZ

lemma prod_norm (β : E) :
    ∏ w : CP E, ‖w.1.embedding β‖ ^ 2 = |(Algebra.norm ℚ β : ℝ)| := by
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm,
    ← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace E => IsTotallyComplex.isComplex w)).prod_comp]
  apply Finset.prod_congr rfl
  intro w _
  rw [InfinitePlace.norm_embedding_eq]
  change w.1 β ^ 2 = w.1 β ^ w.1.mult
  rw [InfinitePlace.mult_isComplex]

lemma dE_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)

lemma card_complexPlaces_pos : 0 < Fintype.card (CP E) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact Fintype.card_pos_iff.mpr ⟨⟨w, IsTotallyComplex.isComplex w⟩⟩

lemma norm_bd_ge (x : VS E) (hx : x ∈ span ℤ (Set.range (bd E))) (hx0 : x ≠ 0) :
    4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤ ‖x‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  obtain ⟨β, hβdef⟩ : ∃ β : E, β = ∑ j, c j • ed E j := ⟨_, rfl⟩
  have hxβ : x = iota E (2 * cc β) := by
    rw [← hc, hβdef]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, cc, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
  have hβ0 : β ≠ 0 := by
    rintro h
    apply hx0
    rw [hxβ, h, cc, map_zero, mul_zero, map_zero]
  have hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * γ) = m := by
    intro γ
    rw [hβdef]
    exact trace_int c γ
  have hN := norm_discr β hβ0 hint
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnorm : ‖x‖ ^ 2 = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
    rw [hxβ, norm_sq_iota, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [map_mul, norm_mul, cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj,
      map_ofNat, h2n]
    ring
  have hn : (0 : ℝ) < Fintype.card (CP E) := by exact_mod_cast card_complexPlaces_pos
  have hd : 0 < dE E := dE_pos
  have hNinv : (dE E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (CP E))
    (fun _ => 1 / (Fintype.card (CP E) : ℝ)) (fun w => ‖w.1.embedding β‖ ^ 2)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), prod_norm, ← Finset.mul_sum] at hgm
  have h1 : dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤
      |(Algebra.norm ℚ β : ℝ)| ^ (1 / (Fintype.card (CP E) : ℝ)) := by
    rw [Real.rpow_neg hd.le, ← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hd.le) hNinv (by positivity)
  rw [hnorm]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans hgm)
    (by positivity : (0 : ℝ) ≤ 4 * (Fintype.card (CP E) : ℝ))
  calc 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ)))
      ≤ 4 * (Fintype.card (CP E) : ℝ) *
        (1 / (Fintype.card (CP E) : ℝ) * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2) := h3
    _ = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
      rw [← mul_assoc, mul_assoc 4, mul_one_div_cancel hn.ne', mul_one]

end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalLatticeDecomposition
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem orthogonal_lattice_decomposition : ProjectionAlongComplement (E := E) := by
  intro r X ξ hξ x hx u hu
  obtain ⟨-, hiso, hne⟩ := hξ
  have key : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.ucomp x ξ u τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.Jz x (X.ucomp x ξ u) τ) (Data.emb τ.1 ξ) = 0 := by
    intro τ
    set e := Data.emb τ.1 ξ with he
    have he0 : e ≠ 0 := emb_ne_zero τ.1 hne
    have hee : hermC τ.1 X.Gm e e = 0 := by rw [he, hermC_emb, hiso, map_zero]
    have hη : X.Hf x τ e e ≠ 0 := fun h => by
      have := X.Hf_iso_pos hx τ he0 hee
      rw [h] at this; simp at this
    have hu' : X.ucomp x ξ u τ = u τ - (X.Hf x τ (u τ) e / X.Hf x τ e e) • e := rfl
    refine ⟨?_, ?_⟩
    · rw [hu', hermC_sub_left, hermC_smul_left, hee, mul_zero, sub_zero]
      exact hu τ
    · rw [Data.Jz_apply, hu', hermC_smul_left, Data.jp_sub, Data.jp_smul, hermC_sub_left,
        hermC_smul_left, ← Data.Hf_eq_jp, ← Data.Hf_eq_jp, div_mul_cancel₀ _ hη, sub_self, mul_zero]
  exact ⟨fun τ => (key τ).1, fun τ => (key τ).2⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

