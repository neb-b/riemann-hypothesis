module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreMoment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagFibreMoment

theorem coeff_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (m : Fin 3 →₀ ℕ) :
    AddMonoidAlgebra.coeff (momentPoly μ w Q) m = ∫ p, w p * AddMonoidAlgebra.coeff Q m p ∂μ := by
  rw [momentPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h]
    simp

theorem momentPoly_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (s : Finset ι)
    (Q : ι → MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ i ∈ s, ∀ m, Integrable (fun p => w p * AddMonoidAlgebra.coeff (Q i) m p) μ) :
    momentPoly μ w (∑ i ∈ s, Q i) = ∑ i ∈ s, momentPoly μ w (Q i) := by
  ext m
  rw [coeff_momentPoly, coeff_sum, coeff_sum]
  simp only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => hQ i hi m

theorem continuous_coeff_aeval (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (AddMonoidAlgebra.coeff (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q) m) := by
  set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ
  set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) :=
    ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst),
      ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]
  have hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r) := by
    funext r
    fin_cases r
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum,
        map_mul, map_X, map_C]
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
  rw [hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (AddMonoidAlgebra.coeff (aeval v Q) m).continuous

theorem sum_words (k : ℕ) :
    ∑ i ∈ Finset.range k, ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ) =
      gPoly k := by
  rw [FibreLocal.gPoly_eq, FlagBundles.gKernel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  rw [show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]
  ring

theorem sum_diagWordMomentPoly (k : ℕ) :
    ∑ i ∈ Finset.range k, diagWordMomentPoly k i = fibreMomentPoly k := by
  simp only [diagWordMomentPoly]
  rw [← momentPoly_sum _ _ _ _ fun i _ m =>
    FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sum, ← map_sum, sum_words]
  rfl

end DiagFibreMoment

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial
open scoped Matrix

theorem frame_matrix_det_ne_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv
  have hsum : ∑ j, v j • b j = 0 := by
    ext l
    have := congrFun hvM l
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this
  have hli := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)
  funext j
  exact hli j

theorem FrameJacobianGeneric.proof (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : FrameJacobianGeneric.Statement := by
  classical
  intro n d J hJ hd b
  have := hJ
  set K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)
  let π : MvPolynomial (Fin n) ℂ →+* K :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hπ : ∀ f, π f = 0 ↔ f ∈ J := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  set r := Fintype.card (Fin n) - d with hr
  obtain ⟨a, c, hac⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero J G hG d hd
  have hrn : r = n - d := by rw [hr, Fintype.card_fin]
  have hGJ : ∀ i, G i ∈ J := fun i => hG ▸ Ideal.subset_span ⟨i, rfl⟩
  let V : Matrix (Fin r) (Fin n) K := Matrix.of fun i l => π (pderiv l (G (a i)))
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun l j => π (C (b j l))
  let W : Matrix (Fin r) (Fin n) K := Matrix.of fun i j => π (frameDeriv b j (G (a i)))
  have hW : W = V * N := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [W, V, N, frameDeriv, Matrix.mul_apply, map_sum, mul_comm]
  have hVc : (V.submatrix id c).det ≠ 0 := by
    have : V.submatrix id c = π.mapMatrix (Matrix.of fun i j => pderiv (c j) (G (a i))) := by
      ext i j
      rfl
    rw [this, ← RingHom.map_det]
    exact fun h => hac ((hπ _).mp h)
  have hN : N.det ≠ 0 := by
    have : N = π.mapMatrix ((C : ℂ →+* MvPolynomial (Fin n) ℂ).mapMatrix
        (Matrix.of fun j l : Fin n => b j l)ᵀ) := by
      ext l j
      rfl
    rw [this, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_transpose]
    intro h
    rw [hπ] at h
    have hu : IsUnit (C (Matrix.of fun j l : Fin n => b j l).det : MvPolynomial (Fin n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (frame_matrix_det_ne_zero b)).map C
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hVinj : ∀ x : Fin r → K, x ᵥ* V = 0 → x = 0 := by
    intro x hx
    apply Matrix.eq_zero_of_vecMul_eq_zero hVc
    ext j
    simpa [Matrix.vecMul, dotProduct] using congrFun hx (c j)
  have hWinj : ∀ x : Fin r → K, Wᵀ *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.mulVec_transpose, hW, ← Matrix.vecMul_vecMul] at hx
    exact hVinj x (Matrix.eq_zero_of_vecMul_eq_zero hN hx)
  obtain ⟨col, hcol⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero Wᵀ hWinj
  have hcol' : (W.submatrix id col).det ≠ 0 := by
    rwa [← Matrix.det_transpose, Matrix.transpose_submatrix]
  have hinj : Function.Injective col := by
    intro i i' h
    by_contra hne
    apply hcol
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp [h]
  let I₀ : Finset (Fin n) := (Finset.univ.image col)ᶜ
  have hmem : ∀ j, j ∈ Set.range col ↔ j ∉ I₀ := by
    intro j
    simp [I₀]
  let e : Fin r ≃ {j // j ∉ I₀} :=
    (Equiv.ofInjective col hinj).trans (Equiv.subtypeEquivRight hmem)
  have he : ∀ i, (e i : Fin n) = col i := fun i => rfl
  let f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ := fun k => G (a (e.symm k))
  have hli : LinearIndependent K (fun i => genericGradient J (G (a i))) := by
    rw [Fintype.linearIndependent_iff]
    intro x hx
    have : x ᵥ* V = 0 := by
      rw [Matrix.vecMul_eq_sum]
      exact hx
    simpa using congrFun (hVinj x this)
  have hspan : Submodule.span K (Set.range (genericGradient J ∘ f)) =
      Submodule.span K (genericGradient J '' (J : Set _)) := by
    have hrange : Set.range (genericGradient J ∘ f) =
        Set.range (fun i => genericGradient J (G (a i))) := by
      ext v
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e.symm k, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp [f]⟩
    rw [hrange]
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hGJ _, rfl⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact (hR n d J hd).trans (by simp)
  obtain ⟨s, hsJ, hs⟩ := hC n J {j // j ∉ I₀} f (fun k => hGJ _) hspan
  refine ⟨I₀, f, s, ?_, fun k => hGJ _, hsJ, ?_, hs⟩
  · rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    omega
  · intro hdet
    rw [← hπ, frameJacobianDet, RingHom.map_det, ← Matrix.det_submatrix_equiv_self e] at hdet
    apply hcol'
    convert hdet using 2
    ext i i'
    simp [f, W, he]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumEventual
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumEventual

def ind {n : ℕ} (T : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ T then 1 else 0

theorem sum_sign_prod_ind {n : ℕ} (e : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, ((ind T i : ℕ) : ℚ) ^ e i =
      ∏ i, (1 - (0 : ℚ) ^ e i) := by
  have h1 : ∏ i, (1 - (0 : ℚ) ^ e i) = ∏ i ∈ Finset.univ, (1 + -(0 : ℚ) ^ e i) := by
    simp only [sub_eq_add_neg]
  rw [h1, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, one_mul, Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin,
    ← Finset.prod_mul_prod_compl T, Finset.compl_eq_univ_sdiff]
  congr 1
  rw [Finset.prod_eq_one (fun i hi => by simp [ind, hi]), one_mul]
  exact Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_sdiff] at hi
    simp [ind, hi.2]

theorem mixed_eval {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℚ) (hQ : Q.totalDegree ≤ n) (c : ℚ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
        eval (Fin.snoc (α := fun _ => ℚ) (fun j => ((ind T j : ℕ) : ℚ)) c) Q =
      ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  trans ∑ T : Finset (Fin n), Q.coeff d * c ^ d (Fin.last n) *
      ((-1 : ℚ) ^ (n - T.card) * ∏ i : Fin n, ((ind T i : ℕ) : ℚ) ^ d i.castSucc)
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [← Finset.mul_sum, sum_sign_prod_ind]
  by_cases h0 : ∃ i : Fin n, d i.castSucc = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, pow_zero, sub_self])]
    ring
  · push Not at h0
    have hdeg := (le_totalDegree hd).trans hQ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at hdeg
    have hge : n ≤ ∑ i : Fin n, d i.castSucc := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i : Fin n, d i.castSucc :=
          Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h0 i)
    rw [show d (Fin.last n) = 0 by omega, pow_zero, mul_one]

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | a :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = (twistSys k x 0).sub I * ∏ i, (L i).sub I ^ ind T i := by
  unfold tensorSub
  rw [foldl_twist_sub, Fin.prod_univ_def]
  congr 1
  induction List.finRange n with
  | nil => simp
  | cons a l ih => by_cases ha : a ∈ T <;> simp [ha, ind, ih]

theorem tensorSub_eq_twistPows {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (twistSys k x 0).twistPows n L (ind T) :=
  SubSystem.ext_sub fun I => by rw [tensorSub_sub, SnapperSections.twistPows_sub]

end InterNumEventual


open InterNumEventual in
theorem InterNumEventual.proof (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) : InterNumEventual.Statement.{u, w} := by
  have hR : RestrLenEuler.Statement.{u, w} := RestrLenEuler.proof
  intro k _ Ω _ _ N x n pp L hW
  have := hW.isPrime
  obtain ⟨Q, hQ, hev⟩ := pieceChar_isNumPolyLT hH hS SnapperDiffPoly.proof L (n + 1) pp hW.isPrime hW.homog
    hW.le hW.dim.le 0
  have hQn : Q.totalDegree ≤ n := by
    rcases hQ with h | h
    · rw [h, totalDegree_zero]; exact Nat.zero_le _
    · omega
  have hall : ∀ᶠ c : ℕ in atTop, ∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c := by
    refine Filter.eventually_all.mpr fun T => ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (hR k Ω N x pp hW.homog hW.le n L (ind T))] with c hc
    rw [tensorSub_eq_twistPows]
    exact hc
  have hval : ∀ c : ℕ, (∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c) →
      (interSum pp (fun i => (L i).toSubSystem) c : ℚ) =
        ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
    intro c hc
    rw [← mixed_eval Q hQn (c : ℚ)]
    unfold interSum
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    have hT := hev (ind T) (c : ℤ)
    simp only at hT
    rw [hc T, hT, Int.cast_natCast]
  obtain ⟨c₀, hc₀⟩ := hall.exists
  refine ⟨interSum pp (fun i => (L i).toSubSystem) c₀, hall.mono fun c hc => ?_⟩
  exact_mod_cast (hval c hc).trans (hval c₀ hc₀).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

theorem MuFrameExists.proof (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) :
    MuFrameExists.Statement D H := by
  intro z hz
  choose c hc using hz.1
  have hx : segreCoord D.y c ≠ 0 := HermMetricEq.segreCoord_ne_zero hz hc
  obtain ⟨m, f, cc, hf, hcc, hsum, hdat⟩ := H.locally c hx
  choose vf hvf using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hf l)
  choose vc hvc using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hcc l)
  have hS : IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (∑ l, cc l * f l) z (∑ l, vc l * vf l) :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun l _ => (hvc l).mul (hvf l)
  rw [hsum] at hS
  have h1 : (∑ l, vc l * vf l) = 1 :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz hS IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one
  have hex : ∃ l, vf l ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at h1
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hb, u, hu, heq⟩ := hdat l
  exact ⟨⟨c, f l, ⟨hc, vf l, HermMetricEq.isValueAt_iff.2 (hvf l), hl⟩, b, hb, u, hu, heq⟩⟩

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem SnapperFinite.closed : SnapperFinite.Statement.{u, v, w} :=
  SnapperFinite.proof Extension.proof Extension.proof TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem SnapperSubquotFinite.closed : SnapperSubquotFinite.Statement.{u, v, w} :=
  SnapperSubquotFinite.proof SnapperFinite.closed

theorem SnapperQuotAdd.closed : SnapperQuotAdd.Statement.{u, v, w} :=
  SnapperQuotAdd.proof SnapperSubquotFinite.closed

theorem SnapperQuotDevissage.closed : SnapperQuotDevissage.Statement.{u, v, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof SnapperQuotAdd.closed SubFamilyTwist.proof

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

namespace SnapperSectionClosed

theorem snapperFinite : SnapperFinite.Statement.{u, w, w} :=
  SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem quotAdd : SnapperQuotAdd.Statement.{u, w, w} :=
  SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)

theorem quotDevissage : SnapperQuotDevissage.Statement.{u, w, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof

end SnapperSectionClosed


open SnapperSectionClosed in
theorem SnapperSection.full : SnapperSection.Statement.{u, w} :=
  SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof

end GroundTheory.Heights₂.Heights.Kleiman
end

