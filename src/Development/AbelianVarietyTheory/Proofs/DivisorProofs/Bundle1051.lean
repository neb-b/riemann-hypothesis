module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0979
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QuadSymbol.SignCount

theorem card_prod_eq_mul_two {ι : Type} [Fintype ι] [Nonempty ι] (c : ℤˣ) :
    Nat.card {s : ι → ℤˣ // c * ∏ i, s i = 1} * 2 = 2 ^ Fintype.card ι := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let m : ι → ℤˣ := Pi.mulSingle i₀ (-1)
  have hm : ∏ i, m i = -1 := by simp [m, Finset.prod_pi_mulSingle']
  have hmm : m * m = 1 := by
    ext i
    by_cases h : i = i₀
    · subst h; simp [m]
    · simp [m, Pi.mulSingle_eq_of_ne h]
  have key : ∀ s : ι → ℤˣ, (c * ∏ i, (s * m) i = 1) ↔ ¬ (c * ∏ i, s i = 1) := by
    intro s
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hm]
    rcases Int.units_eq_one_or (c * ∏ i, s i) with h | h
    · rw [← mul_assoc, h]; decide
    · rw [← mul_assoc, h]; decide
  let e : {s : ι → ℤˣ // c * ∏ i, s i = 1} ≃ {s : ι → ℤˣ // ¬ (c * ∏ i, s i = 1)} :=
    { toFun := fun s => ⟨s.1 * m, fun h => (key s.1).1 h s.2⟩
      invFun := fun s => ⟨s.1 * m, by
        have := (key s.1).2 s.2
        exact this⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm]) }
  have htot := Fintype.card_subtype_compl (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [Nat.card_eq_fintype_card, mul_two]
  nth_rewrite 2 [Fintype.card_congr e]
  have hle := Fintype.card_subtype_le (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [htot, Fintype.card_pi, Finset.prod_const, Fintype.card_units_int, Finset.card_univ] at *
  omega

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

theorem neg_one_not_mem_normGroup {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : NumberField.IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) : (-1 : (w.Completion)ˣ) ∉ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg : InfinitePlace.embedding_of_isReal hw δ < 0 := by
    by_contra hc
    obtain ⟨r, hr⟩ := Real.isSquare_iff.2 (not_lt.1 hc)
    let τ : L →+* ℂ := ComplexEmbedding.lift L w.embedding
    have hτ : ∀ x : K, τ (algebraMap K L x) = InfinitePlace.embedding_of_isReal hw x := fun x => by
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact ComplexEmbedding.lift_algebraMap_apply L w.embedding x
    have h2 : τ (b 1) * τ (b 1) = (r : ℂ) * r := by rw [← map_mul, h1, hτ, hr]; push_cast; rfl
    have h3 : starRingEnd ℂ (τ (b 1)) = τ (b 1) := by
      rcases mul_self_eq_mul_self_iff.1 h2 with h | h <;> rw [h] <;> simp
    refine InfinitePlace.not_isReal_iff_isComplex.2 (hL.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    change starRingEnd ℂ (τ x) = τ x
    rw [← b.sum_repr x, Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def]
    simp only [map_add (f := _), map_mul, map_one, hτ, h3, Complex.conj_ofReal]
  rw [mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, hxy⟩
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K w.Completion δ) = InfinitePlace.embedding_of_isReal hw δ := by
    rw [InfinitePlace.Completion.algebraMap_apply]
    simpa [f, InfinitePlace.Completion.instCoe] using
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  have := congrArg f hxy
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, hf] at this
  nlinarith [sq_nonneg (f x), sq_nonneg (f y)]

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

def infSigns (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] (t : Kˣ) :
    InfinitePlace K → ℤˣ :=
  fun w => eta K L w.Completion (infDiag K t w)

theorem infSigns_eq_of_mem {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {t t' : Kˣ} (h : t⁻¹ * t' ∈ globalNorms K L) :
    infSigns K L t' = infSigns K L t := by
  funext w
  refine eta_eq_of_div_mem ?_
  have := toUnits_mem_normGroup (K := K) (L := L) w.Completion h
  rw [← div_eq_inv_mul, _root_.map_div] at this
  exact this

theorem infSigns_out {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (t : Kˣ) :
    infSigns K L (Quotient.out (QuotientGroup.mk t : Kˣ ⧸ globalNorms K L)) = infSigns K L t :=
  infSigns_eq_of_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm)

theorem card_classes_mul_two : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L], NumberField.IsTotallyReal K → NumberField.IsTotallyComplex L → ∀ x : GlobalTheory.QuadSymbol.FinFam K, GlobalTheory.QuadSymbol.AlmostNorm K L x → Nat.card {q : Kˣ ⧸ GlobalTheory.QuadSymbol.globalNorms K L // ∃ t : Kˣ, q = QuotientGroup.mk t ∧ ∀ u, x u / GlobalTheory.QuadSymbol.finDiag K t u ∈ GlobalTheory.QuadSymbol.normGroup K L (u.adicCompletion K)} * 2 = 2 ^ Fintype.card (InfinitePlace K) := by
  intro K L _ _ _ _ _ _ hK hL x hx
  have hfd : FiniteDimensional K L := Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨-, hnorm, hseq, -⟩ := exactSequence K L
  obtain ⟨-, hc2⟩ := localCharacters K L
  set c : ℤˣ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v) with hc
  rw [← card_prod_eq_mul_two c]
  congr 1
  have hprod : ∀ t : Kˣ, (∀ u, x u / finDiag K t u ∈ normGroup K L (u.adicCompletion K)) →
      c * ∏ w, infSigns K L t w = 1 := by
    intro t ht
    have := (hseq x (infDiag K t) hx).1 ⟨t, fun u => ht u, fun w => by simp [one_mem]⟩
    exact this
  refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨infSigns K L (Quotient.out q.1), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨t, hq, ht⟩ := q.2
    rw [hq, infSigns_out]
    exact hprod t ht
  · rintro ⟨q₁, t₁, rfl, h₁⟩ ⟨q₂, t₂, rfl, h₂⟩ he
    have he' : infSigns K L t₁ = infSigns K L t₂ := by
      have := congrArg Subtype.val he
      simpa only [infSigns_out] using this
    refine Subtype.ext (QuotientGroup.eq.2 ((hnorm (t₁⁻¹ * t₂)).1 ⟨fun u => ?_, fun w => ?_⟩))
    · have hm := div_mem (h₁ u) (h₂ u)
      rwa [div_div_div_cancel_left, finDiag, finDiag, ← _root_.map_div, div_eq_inv_mul] at hm
    · have hm := Converse.div_mem_normGroup (hc2 w) (congrFun he' w)
      rwa [infDiag, infDiag, ← _root_.map_div, div_eq_inv_mul] at hm
  · rintro ⟨s, hs⟩
    let y : InfFam K := fun w => if s w = 1 then 1 else -1
    have hy : ∀ w, eta K L w.Completion (y w) = s w := by
      intro w
      rcases Int.units_eq_one_or (s w) with h | h
      · simp only [y, h, if_true]
        exact eta_eq_one_iff.2 (one_mem _)
      · simp only [y, h, show (-1 : ℤˣ) ≠ 1 by decide, if_false]
        exact eta_eq_neg_one_iff.2 (neg_one_not_mem_normGroup hL (hK.isReal w))
    have hy1 : etaProd K L x y = 1 := by
      unfold etaProd
      rw [Finset.prod_congr rfl fun w _ => hy w]
      exact hs
    obtain ⟨t, ht1, ht2⟩ := (hseq x y hx).2 hy1
    refine ⟨⟨QuotientGroup.mk t, t, rfl, fun u => ht1 u⟩, Subtype.ext ?_⟩
    simp only [infSigns_out]
    funext w
    rw [← hy w]
    exact (eta_eq_of_div_mem (ht2 w)).symm

end GlobalTheory.QuadSymbol.SignCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VKill

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_exp {P : Mt n} (hP : IsUnit P) (X : Mt n) (t : ℝ) :
    P * NormedSpace.exp (t • X) * P⁻¹ = NormedSpace.exp (t • (P * X * P⁻¹)) := by
  rw [← Matrix.exp_conj P _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem dRep_conj {P : Mt n} (hP : IsUnit P) (σ : Mt n → (H →L[ℂ] H)) (X : Mt n) (v : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X v = dRep σ (P * X * P⁻¹) v := by
  unfold dRep
  simp only [conj_exp hP]

theorem conjH_conj {P : Mt n} (hP : IsUnit P) (J Z : Mt n) :
    conjH (Pᴴ * J * P) (P⁻¹ * Z * P) = P⁻¹ * conjH J Z * P := by
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h1 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h2 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold conjH
  simp only [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, Matrix.mul_neg,
    Matrix.neg_mul]

theorem dRepC_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) :
    dRepC (Pᴴ * J * P) (fun g => σ (P * g * P⁻¹)) (P⁻¹ * Z * P) v = dRepC J σ Z v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ (c : ℂ) (Y : Mt n), P * (c • (P⁻¹ * Y * P)) * P⁻¹ = c • Y := fun c Y => by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  unfold dRepC
  rw [dRep_conj hP, dRep_conj hP, conjH_conj hP, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.sub_mul, ← Matrix.mul_sub,
    h2, h2]

theorem conj_prod {P : Mt n} (hP : IsUnit P) (l : List (Mt n)) :
    P * l.prod * P⁻¹ = (l.map fun g => P * g * P⁻¹).prod := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  induction l with
  | nil => simp [Matrix.mul_nonsing_inv _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem smooth_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (v : H)
    (h : SmoothVec (lieH (Pᴴ * J * P)) (fun g => σ (P * g * P⁻¹)) v) : SmoothVec (lieH J) σ v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ Y : Mt n, P * (P⁻¹ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h3 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h4 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  intro k Xs hX
  have := h k (fun i => P⁻¹ * Xs i * P) (fun i => by
    have e : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    show (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) = 0
    have e2 : (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) =
        Pᴴ * ((Xs i)ᴴ * J + J * Xs i) * P := by
      simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, h4, Matrix.mul_add, Matrix.add_mul]
    rw [e2, e, Matrix.mul_zero, Matrix.zero_mul])
  simp only [conj_prod hP, List.map_ofFn, Function.comp_def, conj_exp hP] at this
  simp only [Matrix.mul_assoc, h2, h1, Matrix.mul_one] at this
  exact this

theorem jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).IsHermitian := by
  unfold Formalism.REAL.Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext a
  by_cases h : ε a <;> simp [h]

theorem jm_det (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  by_cases h : ε a <;> simp [h]

theorem borel_extVec (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec) (_hθ : IsInfFam θ) (hM : HolShape M) (hw : WtIs M w) (hv : IsExtVec M v)
    (τ : D.what₂.Tau) :
    SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c →
      dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
        if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  obtain ⟨hc, hU, -, hx⟩ := _root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ
  obtain ⟨-, hx⟩ := hx hM
  obtain ⟨hHC, p, hp, hε⟩ := hM τ
  obtain ⟨-, hlow, hwt⟩ := hv τ
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hG := M.fr_gram τ
  have hH : (gramAt D V τ).IsHermitian := by
    rw [← hG]; exact Matrix.isHermitian_conjTranspose_mul_mul _ (jm_herm _)
  have hD : (gramAt D V τ).det ≠ 0 := by
    rw [← hG, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero hPd.star.ne_zero (jm_det _)) hPd.ne_zero
  have hs : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) :=
    (GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ hH hD hU).1 _ (v τ).2
  refine ⟨hs, fun a c hac => ?_⟩
  have hs' : SmoothVec (lieH (Formalism.REAL.Jm (M.ε τ))) (M.σ τ) (v τ : M.H τ) := by
    refine smooth_conj hP _ _ _ ?_
    rw [hG]; exact hs
  have hl : (v τ : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hlow
  have hB := _root_.GlobalTheory.HolDict.BorelK.extremal_killed _ _ _ _ _ (M.ds τ) _ hl hs' hwt
  have hm := _root_.GlobalTheory.HolDict.Lowering.lowK_killed _ p _ _ _ _ hHC hε (M.ds τ) _ hl hs'
  have e : dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
      dRepC (Formalism.REAL.Jm (M.ε τ)) (M.σ τ)
        (Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1) (v τ : M.H τ) := by
    rw [hx a c, ← hG]
    exact dRepC_conj hP _ _ _ _
  rw [e]
  split_ifs with h
  · subst h
    rw [hB.1]
    have := hw τ a
    unfold extWt at this
    rw [← this]
    simp
  · have hlt : (a : ℕ) < c := lt_of_le_of_ne hac fun h' => h (Fin.ext h')
    have hq := nNeg_shape hp hε
    have hcn := c.2
    have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
      intro b
      have := b.2
      rw [hε, hq]
      unfold arr
      split_ifs with hb
      · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
      · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
    by_cases ha : (a : ℕ) < V.rank - p
    · by_cases hc' : (c : ℕ) < V.rank - p
      · refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
        rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_pos ha, if_pos hc']
        omega
      · exact hm _ _ (by rw [hsg]; simp [hc']) (by rw [hsg]; simp [ha])
    · have hc' : ¬ (c : ℕ) < V.rank - p := by omega
      refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
      rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_neg ha, if_neg hc']
      omega

end GlobalTheory.HolDict.VKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMin
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem real_root_quad_le {x : ℝ} {α β : ℂ} (h : (x : ℂ) ^ 2 - α * x - β = 0) : x ≤ ‖α‖ + ‖β‖ + 1 := by
  have h1 : (x : ℂ) ^ 2 = α * x + β := by linear_combination h
  have h2 : ‖(x : ℂ)‖ ^ 2 ≤ ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by
    calc ‖(x : ℂ)‖ ^ 2 = ‖(x : ℂ) ^ 2‖ := (norm_pow _ _).symm
    _ = ‖α * x + β‖ := by rw [h1]
    _ ≤ ‖α * x‖ + ‖β‖ := norm_add_le _ _
    _ = ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by rw [norm_mul]
  have hx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx] at h2
  have ha := norm_nonneg α
  have hb := norm_nonneg β
  by_contra hc
  push_neg at hc
  have ht : ‖α‖ + ‖β‖ + 1 < |x| := lt_of_lt_of_le hc (le_abs_self x)
  nlinarith [mul_nonneg hb (by linarith : (0:ℝ) ≤ |x| - 1),
    mul_pos (by linarith : (0:ℝ) < |x| - (‖α‖ + ‖β‖ + 1)) (by linarith : (0:ℝ) < |x|)]

theorem diag_eig_le_of_cas_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  intro ι _ _ s α β
  refine ⟨max (‖α‖ + ‖β‖ + 1) ((2 * ‖α‖ + Fintype.card ι + 1) / 4), ?_⟩
  intro M _ _ F hGl hq hLoc ω hω x y hy hfalse htrue hcas
  by_cases hz : ∀ j, s j = false → ∑ b, F j b (y b) = 0
  · have hbc := _root_.GlobalTheory.HoweR.qop_quadratic_on_eigenvector ι M s F α β x y hq hfalse htrue hz
    obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (funext h)
    have h0 : (x : ℂ) ^ 2 - α * x - β = 0 := by
      by_contra hne
      exact ha ((smul_eq_zero.mp (hbc a)).resolve_left hne)
    exact le_max_of_le_left (real_root_quad_le h0)
  · push_neg at hz
    obtain ⟨j, hj, hzj⟩ := hz
    have hd := _root_.GlobalTheory.HoweR.cas_drop ι M s F α β x ω y hGl hq hfalse htrue hcas j hj
    obtain ⟨U, hU, hUU⟩ := hLoc {∑ b, F j b (y b)}
    have hzU : ∑ b, F j b (y b) ∈ U := hU _ (Finset.mem_singleton_self _)
    have him := ((GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hUU).1 _ _ hzU hzj hd).1
    set c : ℂ := (ω : ℂ) - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ) with hc
    have hcre : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt := hω c.re _ hzj (by rw [← hcre]; exact hd)
    have hre : c.re = ω - 4 * x + 2 * α.re + ((Finset.univ.filter fun a => s a = true).card : ℝ)
      - ((Finset.univ.filter fun a => s a = false).card : ℝ) := by simp [hc]
    have hr : ((Finset.univ.filter fun a => s a = true).card : ℝ) ≤ Fintype.card ι := by
      have := Finset.card_filter_le (Finset.univ : Finset ι) (fun a => s a = true)
      rw [Finset.card_univ] at this
      exact_mod_cast this
    have hαre : α.re ≤ ‖α‖ := Complex.re_le_norm α
    have hr'0 : (0:ℝ) ≤ ((Finset.univ.filter fun a => s a = false).card : ℝ) := Nat.cast_nonneg _
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    linarith

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharpolyBound

theorem continuous_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  refine (MvPolynomial.continuous_eval _).comp ?_
  exact continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound {X : Type} [TopologicalSpace X] (w : Pl E) {f : X → w.adicCompletion E} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) : ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v (f x) ≤ B := by
  have hcov : C ⊆ ⋃ m : ℤ, f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v (f x)) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · exact ⟨WithZero.log (Valued.v (f x)), (WithZero.exp_log h).ge⟩
  have hmono : Monotone fun m : ℤ => f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro a b hab x hx
    exact le_trans hx (WithZero.exp_le_exp.2 hab)
  obtain ⟨m, hm⟩ := hC.elim_directed_cover _ (fun m => (isOpen_vle w m).preimage hf) hcov hmono.directed_le
  exact ⟨WithZero.exp m, fun x hx => hm hx⟩

end GlobalTheory.CharpolyBound

open GlobalTheory.CharpolyBound in
theorem GlobalTheory.CharpolyBound.bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ B) ∧ Valued.v ((g.val.charpoly.coeff 0)⁻¹) ≤ B := by
  intro E _ _ _ n w C hC
  have hval : Continuous fun g : GLw n w => g.val := Units.continuous_val
  have hinv : Continuous fun g : GLw n w => ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_coe_inv
  have hk : ∀ k : ℕ, ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, Valued.v (g.val.charpoly.coeff k) ≤ B :=
    fun k => exists_bound w ((continuous_coeff n k).comp hval) hC
  choose Bk hBk using hk
  obtain ⟨Bi, hBi⟩ := exists_bound w (hinv.matrix_det) hC
  refine ⟨(Finset.range (n + 1)).sup Bk ⊔ Bi, fun g hg => ⟨fun k => ?_, ?_⟩⟩
  · by_cases hkn : k ≤ n
    · exact le_sup_of_le_left ((hBk k g hg).trans (Finset.le_sup (f := Bk) (Finset.mem_range.2 (by omega))))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
      exact zero_le'
  · have h0 : g.val.charpoly.coeff 0 = (-1) ^ n * g.val.det := by
      rw [det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hdet : g.val.det * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
      rw [← det_mul, Units.mul_inv, det_one]
    have hc : (g.val.charpoly.coeff 0)⁻¹ =
        (-1) ^ n * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det := by
      rw [h0, mul_inv, inv_eq_of_mul_eq_one_right hdet, ← inv_pow, inv_neg_one]
    rw [hc, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact le_sup_of_le_right (hBi g hg)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.Div

theorem coh_subsingleton_of_cls_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB),
    cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) →
      Subsingleton (coh (LB.toMod N) q) := by
  intro X M N hM hN e q h
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hM hN e
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((Twist.unitTwistIso M).symm ≪≫ i ≪≫ Twist.unitTwistIso N)).toEquiv.subsingleton_congr.1 h

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocalStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → (minpoly G.F γ).Separable → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ (K : Type) (_ : CommRing K) (R : Subring K) (Φ : Matrix (Fin G.n) (Fin G.n) K ≃+* Qv v ⊗[ℚ] G.C), Set.Finite {I : Ideal R | I.IsMaximal} ∧ (∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a ↔ ∀ i j, Φ.symm a i j ∈ R) ∧ ∃ Q : Polynomial R, Q.Separable ∧ Q.map R.subtype = (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)).charpoly := by
  first | (exact @GlobalTheory.OrbFinAf.split_eventually) | (exact GlobalTheory.OrbFinAf.split_eventually) | (intros; apply GlobalTheory.OrbFinAf.split_eventually  <;> assumption)
end

