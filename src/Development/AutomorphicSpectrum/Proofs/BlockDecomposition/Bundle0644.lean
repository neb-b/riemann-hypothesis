module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0627
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0630
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalFormL2Mem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Weyl

variable {D : D7} {n : ℕ}

theorem mat_inv_eq (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) : mat g⁻¹ = blk4 0 (-1) 1 0 := by
  have h : blk4 (0 : Mx D n n) (-1) 1 0 * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simpa using block_matrix_one (n := n) (R := AE D)
  calc mat g⁻¹ = (blk4 (0 : Mx D n n) (-1) 1 0 * mat g) * mat g⁻¹ := by rw [h, Matrix.one_mul]
    _ = blk4 0 (-1) 1 0 := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

theorem inner_add_left (V : HSp D) (a b c : Mx D V.rank n) :
    inner V (a + b) c = inner V a c + inner V b c := by
  simp only [GlobalTheory.StdUnn.inner, adj_add, Matrix.add_mul]

theorem inner_add_right (V : HSp D) (a b c : Mx D V.rank n) :
    inner V a (b + c) = inner V a b + inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add]

theorem inner_neg_left (V : HSp D) (a c : Mx D V.rank n) : inner V (-a) c = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, adj_neg, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) (a c : Mx D V.rank n) : inner V a (-c) = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add _ a b

theorem trA_neg (a : AE D) : trA (-a) = -trA a := map_neg _ a

theorem halfTr_add_swap (V : HSp D) (a b : Mx D V.rank n) :
    halfTr (Matrix.trace (inner V a b)) + halfTr (Matrix.trace (inner V b a)) =
      trA (Matrix.trace (inner V a b)) := by
  have h : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  rw [halfTr, halfTr, ← GlobalTheory.SWLink.trA_inner_comm V a b, ← add_mul, h, one_mul]

theorem phase (V : HSp D) (t x y z : Mx D V.rank n) :
    (trA (Matrix.trace (inner V (t + -x) y)) + halfTr (Matrix.trace (inner V x y))) +
        trA (Matrix.trace (inner V z (t + -x))) =
      (trA (Matrix.trace (inner V z (-x))) + halfTr (Matrix.trace (inner V y (-x)))) +
        trA (Matrix.trace (inner V (z + y) t)) := by
  have h := halfTr_add_swap V x y
  have c := GlobalTheory.SWLink.trA_inner_comm V t y
  have hn : halfTr (Matrix.trace (inner V y (-x))) = -halfTr (Matrix.trace (inner V y x)) := by
    rw [inner_neg_right, Matrix.trace_neg, halfTr, halfTr, trA_neg, mul_neg]
  rw [hn]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, Matrix.trace_add, Matrix.trace_neg,
    trA_add, trA_neg]
  rw [c, ← h]
  abel

end GlobalTheory.CompanionTheory.EisCovar.Weyl

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → μ.IsAddHaarMeasure → ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hω hμ g hg v Φ Ψ hΨ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = yPart v := by
    rw [Weyl.mat_inv_eq g hg, x_part_mul_block]; simp
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = -xPart v := by
    rw [Weyl.mat_inv_eq g hg, y_part_mul_block]; simp
  funext z
  rw [hω.weyl g hg Ψ z]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, hω.weyl g hg Φ (z + yPart v), ← integral_const_mul,
    ← integral_add_right_eq_self (μ := μ) (fun t => Ψ.1 t * ψ (trA (Matrix.trace (inner V z t)))) (-xPart v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have e := Weyl.phase V t (xPart v) (yPart v) z
  have e2 := congrArg ψ e
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψ (_ + _)] at e2
  simp only [hΨ, PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, neg_add_cancel_right]
  linear_combination (Φ.1 t) * e2

end GlobalTheory.CompanionTheory.EisCovar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem IsInt.mul {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s t : Type} [Fintype s]
    {M : Matrix r s (w.adicCompletion E)} {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) :
    IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun l _ => (Ov E w).mul_mem (hM i l) (hN l j)

theorem tj_blk (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) ϖ k (blk h w m X) =
      if IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧
        IsInt w (ϖ • (X * (m.2⁻¹).val)) ∧ ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) then 1 else 0 := by
  rw [_root_.GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w n k ϖ hϖ hk]
  refine if_congr ?_ rfl rfl
  rw [_root_.GlobalTheory.CompanionTheory.CtS.isInt_blk_iff E n a b h w m X, _root_.GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff E n a b h w ϖ m X, _root_.GlobalTheory.CompanionTheory.CtS.ordL_blk_det E n a b h w m X]
  tauto

theorem hint_lat (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) (m : GLw a w × GLw b w)
    (i1 : IsInt w m.1.val) (j2 : IsInt w (ϖ • (m.2⁻¹).val))
    (t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0) (t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0) :
    hint (intMat a b w) (fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
        IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) = (qV E w : ℂ) ^ (i * (b - j)) := by
  have hle : intSub a b w ≤ latM ϖ m := fun X hX => by
    refine ⟨i1.mul hX, ?_⟩
    have e : ϖ • (X * (m.2⁻¹).val) = X * (ϖ • (m.2⁻¹).val) := (Matrix.mul_smul _ _ _).symm
    rw [e]
    exact IsInt.mul hX j2
  have := _root_.GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice E a b w (latM ϖ m) hle
  rw [_root_.GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex E a b w ϖ hϖ i j hi hj m t1 t2, GlobalTheory.T.diagonal_lattice_index_pow E a b w ϖ hϖ i j hi hj] at this
  rw [Nat.cast_pow] at this
  have e2 : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      if IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) =
      fun X => if Multiplicative.toAdd X ∈ latM ϖ m then (1 : ℂ) else 0 :=
    funext fun X => if_congr Iff.rfl rfl rfl
  rw [e2]
  exact this

theorem coef_eq (q : ℕ) (hq : q ≠ 0) (c : ℂˣ) (a b i j : ℕ) (hj : j ≤ b) :
    (c : ℂ) ^ (i * b + j * a) * ((q : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) * (q : ℂ) ^ (i * (b - j))) = coef q c a b i j := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [coef]
  congr 1
  rw [← Complex.cpow_natCast (q : ℂ), ← Complex.cpow_add _ _ hq']
  congr 1
  push_cast [Nat.cast_sub hj]
  ring

theorem hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  unfold hint
  rw [finsum_zero, mul_zero]

set_option maxHeartbeats 1600000 in
theorem ct_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (c : ℂˣ)
    (ϖ : w.adicCompletion E) (hw : IsSplitAt w) (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) :
    ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k m =
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) := by
  rw [_root_.GlobalTheory.CompanionTheory.CtS.ctT_split_eq E n a b h w _ ϖ hw hϖ k m]
  by_cases hP : ∃ p ∈ pairs a b k, Tj ℂ a (Ov E w) ϖ p.1 m.1 ≠ 0 ∧ Tj ℂ b (Ov E w) ϖ p.2 m.2 ≠ 0
  · obtain ⟨⟨i, j⟩, hp, h1, h2⟩ := hP
    obtain ⟨hij, hi, hj⟩ : i + j = k ∧ i ≤ a ∧ j ≤ b := by
      exact mem_pairs.1 hp
    simp only at h1 h2
    have c1 := _root_.GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w a i ϖ hϖ hi m.1
    have c2 := _root_.GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w b j ϖ hϖ hj m.2
    rw [c1] at h1
    rw [c2] at h2
    obtain ⟨i1, i2, i3⟩ : IsInt w m.1.val ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ ordL m.1.val.det = (i : ℤ) := by
      by_contra hc; exact h1 (if_neg hc)
    obtain ⟨j1, j2, j3⟩ : IsInt w m.2.val ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ ordL m.2.val.det = (j : ℤ) := by
      by_contra hc; exact h2 (if_neg hc)
    have hfun : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) =
        fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
          IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m]
      have e : ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) := by rw [i3, j3, ← hij]; push_cast; rfl
      by_cases hX : IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val))
      · rw [if_pos ⟨i1, j1, hX.1, i2, j2, hX.2, e⟩, if_pos hX]
      · rw [if_neg fun hc => hX ⟨hc.2.2.1, hc.2.2.2.2.2.1⟩, if_neg hX]
    have u1 : Tj ℂ a (Ov E w) ϖ i m.1 = 1 := by rw [c1, if_pos ⟨i1, i2, i3⟩]
    have u2 : Tj ℂ b (Ov E w) ϖ j m.2 = 1 := by rw [c2, if_pos ⟨j1, j2, j3⟩]
    have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by rw [u1]; exact one_ne_zero
    have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by rw [u2]; exact one_ne_zero
    rw [hfun, hint_lat E a b w ϖ hϖ i j hi hj m i1 j2 t1 t2, _root_.GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist E a b w c i j m i3 j3, _root_.GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value E a b w i j m i3 j3,
      coef_eq _ (qV_ne_zero w) c a b i j hj, Finset.sum_eq_single_of_mem (⟨i, j⟩ : ℕ × ℕ) hp]
    · simp [u1, u2]
    · rintro ⟨i', j'⟩ hp' hne
      obtain ⟨hij', hi', hj'⟩ : i' + j' = k ∧ i' ≤ a ∧ j' ≤ b := by
        exact mem_pairs.1 hp'
      have : i' ≠ i := fun e => hne (by subst e; congr; omega)
      have u : Tj ℂ a (Ov E w) ϖ i' m.1 = 0 := by
        rw [_root_.GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w a i' ϖ hϖ hi' m.1, if_neg]
        rintro ⟨-, -, e⟩
        exact this (by rw [i3] at e; exact_mod_cast e.symm)
      simp [u]
  · push_neg at hP
    have hz : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) = fun _ => 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m, if_neg]
      rintro ⟨i1, j1, -, i2, j2, -, e⟩
      obtain ⟨i, hi, i3⟩ := _root_.GlobalTheory.CompanionTheory.CtS.ordL_det_range E w a ϖ hϖ m.1 i1 i2
      obtain ⟨j, hj, j3⟩ := _root_.GlobalTheory.CompanionTheory.CtS.ordL_det_range E w b ϖ hϖ m.2 j1 j2
      have hp : (⟨i, j⟩ : ℕ × ℕ) ∈ pairs a b k := by
        have : i + j = k := by rw [i3, j3] at e; exact_mod_cast e
        exact mem_pairs.2 ⟨this, hi, hj⟩
      have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by
        rw [_root_.GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w a i ϖ hϖ hi m.1, if_pos ⟨i1, i2, i3⟩]; exact one_ne_zero
      have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by
        rw [_root_.GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w b j ϖ hϖ hj m.2, if_pos ⟨j1, j2, j3⟩]; exact one_ne_zero
      exact t2 (hP (i, j) hp t1)
    have hs : ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      by_cases t1 : Tj ℂ a (Ov E w) ϖ p.1 m.1 = 0
      · simp [t1]
      · simp [hP p hp t1]
    rw [hz, hs, hint_zero, mul_zero, mul_zero]

theorem ctSat : CtSat := by
  intro E _ _ _ n a b h w ν c V _ _ ρ x Ba Bb hw hν hs ϖ hϖ k hk
  subst hν
  have hF : ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k = fun m =>
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) :=
    funext fun m => ct_eq E n a b h w c ϖ hw hϖ k hk m
  rw [hF, _root_.GlobalTheory.CompanionTheory.CtS.HeckeSum.heckeVec_Tj_sum E a b w ϖ hϖ, _root_.GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join _ n a b c Ba Bb (qV_ne_zero w) h hs.2.1 hs.2.2.1 k hk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨-, hi, hj⟩ : p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
    exact mem_pairs.1 hp
  rw [hs.2.2.2 ϖ hϖ p.1 hi p.2 hj, smul_smul]

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSmoothModuleUnique
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CuspIrred

open scoped InnerProductSpace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem continuous_infGL' : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem map_closure_le {C S : Submodule ℂ (L2 (latticeGL E a) μ)} (hC : C = S.topologicalClosure)
    (T : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) (h : ∀ F ∈ S, T F ∈ C) {v : L2 (latticeGL E a) μ}
    (hv : v ∈ C) : T v ∈ C := by
  have hcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := hC ▸ Submodule.isClosed_topologicalClosure _
  have hle : S.topologicalClosure ≤ C.comap (T : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
    Submodule.topologicalClosure_minimal _ h (hcl.preimage T.continuous)
  exact hle (hC ▸ hv)

theorem R_curve_mem {W : Submodule ℂ (Sm E a)} (hs : _root_.GlobalTheory.CuspRep.IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) {c : ℝ → GL (Fin a) (Cinf E)} {X : GlobalTheory.CuspRep.Lie E a}
    (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) {φ : Sm E a} (hφ : φ ∈ W) (h : MemL2Quotient (latticeGL E a) μ φ.1) (t : ℝ) :
    R (latticeGL E a) μ (infGL E a (c t)) h.toL2 ∈ (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hCcl : IsClosed (C : Set (L2 (latticeGL E a) μ)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace C := hCcl.completeSpace_coe
  let ψ : ℕ → Sm E a := fun k => ((lie E a X) ^ k) φ
  have hψ0 : ψ 0 = φ := rfl
  have hψs : ∀ k, ψ (k + 1) = lie E a X (ψ k) := fun k => by
    simp only [ψ, pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, ψ k ∈ W := fun k => by
    induction k with
    | zero => exact hφ
    | succ k ih => rw [hψs]; exact hs (.lie X) _ ih
  have hM : ∀ k, MemL2Quotient (latticeGL E a) μ (ψ k).1 := fun k => (hW _ (hmem k)).2
  have hcont : ∀ k, Continuous (ψ k).1 := fun k => ContAut.continuous_of_isOpen_stab E a _ (hW _ (hmem k)).1.level
  let F : ℕ → ℝ → L2 (latticeGL E a) μ := fun k t => R (latticeGL E a) μ (infGL E a (c t)) (hM k).toL2
  obtain ⟨M, B, hb⟩ := _root_.GlobalTheory.CompanionTheory.AnalyticBound.factorial_bound E a μ W hs hW φ hφ X
  have hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t := fun k t =>
    _root_.GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R (GA E a) (latticeGL E a) μ (ψ k).1 (ψ (k + 1)).1 (hM k) (hM (k + 1)) (fun t => infGL E a (c t))
      (hcont k) (hcont (k + 1)) (continuous_infGL'.comp hc) (by simp [h0]) (fun s t => by simp [hadd])
      (fun g => by
        have := hasDerivAt_curve (ψ k) g c X h0 hX
        rw [hψs]
        exact this) t
  have hn : ∀ k t, ‖F k t‖ ≤ M * B ^ k * (k.factorial : ℝ) := fun k t => (norm_R _ _).trans_le (hb k (hM k))
  have hF0 : ∀ k, F k 0 ∈ C := fun k => by
    have : F k 0 = (hM k).toL2 := by simp [F, h0]
    rw [this]
    exact Submodule.le_topologicalClosure _ (toL2_mem_classes (hmem k) (hM k))
  have hperp : F 0 t ∈ Cᗮᗮ := (Submodule.mem_orthogonal _ _).2 fun u hu =>
    GlobalTheory.T.analytic_orthogonal_vanishing _ F M B u hd hn (fun k => (Submodule.mem_orthogonal' _ _).1 hu _ (hF0 k)) t
  rw [Submodule.orthogonal_orthogonal] at hperp
  have e : (hM 0).toL2 = h.toL2 := rfl
  exact e ▸ hperp

theorem isSubrep_closure {W : Submodule ℂ (Sm E a)} (hs : _root_.GlobalTheory.CuspRep.IsStable W)
    (hW : ∀ φ ∈ W, IsAutForm φ ∧ MemL2Quotient (latticeGL E a) μ φ.1) :
    IsSubrep (R (latticeGL E a) μ) (classes W μ).topologicalClosure := by
  set C := (classes W μ).topologicalClosure with hCdef
  have hcls : ∀ F ∈ classes W μ, ∃ φ ∈ W, ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, F = h.toL2 := fun F hF => by
    obtain ⟨φ, hφ, e⟩ := mem_classes.1 hF
    exact ⟨φ, hφ, (hW φ hφ).2, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (hW φ hφ).2.lift_toL2_ae_eq.symm)⟩
  have hfin : ∀ k, ∀ v ∈ C, R (latticeGL E a) μ (finGL E a k) v ∈ C := fun k v hv =>
    map_closure_le hCdef _ (fun F hF => Submodule.le_topologicalClosure _
      (R_mem_classes (fun φ hφ => hs (.fin k) φ hφ) hF)) hv
  let S : Subgroup (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (∀ v ∈ C, R (latticeGL E a) μ (infGL E a y) v ∈ C) ∧
        ∀ v ∈ C, R (latticeGL E a) μ (infGL E a y⁻¹) v ∈ C}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => ⟨fun v hv => by
          rw [map_mul, map_mul]; exact hx.1 _ (hy.1 v hv), fun v hv => by
          rw [_root_.mul_inv_rev, map_mul, map_mul]; exact hy.2 _ (hx.2 v hv)⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩ }
  have hS : S = ⊤ := _root_.GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf E a S fun c X hc h0 hadd hX t => by
    have key : ∀ t, ∀ v ∈ C, R (latticeGL E a) μ (infGL E a (c t)) v ∈ C := fun t v hv =>
      map_closure_le hCdef _ (fun F hF => by
        obtain ⟨φ, hφ, h, rfl⟩ := hcls F hF
        exact R_curve_mem hs hW hc h0 hadd hX hφ h t) hv
    have hinv : (c t)⁻¹ = c (-t) := inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
    exact ⟨key t, by rw [show (c t)⁻¹ = c (-t) from hinv]; exact key (-t)⟩
  refine ⟨Submodule.isClosed_topologicalClosure _, fun g v hv => ?_⟩
  have hy : GeneralLinearGroup.map (pInf E) g ∈ S := hS ▸ Subgroup.mem_top _
  rw [← infGL_mul_finGL g, map_mul]
  exact hy.1 _ (hfin _ v hv)

theorem irred_module : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → W ≠ ⊥ → (∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → ∀ φ : Sm E a, (IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) → φ ∈ W := by
  rintro E _ _ _ a μ _ _ H hH hi W hs hne hW φ ⟨hφ, -, h, hh⟩
  have hW' : ∀ ψ ∈ W, IsAutForm ψ ∧ MemL2Quotient (latticeGL E a) μ ψ.1 := fun ψ hψ =>
    ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2.choose⟩
  have hsub := isSubrep_closure (μ := μ) hs hW'
  have hle : (classes W μ).topologicalClosure ≤ H := by
    refine Submodule.topologicalClosure_minimal _ (fun F hF => ?_) hi.1.1
    obtain ⟨ψ, hψ, e⟩ := mem_classes.1 hF
    obtain ⟨h', hh'⟩ := (hW ψ hψ).2.2
    rwa [show F = h'.toL2 from l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h'.lift_toL2_ae_eq.symm)]
  have hcl : (classes W μ).topologicalClosure = H := by
    refine (hi.2.2 _ hle hsub).resolve_left fun h0 => ?_
    obtain ⟨ψ, hψ, hψ0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨h', -⟩ := (hW ψ hψ).2.2
    refine toL2_ne_zero h' (ContAut.continuous_of_isOpen_stab E a ψ (hW ψ hψ).1.1.level)
      (fun e => hψ0 (Subtype.ext e)) ?_
    have : h'.toL2 ∈ (classes W μ).topologicalClosure :=
      Submodule.le_topologicalClosure _ (toL2_mem_classes hψ h')
    rw [h0] at this
    exact this
  exact _root_.GlobalTheory.CompanionTheory.IrredMod.mem_of_toL2_mem E a μ H hH hi W hs (fun ψ hψ => ⟨(hW ψ hψ).1.1, (hW ψ hψ).2.2⟩) hcl φ hφ.1 h hh

end GlobalTheory.CompanionTheory.CuspIrred
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBUnique
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isB_unique : ∀ {D : D7} {p : ℕ} {e : AE D} {g : G D p} {x x' : hermS D p e} (h : IsB e g x) (h' : IsB e g x'), x = x' := by
  intro D p e g x x' h h'
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨-, hx'⟩ := h'
  have key : ∀ z : hermS D p e, mm (lowC g) z.1.1 = e • lowD g → z.1.1 = mm y (e • lowD g) := by
    intro z hz
    have hs : e • z.1.1 = z.1.1 := z.2
    rw [← hz]
    show z.1.1 = y * (lowC g * z.1.1)
    rw [← Matrix.mul_assoc]
    have hy' : y * lowC g = e • (1 : Mx D p p) := hy
    rw [hy', Matrix.smul_mul, Matrix.one_mul, hs]
  exact Subtype.ext (Subtype.ext ((key x hx).trans (key x' hx').symm))

end GlobalTheory.CompanionTheory.MuC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSVal
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
namespace GlobalTheory.CompanionTheory.MuC

theorem isClosed_hermS_val (D : D7) (p : ℕ) (e : AE D) :
    IsClosed ((hermS D p e : AddSubgroup (hermA D p)) : Set (hermA D p)) := by
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hc : Continuous fun x : hermA D p => e • (x : Formalism.IndefR.Datum.Mx D p p) :=
    (continuous_const_smul e).comp continuous_subtype_val
  exact isClosed_eq hc continuous_subtype_val


set_option synthInstance.maxHeartbeats 400000 in
theorem hermS_facts : ∀ (D : D7) (p : ℕ) (e : AE D), LocallyCompactSpace (hermS D p e) ∧ T2Space (hermS D p e) ∧
    SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e) ∧ IsTopologicalAddGroup (hermS D p e) := by
  intro D p e
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hS := isClosed_hermS_val D p e
  have hA : IsClosed ((hermA D p : AddSubgroup (Formalism.IndefR.Datum.Mx D p p)) : Set (Formalism.IndefR.Datum.Mx D p p)) :=
    GlobalTheory.CompanionTheory.HermVol.isClosed_hermA
  haveI : LocallyCompactSpace (Formalism.IndefR.Datum.Mx D p p) :=
    show LocallyCompactSpace (Fin p → Fin p → AE D) from inferInstance
  haveI : SecondCountableTopology (Formalism.IndefR.Datum.Mx D p p) :=
    show SecondCountableTopology (Fin p → Fin p → AE D) from inferInstance
  haveI : BorelSpace (Formalism.IndefR.Datum.Mx D p p) := by
    first
    | exact show BorelSpace (Fin p → Fin p → AE D) from inferInstance
    | exact ⟨rfl⟩
    | exact Matrix.borelSpace
  haveI : SecondCountableTopology (hermA D p) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermA D p : Set (Formalism.IndefR.Datum.Mx D p p))) from inferInstance
  haveI : SecondCountableTopology (hermS D p e) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermS D p e : Set (hermA D p))) from inferInstance
  haveI : LocallyCompactSpace (hermA D p) := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end GlobalTheory.CompanionTheory.MuC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRhoRight
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isRho_right {D : D7} {p : ℕ} {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    IsRho (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), ?_⟩
  intro q hq a ha g
  have := hf.2 q hq a ha (g * x)
  simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.MuC
end

