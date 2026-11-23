module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLevi

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem locMat_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL (Fin n) (Fv F v)) :
    (LeviAtPlace.locMat h t J g)ᵀ * J.map (inclR (Fv F v)) * (LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ) =
      J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, LeviAtPlace.locMat, pairMat_snd]
  have hs2 : ((LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, LeviAtPlace.locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, LeviAtPlace.locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, LeviAtPlace.locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h'
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨⟨adelicGL h t G.W.J hJ h', lift_unitary v σ G.W.J _
    (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew h')⟩, lift_sub_one_at v _, ?_⟩
  change (lift v (LeviAtPlace.locMat h t G.W.J h')).map (piW t) = h'.1
  have key : (lift v (LeviAtPlace.locMat h t G.W.J h')).map (piW t) =
      (LeviAtPlace.locMat h t G.W.J h').map (splitProj t) := by
    conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J h'), Matrix.map_map]
    rfl
  rw [key]
  exact pairMat_fst h t _ _

end GlobalTheory.SkewLevi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Matrix

namespace GlobalTheory.SkewSplitSurj

open GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem locMat_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL (Fin n) (Fv F v)) :
    (GlobalTheory.LeviAtPlace.locMat h t J g)ᵀ * J.map (inclR (Fv F v)) *
      (GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ) = J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, GlobalTheory.LeviAtPlace.locMat, pairMat_snd]
  have hs2 : ((GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, GlobalTheory.LeviAtPlace.locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, GlobalTheory.LeviAtPlace.locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

end GlobalTheory.SkewSplitSurj


open GlobalTheory.SkewSplitSurj in
theorem GlobalTheory.SkewSplitSurj.exists_locMat_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c x : GL (Fin d) (Fv F v)),
    ∃ h ∈ UAt σ W (evFin F v), locMat t c h = x := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v t c x
  have hcm := hB.cm
  have hJ : IsUnit (W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
    have h1 : W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show W.J.map t = (t : E →+* Fv F v).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  set g : GL (Fin d) (Fv F v) := c * x * c⁻¹ with hg
  let hU : UA σ W.J := ⟨GlobalTheory.LeviAtPlace.adelicGL hcm t W.J hJ g,
    GlobalTheory.LeviAtPlace.lift_unitary v σ W.J _ (locMat_unitary_skew hcm t W.J hJ hW.skew g)⟩
  have hmat : mat hU = GlobalTheory.LeviAtPlace.lift v (GlobalTheory.LeviAtPlace.locMat hcm t W.J g) := rfl
  have hpi : (mat hU).map (piW t) = g.val := by
    have e : ∀ M : Matrix (Fin d) (Fin d) (AE F E), M.map (piW t) = (M.map (compFin F E v)).map (splitProj t) :=
      fun M => by rw [Matrix.map_map]; rfl
    rw [hmat, e, GlobalTheory.LeviAtPlace.compFin_lift]
    exact GlobalTheory.LeviAtPlace.pairMat_fst hcm t _ _
  refine ⟨hU, ?_, ?_⟩
  · show At (evFin F v) (mat hU - 1)
    rw [hmat]
    exact GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  · apply Units.ext
    rw [GlobalTheory.KSplit.locMat_val, hpi, hg]
    simp [Matrix.mul_assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

namespace GlobalTheory.DiagRowSubst

theorem diag_var (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (v : Fin N × Fin N) :
    (∑ b : Fin N, C (Matrix.diagonal d v.1 b) * X (b, v.2) : MvPolynomial (Fin N × Fin N) R) = C (d v.1) * X v := by
  simp only [Matrix.diagonal_apply, apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem weight_prod (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (m : Fin N × Fin N →₀ ℕ) :
    ∏ a, d a ^ Finsupp.weight (rowW N N) m a = m.prod (fun v e => d v.1 ^ e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [pow_ite, pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ v.1]
  simp

theorem weight_le (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a ≤ m.sum (fun _ e => e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> omega

theorem mono (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R)
    (m : Fin N × Fin N →₀ ℕ) (c : O) :
    rowSubst O N R (Matrix.diagonal d) (monomial m c) =
      monomial m (algebraMap O R c * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
  rw [weight_prod, rowSubst, aeval_monomial]
  simp_rw [diag_var, mul_pow]
  rw [Finsupp.prod_mul, monomial_eq, map_mul, map_finsuppProd]
  simp only [map_pow, MvPolynomial.algebraMap_apply, mul_assoc]

theorem rowSubst_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  intro O _ N R _ _ d D f hf
  classical
  have hL : rowSubst O N R (Matrix.diagonal d) f = ∑ m ∈ f.support,
      monomial m (algebraMap O R (AddMonoidAlgebra.coeff f m) * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [mono]
  rw [hL]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [weightedHomogeneousComponent_apply, map_sum, map_monomial, Finset.smul_sum, smul_monomial, smul_eq_mul,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_ite_eq, if_pos, mul_comm]
  rw [Fintype.mem_piFinset]
  intro a
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact (weight_le N m a).trans ((le_totalDegree hm).trans hf)

end GlobalTheory.DiagRowSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyEqEvalGenericRowSubstit
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenCoef.RowSubstSum

def evY (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+* MvPolynomial (Fin N × Fin N) R :=
  eval₂Hom (MvPolynomial.map (algebraMap O R)) (fun v => C (Y v.1 v.2))

theorem evY_genSub (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (f : MvPolynomial (Fin N × Fin N) O) : evY O N R Y (GlobalTheory.HighWt.genSub O N f) = rowSubst O N R Y f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [evY, GlobalTheory.HighWt.genSub, rowSubst, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [GlobalTheory.HighWt.genSub, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [GlobalTheory.HighWt.genSub, map_mul] at hp ⊢
    rw [hp]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [evY, rowSubst, map_sum]

theorem evY_eq_sum (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) :
    evY O N R Y P = ∑ m ∈ P.support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) (P.coeff m) := by
  simp only [evY, coe_eval₂Hom, MvPolynomial.eval₂, Finsupp.sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : (m.prod fun v k => (C (Y v.1 v.2) : MvPolynomial (Fin N × Fin N) R) ^ k) = C (m.prod fun v k => Y v.1 v.2 ^ k) := by
    simp [Finsupp.prod, map_prod, map_pow]
  rw [h, mul_comm, C_mul']

theorem main : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  intro O _ N R _ _ Y f
  rw [← evY_genSub, evY_eq_sum]

end GlobalTheory.GenCoef.RowSubstSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSum
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.RowSubstTransvection

theorem natDegree_rowGen_le (O : Type) [CommRing O] (N : ℕ) (a b : Fin N)
    (f : MvPolynomial (Fin N × Fin N) O) :
    (rowGen O (n := N) a b f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [rowGen, aeval_monomial]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h0 : (algebraMap O (Polynomial (MvPolynomial (Fin N × Fin N) O)) (f.coeff m)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add]
  have hg : ∀ v : Fin N × Fin N, (Polynomial.C (X v : MvPolynomial (Fin N × Fin N) O) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)).natDegree ≤ 1 := by
    intro v
    split_ifs
    · refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_C]
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C]
      simpa using Polynomial.natDegree_X_le
    · simp
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum]
  apply Finset.sum_le_sum
  intro v _
  refine (Polynomial.natDegree_pow_le).trans ?_
  simpa using Nat.mul_le_mul_left (m v) (hg v)

theorem rowSubst_transvection (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f.totalDegree ≤ D) :
    rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  have key : (rowSubst O N R (Matrix.transvection a b r)).toRingHom =
      (Polynomial.evalRingHom (C r : MvPolynomial (Fin N × Fin N) R)).comp
        ((Polynomial.mapRingHom (MvPolynomial.map (σ := Fin N × Fin N) (algebraMap O R))).comp
          (rowGen O (n := N) b a).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowSubst, rowGen, MvPolynomial.algebraMap_eq]
    · intro v
      simp [rowSubst, rowGen, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
      by_cases h : v.1 = a
      · have h' : a = v.1 := h.symm
        simp only [h', true_and, if_true]
        simp [apply_ite C, ite_mul, Finset.sum_ite_eq']
        ring
      · have h' : ¬ a = v.1 := fun e => h e.symm
        simp [h, h']
  have h1 := DFunLike.congr_fun key f
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
    Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom] at h1
  rw [h1, Polynomial.eval_eq_sum_range' (n := D + 1)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_map, smul_eq_C_mul, C_pow, mul_comm]
    rfl
  · exact Nat.lt_succ_of_le ((Polynomial.natDegree_map_le).trans ((natDegree_rowGen_le O N b a f).trans hf))

end GlobalTheory.RowSubstTransvection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiPlaceStep
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.Places

section One

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_hwSub_iff (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub a μ ↔ (∀ c, a (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → a (Eab c d) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem hw_comm {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {L : Module.End ℂ V} (h : ∀ Z v, L (a Z v) = a Z (L v))
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub a μ) : L v ∈ hwSub a μ := by
  rw [mem_hwSub_iff] at hv ⊢
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · rw [← h, hv.1 c, map_smul]
  · rw [← h, hv.2 c d hcd, map_zero]

end One

section Quad

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem qop_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) (α β : ℂ)
    (a b : ι) {v : M} (hv : v ∈ H) : qop F α β a b v ∈ H := by
  unfold qop
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply]
  refine H.sub_mem (H.sub_mem (H.sum_mem fun c _ => hF _ _ _ (hF _ _ _ hv)) (H.smul_mem _ (hF _ _ _ hv))) ?_
  by_cases hab : a = b
  · simpa [hab] using H.smul_mem β hv
  · simp [hab]

theorem negT_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) :
    ∀ a b, ∀ u ∈ H, negT F a b u ∈ H := fun a b u hu => by
  simp only [negT, LinearMap.neg_apply]
  exact H.neg_mem (hF b a u hu)

end Quad

theorem multi_place_step : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (α β α' β' : T → ℂ), ∃ B : ℚ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ N N' : Submodule ℂ V, N < N' →
    (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') → (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) N N') →
    ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) ∧ ∃ v ∈ N', (∀ w, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
  intro T _ _ R S α β α' β'
  have hk := fun w => _root_.GlobalTheory.HoweR.exists_hwSub_of_quadMod (R w) (S w) (α w) (β w) (α' w) (β' w)
  choose Bw hBw using hk
  refine ⟨∑ w, |Bw w|, ?_⟩
  intro V _ _ a hG hc N N' hNN' hsN hsN' hQ
  have hB : ∀ w, |Bw w| ≤ ∑ w, |Bw w| := fun w =>
    Finset.single_le_sum (f := fun w => |Bw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  have h0 : (0 : ℚ) ≤ ∑ w, |Bw w| := Finset.sum_nonneg fun w _ => abs_nonneg (Bw w)
  have key : ∀ s : Finset T, ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ ∑ w, |Bw w|) ∧
      ∃ v ∈ N', (∀ w ∈ s, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨v, hv, hvN⟩ := SetLike.exists_of_lt hNN'
      exact ⟨fun _ _ => 0, fun _ _ => by simpa using h0, v, hv, by simp, hvN⟩
    | insert w s hws ih =>
      obtain ⟨μ, hμB, v, hvN', hvs, hvN⟩ := ih
      let H : Submodule ℂ V := ⨅ w' ∈ s, hwSub (a w') (μ w')
      have memH : ∀ u, u ∈ H ↔ ∀ w' ∈ s, u ∈ hwSub (a w') (μ w') := fun u => by
        simp only [H, Submodule.mem_iInf]
      have sH : ∀ Z, ∀ u ∈ H, a w Z u ∈ H := fun Z u hu => by
        rw [memH] at hu ⊢
        intro w' hw'
        exact hw_comm (fun Z' x => hc w w' (fun e => hws (e ▸ hw')) Z Z' x) (hu w' hw')
      have sU : ∀ c d, ∀ u ∈ H, units (a w) c d u ∈ H := fun c d u hu => sH _ u hu
      have hlt : N ⊓ H < N' ⊓ H := by
        refine lt_of_le_of_ne (inf_le_inf_right _ hNN'.le) fun e => hvN ?_
        have : v ∈ N' ⊓ H := ⟨hvN', (memH v).2 hvs⟩
        rw [← e] at this
        exact this.1
      have hS1 : Stab (a w) (N ⊓ H) := fun Z u hu => ⟨hsN w Z u hu.1, sH Z u hu.2⟩
      have hS2 : Stab (a w) (N' ⊓ H) := fun Z u hu => ⟨hsN' w Z u hu.1, sH Z u hu.2⟩
      have hQ' : QuadMod (a w) (α w) (β w) (α' w) (β' w) (N ⊓ H) (N' ⊓ H) := fun c d u hu =>
        ⟨⟨(hQ w c d u hu.1).1, qop_mem _ H sU _ _ c d hu.2⟩,
          ⟨(hQ w c d u hu.1).2, qop_mem _ H (negT_mem _ H sU) _ _ c d hu.2⟩⟩
      obtain ⟨ν, hνB, u, huN', huhw, huN⟩ := hBw w V (a w) (hG w) _ _ hlt hS1 hS2 hQ'
      refine ⟨Function.update μ w ν, fun w' c => ?_, u, huN'.1, fun w' hw' => ?_, fun h => huN ⟨h, huN'.2⟩⟩
      · rcases eq_or_ne w' w with rfl | e
        · simp only [Function.update_self]
          exact (hνB c).trans ((le_abs_self _).trans (hB w'))
        · rw [Function.update_of_ne e]
          exact hμB w' c
      · rcases Finset.mem_insert.1 hw' with rfl | hw''
        · simpa using huhw
        · have hne : w' ≠ w := fun e => hws (e ▸ hw'')
          rw [Function.update_of_ne hne]
          exact (memH u).1 huN'.2 w' hw''
  obtain ⟨μ, hμ, v, hv, hvs, hvN⟩ := key Finset.univ
  exact ⟨μ, hμ, v, hv, fun w => hvs w (Finset.mem_univ w), hvN⟩

end GlobalTheory.HoweR.Places

end
end

