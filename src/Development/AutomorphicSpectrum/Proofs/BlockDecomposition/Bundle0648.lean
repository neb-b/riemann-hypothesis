module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRange
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ
  obtain ⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple F E σ hCM M n dx hdx.1
  obtain ⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod F E σ hCM n db hdb.1
  obtain ⟨k, P, Q, hP, hQ, hsum⟩ := id hΦ
  have hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat
      (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X)) := fun i =>
    GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl
  have hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
      (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) *
        starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b)) := by
    intro i b
    let A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun x =>
      P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
          gramR (Ainf F) σ J x)))
    let B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun y =>
      Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
          gramR (Af F) σ J y)))
    let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun z => A z.1 * B z.2
    have e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
        ∫ X, G (projInf X, projFin X) ∂dx := by
      unfold starN
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show _ * _ = G _
      rw [_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split F E σ hCM M J n ψ b X]
      simp only [G, A, B]
      ring
    have e2 := hme.integral_map (μ := dx) G
    have e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂ := integral_prod_mul A B
    rw [e1]
    refine e2.symm.trans ?_
    rw [hmap, integral_smul_measure, e3, Complex.real_smul]
    rfl
  have hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db := by
    intro i
    have hA := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)
    have hB := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)
    have hAB := hA.mul_prod hB
    have hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n =>
        starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2)
        (db.map (fun b => (hermInf σ b, hermFin σ b))) := by
      rw [hmap']
      exact hAB.smul_measure hc'
    have := (hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hfac i b).symm
  have hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b := by
    funext b
    unfold starN
    rw [← integral_finsetSum _ fun i _ => _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Φ X * _ = _
    rw [hsum, Finset.sum_mul]
  rw [hdec]
  exact integrable_finsetSum _ fun i _ => hpure i

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSymplecticFormSqNegOne
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

open GlobalTheory.StdUnn.Gen GlobalTheory.StdUnn.Model

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem standard_symplectic_form_sq_neg_one :
    (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) R) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.neg_apply, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

theorem flip_J {J M A : Matrix (Fin (n + n)) (Fin (n + n)) R} (h : A * J * M = J) (hJ : J * J = -1) :
    M * J * A = J := by
  have h1 : (-(J * A * J)) * M = 1 := by
    calc (-(J * A * J)) * M = -(J * (A * J * M)) := by simp only [neg_mul, mul_assoc]
      _ = 1 := by rw [h, hJ, neg_neg]
  have h2 : M * (-(J * A * J)) = 1 := mul_eq_one_comm.1 h1
  calc M * J * A = -((M * (-(J * A * J))) * J) * (J * J) * (-1) * (-1) * (-1) * 0 + M * J * A := by simp
    _ = J := by
      have h3 : M * J * A * (J * J) = -J := by
        calc M * J * A * (J * J) = (M * (J * A * J)) * J := by simp only [mul_assoc]
          _ = -J := by
            have : M * (J * A * J) = -1 := by
              have := congrArg Neg.neg h2
              simpa using this
            rw [this]; simp
      rw [hJ] at h3
      simpa using h3

theorem symplectic_lower_block_relation {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d * blk4 0 1 (-1) 0 * blk4 a' b' c' d' = blk4 0 1 (-1) 0) : c * d' = d * b' := by
  simp only [submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  have h4 := (blockMatrixTwoByTwoFin_injective h).2.2.2
  exact (neg_add_eq_zero.1 h4).symm

theorem mul_smul_of_idem {e : R} (he : e * e = e) {y c : Matrix (Fin n) (Fin n) R}
    (hy : y * c = e • (1 : Matrix (Fin n) (Fin n) R)) : c * (e • y) = e • (1 : Matrix (Fin n) (Fin n) R) := by
  have he0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have he0' : (1 - e) * e = 0 := by rw [mul_comm, he0]
  have he1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, he0, sub_zero]
  have h1 : (e • y + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) *
      (e • c + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul, hy, smul_smul,
      he, he0, he0', he1, zero_smul, add_zero, zero_add]
    rw [← add_smul, add_sub_cancel, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  have h3 : e • (c * y) + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) = 1 := by
    simpa only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul, smul_smul,
      he, he0, he0', he1, zero_smul, add_zero, zero_add] using h2
  rw [Matrix.mul_smul, eq_sub_of_add_eq h3, sub_smul, one_smul]
  abel

end Ring

theorem herm_core {A : Type} [Ring A] {E w c d c' d' w' : A} (hwc : w * c = E) (hcw : c' * w' = E)
    (H : c * d' = d * c') (hw : w * E = w) (hw' : E * w' = w') (hd : E * d = d * E)
    (hd' : E * d' = d' * E) : d' * w' = w * d := by
  calc d' * w' = d' * (E * w') := by rw [hw']
    _ = (E * d') * w' := by rw [hd', mul_assoc]
    _ = w * (c * d') * w' := by rw [← hwc]; simp only [mul_assoc]
    _ = w * d * (c' * w') := by rw [H]; simp only [mul_assoc]
    _ = w * (E * d) := by rw [hcw, mul_assoc, ← hd]
    _ = w * d := by rw [← mul_assoc, hw]

theorem cell_core_ring {R : Type} [CommRing R] {n : ℕ} {s : R → R}
    (ad : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R)
    (ad_mul : ∀ x y, ad (x * y) = ad y * ad x) (ad_smul : ∀ (a : R) x, ad (a • x) = s a • ad x)
    (ad_one : ad 1 = 1) {e : R} (he : e * e = e) (hc : s e = e) {y c d : Matrix (Fin n) (Fin n) R}
    (hy : y * c = e • (1 : Matrix (Fin n) (Fin n) R)) (H : c * ad d = d * ad c) :
    e • ((e • y) * d) = (e • y) * d ∧ ad ((e • y) * d) = (e • y) * d ∧ c * ((e • y) * d) = e • d := by
  have hcw : c * (e • y) = e • (1 : Matrix (Fin n) (Fin n) R) := mul_smul_of_idem he hy
  have hwc : (e • y) * c = e • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.smul_mul, hy, smul_smul, he]
  have hw : e • (e • y) = e • y := by rw [smul_smul, he]
  have haw : e • ad (e • y) = ad (e • y) := by
    have := ad_smul e (e • y)
    rw [hw, hc] at this
    exact this.symm
  have hawc : ad c * ad (e • y) = e • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← ad_mul, hwc, ad_smul, ad_one, hc]
  have hidem : e • ((e • y) * d) = (e • y) * d := by rw [← Matrix.smul_mul, hw]
  have hcomm : ∀ z : Matrix (Fin n) (Fin n) R,
      (e • (1 : Matrix (Fin n) (Fin n) R)) * z = z * (e • (1 : Matrix (Fin n) (Fin n) R)) := fun z => by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  refine ⟨hidem, ?_, ?_⟩
  · rw [ad_mul]
    refine herm_core hwc hawc H ?_ ?_ (hcomm d) (hcomm (ad d))
    · rw [Matrix.mul_smul, mul_one, hw]
    · rw [Matrix.smul_mul, one_mul, haw]
  · rw [← mul_assoc, hcw, Matrix.smul_mul, one_mul]

variable {D : D7} {p : ℕ}

theorem mat_J_adj (g : G D p) :
    mat g * blk4 0 1 (-1) 0 * adj (mat g) = (blk4 0 1 (-1) 0 : Mx D (p + p) (p + p)) := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D p) * mat g = JR (AF D.host.F) (Jst D p) := g.2
  rw [JR_Jst] at h
  exact flip_J h standard_symplectic_form_sq_neg_one

theorem lowC_mul_adj_lowD (g : G D p) : lowC g * adj (lowD g) = lowD g * adj (lowC g) := by
  obtain ⟨a, b, c, d, hM⟩ := exists_blockMatrixTwoByTwoFin_eq (mat g)
  have hc : lowC g = c := by
    ext i j
    simp only [lowC, hM, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]
  have hd : lowD g = d := by
    ext i j
    simp only [lowD, hM, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]
  have h := mat_J_adj g
  rw [hM, adelicConjTranspose_blockMatrixTwoByTwoFin] at h
  rw [hc, hd]
  exact symplectic_lower_block_relation h

theorem exists_isB : ∀ {D : D7} {p : ℕ} {e : AE D} (he : e * e = e) (hc : cA D e = e) {g : G D p}
    (hg : InCell e g), ∃ x, IsB e g x := by
  intro D p e he hc g hg
  obtain ⟨y, hy⟩ := id hg
  obtain ⟨h1, h2, h3⟩ := cell_core_ring (R := AE D) (n := p) (s := cA D) adj adj_mul adj_smul adj_one he hc
    (y := y) (c := lowC g) (d := lowD g) hy (lowC_mul_adj_lowD g)
  exact ⟨⟨⟨(e • y) * lowD g, h2⟩, h1⟩, hg, h3⟩

end GlobalTheory.CompanionTheory.MuC

end
end

