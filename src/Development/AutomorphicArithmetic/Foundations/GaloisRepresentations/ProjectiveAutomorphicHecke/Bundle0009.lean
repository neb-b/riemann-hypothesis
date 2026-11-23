module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocAdj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PClassFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSatVal
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
section
namespace UpperTheory.Gal.CertificateRingHomMap

universe u v

theorem extZero_holds : ExtZero := pExtZero_holds
theorem centralEig2_holds : CentralEig2 := pCentralEig2_of
theorem extEig2_holds : ExtEig2 := pExtEig2_of extZero_holds centralEig2_holds
theorem locAdj_holds : LocAdj := pLocAdj_of
theorem rootsAlg_holds : RootsAlg := pRootsAlg_of
theorem finToHecke_holds : FinToHecke := pFinToHecke_of
theorem classFin_holds : ClassFin := pClassFin_of
theorem xiScalar_holds : XiScalar := pXiScalar_of
theorem xiZeta_holds : XiZeta := pXiZeta_of xiScalar_holds
theorem intConj_holds : IntConj := pIntConj_of
theorem intSim_holds : IntSim := pIntSim_of
theorem ofUBij_holds : OfUBij := pOfUBij_of
theorem locComm_holds : LocComm := pLocComm_of
theorem locMem_holds : LocMem := pLocMem_of intConj_holds locComm_holds
theorem levOpen_holds : LevOpen := pLevOpen_of
theorem intCompact_holds : IntCompact := pIntCompact_of
theorem levCompact_holds : LevCompact := pLevCompact_of intCompact_holds intConj_holds locComm_holds levOpen_holds
theorem nhds_basis_levelSubgroup : Nbhd2 := pNbhd2_of
theorem nbhdU_holds : NbhdU := pNbhdU_of nhds_basis_levelSubgroup intConj_holds locComm_holds ofUBij_holds
theorem sphType_holds : SphType := pSphType_of intConj_holds locComm_holds
theorem stepAt_holds : StepAt := pStepAt_of locAdj_holds locComm_holds ofUBij_holds
theorem vecU_holds : VecU := pVecU_of nbhdU_holds stepAt_holds sphType_holds locComm_holds
theorem satVal_holds : SatVal := pSatVal_of
theorem kerFormU_holds : KerFormU := pKerFormU_of ofUBij_holds
theorem heckePres_holds : HeckePres := pHeckePres_of locComm_holds locMem_holds
theorem kapOf_holds : KapOf := pKapOf_of finToHecke_holds xiZeta_holds intSim_holds levOpen_holds

theorem formGU_holds : FormGU :=
  pFormGU_of extEig2_holds classFin_holds xiZeta_holds kerFormU_holds heckePres_holds satVal_holds locMem_holds locComm_holds
    levOpen_holds ofUBij_holds

theorem seedGU_holds : SeedGU :=
  seedGU_of zetaEx_holds vecU_holds sphType_holds formGU_holds kapOf_holds levOpen_holds levCompact_holds

end UpperTheory.Gal.CertificateRingHomMap
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PAutEx
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pAutEx_of :
    UpperTheory.Gal.CertificateRingHomMap.AutEx := by
  intro E _ _ τ τ₀
  obtain ⟨σ, hσ⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegreeAlt.exists_ringEquiv_comp τ τ₀
  exact ⟨σ, fun y => RingHom.congr_fun hσ y⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCharConj
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pCharConj_of :
    UpperTheory.Gal.CertificateRingHomMap.CharConj := by
  intro E _ _ _ n y P s h φ t ht
  set A : Matrix (Fin n) (Fin n) ℂ := (y : Matrix (Fin n) (Fin n) E).map φ with hAdef
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) E).map φ with hQdef
  set B : Matrix (Fin n) (Fin n) ℂ :=
    (y : Matrix (Fin n) (Fin n) E).map (NumberField.ComplexEmbedding.conjugate φ) with hBdef
  have hB : B = ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E)).map φ := by
    ext i j
    simp only [B, Matrix.map_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq,
      NumberField.IsCMField.complexEmbedding_complexConj]
  have hrel : Bᵀ * Q * A = ((s : ℚ) : ℂ) • Q := by
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map φ) h
    simp only [Matrix.map_mul] at h2
    rw [Matrix.transpose_map] at h2
    rw [hB, hQdef, hAdef, h2]
    ext i j
    simp [Matrix.map_apply]
  have hA : ((y : Matrix (Fin n) (Fin n) E).map φ).charpoly = ∏ i, (X - C (t i)) := by
    rw [Matrix.charpoly_map]; exact ht
  have hdetA : A.det ≠ 0 := by
    have hu : IsUnit (y : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [hAdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hdetQ : Q.det ≠ 0 := by
    have hu : IsUnit (P : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
    rw [hQdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hprodt : A.det = ∏ i, t i := by
    have e := congrArg (Polynomial.eval 0) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at e
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub] at e
    rw [map_zero, zero_sub, Matrix.det_neg, Fintype.card_fin] at e
    have e2 : ∏ i, -t i = (-1) ^ n * ∏ i, t i := by
      calc ∏ i, -t i = ∏ i, ((-1) * t i) := by simp
        _ = (-1) ^ n * ∏ i, t i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e2] at e
    exact mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) e
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i hi
    apply hdetA
    rw [hprodt]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hpt : ∏ i, t i ≠ 0 := hprodt ▸ hdetA
  refine ⟨ht0, ?_⟩
  rw [← Matrix.charpoly_map]
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := {z : ℂ | z ≠ 0})
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    have key : (Matrix.scalar (Fin n) z - B).det * A.det =
        z ^ n * (-1) ^ n * (Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A).det := by
      have e1 : (Matrix.scalar (Fin n) z - Bᵀ) * Q * A = Q * (z • A - ((s : ℚ) : ℂ) • 1) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_mul, sub_mul, hrel, mul_sub]
        simp [smul_mul_assoc, mul_smul_comm]
      have e2 : (Matrix.scalar (Fin n) z - B).det = (Matrix.scalar (Fin n) z - Bᵀ).det := by
        rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, Matrix.charpoly_transpose]
      have e3 : z • A - ((s : ℚ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
          z • (-(Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A)) := by
        rw [neg_sub, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
          mul_div_cancel₀ _ hz]
      have e4 := congrArg Matrix.det e1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, e3, Matrix.det_smul, Matrix.det_neg,
        Fintype.card_fin, ← e2] at e4
      apply mul_left_cancel₀ hdetQ
      linear_combination e4
    have hAev := congrArg (Polynomial.eval (((s : ℚ) : ℂ) / z)) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at hAev
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hAev
    rw [hAev, hprodt] at key
    rw [Matrix.eval_charpoly, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hfac : ∀ i, (z - ((s : ℚ) : ℂ) / t i) * t i = (z * -1) * (((s : ℚ) : ℂ) / z - t i) := by
      intro i
      field_simp [ht0 i, hz]
      ring
    have hq : (∏ i, (z - ((s : ℚ) : ℂ) / t i)) * ∏ i, t i =
        z ^ n * (-1) ^ n * ∏ i, (((s : ℚ) : ℂ) / z - t i) := by
      rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hfac i),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    exact mul_right_cancel₀ hpt (key.trans hq.symm)
  · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PEpsIff
section
noncomputable section

open NumberField

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem agree_of_adjoin {E : Type} [Field E] [NumberField E] (φ ψ : E →+* ℂ) {a b : E}
    (h : φ a = ψ a) (hb : b ∈ IntermediateField.adjoin ℚ {a}) : φ b = ψ b :=
  _root_.UpperTheory.Reformulated.B.Qk58.agree_of_adjoin φ ψ h hb

private theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z :=
  _root_.UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq hd hz

theorem pEpsIff_of : EpsIff := by
  intro E _ _ _ d x ω hd hx hω hx' τ φ
  have hτ : (τ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hc : ComplexEmbedding.conjugate τ x = -τ x := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg_of_sq hd hτ
  constructor
  · intro h
    have h' : φ ω = ComplexEmbedding.conjugate τ ω := by
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact h
    rw [agree_of_adjoin φ _ h' hx', hc]
  · intro h
    have h' : φ x = ComplexEmbedding.conjugate τ x := by rw [h, hc]
    rw [agree_of_adjoin φ _ h' hω, ComplexEmbedding.conjugate_coe_eq]

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpCore
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem symm_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {σ : ℂ ≃+* ℂ} {τ τ₀ : E →+* ℂ}
    (hσ : ∀ y, σ (τ y) = τ₀ y) :
    (σ.symm : ℂ →+* ℂ).comp τ₀ = τ ∧
      (σ.symm : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate τ₀) = ComplexEmbedding.conjugate τ := by
  constructor
  · refine RingHom.ext fun y => ?_
    simp [← hσ y]
  · refine RingHom.ext fun y => ?_
    have h1 : ComplexEmbedding.conjugate τ₀ y = τ₀ (IsCMField.complexConj E y) := by
      rw [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
    have h2 : ComplexEmbedding.conjugate τ y = τ (IsCMField.complexConj E y) := by
      rw [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
    rw [h2]
    simp [h1, ← hσ]

private theorem sum_reindex {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {σ : ℂ ≃+* ℂ} {τ τ₀ : E →+* ℂ} {x : E}
    (lam : (E →+* ℂ) → Fin n → ℕ) (hσ : ∀ y, σ (τ y) = τ₀ y) {ε : (E →+* ℂ) → ℕ}
    (hε : ∀ φ : E →+* ℂ, ε ((σ : ℂ →+* ℂ).comp φ) = if φ x = -τ x then 1 else 0) :
    ∑ φ ∈ (Finset.univ.erase τ₀).erase (ComplexEmbedding.conjugate τ₀), ε φ * ∑ j, UpperTheory.Gal.LocalSmoothExtension.conjWt σ lam φ j =
      ∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), (if φ x = -τ x then 1 else 0) * ∑ j, lam φ j := by
  obtain ⟨e1, e2⟩ := symm_comp hσ
  have hA : ∀ φ : E →+* ℂ, (σ : ℂ →+* ℂ).comp ((σ.symm : ℂ →+* ℂ).comp φ) = φ := fun φ =>
    RingHom.ext fun y => by simp
  have hB : ∀ φ : E →+* ℂ, (σ.symm : ℂ →+* ℂ).comp ((σ : ℂ →+* ℂ).comp φ) = φ := fun φ =>
    RingHom.ext fun y => by simp
  refine Finset.sum_nbij' (fun φ => (σ.symm : ℂ →+* ℂ).comp φ) (fun φ => (σ : ℂ →+* ℂ).comp φ) ?_ ?_
    (fun φ _ => hA φ) (fun φ _ => hB φ) ?_
  · intro φ hφ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hφ ⊢
    exact ⟨fun h => hφ.1 ((hA φ).symm.trans (by rw [h, ← e2, hA])),
      fun h => hφ.2 ((hA φ).symm.trans (by rw [h, ← e1, hA]))⟩
  · intro φ hφ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hφ ⊢
    exact ⟨fun h => hφ.1 ((hB φ).symm.trans (by rw [h, e2])),
      fun h => hφ.2 ((hB φ).symm.trans (by rw [h, e1]))⟩
  · intro φ _
    have h := hε ((σ.symm : ℂ →+* ℂ).comp φ)
    rw [hA] at h
    rw [h]
    rfl

theorem UpperTheory.Gal.CertificateRingHomMap.pExpCore_of :
    UpperTheory.Gal.CertificateRingHomMap.ExpSum → UpperTheory.Gal.CertificateRingHomMap.ExpCore := by
  intro hS E _ _ _ n d x hd hx W m hm
  refine ⟨fun τ a b hab => ?_, fun τ τ₀ σ hσ ε hε k => ?_⟩
  · unfold lamOf
    split_ifs
    · exact le_rfl
    · exact Int.toNat_le_toNat (add_le_add_left ((W _).anti hab) _)
  · obtain ⟨e1, e2⟩ := symm_comp hσ
    have hs := hS E n d x hd hx W m hm τ
    rw [← sum_reindex (lamOf W m) hσ hε] at hs
    have c1 : ∀ i, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) τ₀ i = lamOf W m τ i := fun i => by
      show lamOf W m ((σ.symm : ℂ →+* ℂ).comp τ₀) i = _
      rw [e1]
    have c2 : ∀ i, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) (ComplexEmbedding.conjugate τ₀) i =
        lamOf W m (ComplexEmbedding.conjugate τ) i := fun i => by
      show lamOf W m ((σ.symm : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate τ₀)) i = _
      rw [e2]
    generalize hR : (∑ φ ∈ (Finset.univ.erase τ₀).erase (ComplexEmbedding.conjugate τ₀),
      ε φ * ∑ j, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) φ j) = R at hs
    have hk : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    rcases InfinitePlace.embedding_mk_eq τ with hv | hv
    · have hc : ComplexEmbedding.conjugate τ ≠ (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding := by
        rw [InfinitePlace.mk_conjugate_eq, hv]; exact conjugate_ne τ
      have l1 : ∀ i, lamOf W m τ i = m (InfinitePlace.mk τ) := fun i => if_pos hv.symm
      have l2 : ∀ i, ((lamOf W m (ComplexEmbedding.conjugate τ) i : ℕ) : ℤ) =
          (W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m (ComplexEmbedding.conjugate τ) i =
          ((W (InfinitePlace.mk (ComplexEmbedding.conjugate τ))).w i +
            m (InfinitePlace.mk (ComplexEmbedding.conjugate τ))).toNat := if_neg hc
        rw [h, InfinitePlace.mk_conjugate_eq]
        exact Int.toNat_of_nonneg (hm _ _)
      have hw : W.at τ = W (InfinitePlace.mk τ) := by
        have h := W.at_embedding (InfinitePlace.mk τ)
        rwa [hv] at h
      refine ⟨fun i => (m (InfinitePlace.mk τ) + R) +
        (∑ j ∈ Finset.univ.erase i, lamOf W m (ComplexEmbedding.conjugate τ) j + (i : ℕ)), k,
        Or.inr ⟨m (InfinitePlace.mk τ), fun i => by rw [c1, l1], fun i => ?_⟩, ?_⟩
      · simp only [c2, hR]
      · have hsum : ((∑ j ∈ Finset.univ.erase k, lamOf W m (ComplexEmbedding.conjugate τ) j : ℕ) : ℤ) =
            ∑ j ∈ Finset.univ.erase k, ((W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun j _ => l2 j
        have h3 := Finset.add_sum_erase Finset.univ
          (fun j => (W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) (Finset.mem_univ k)
        have h4 : ∑ j, ((W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) =
            ∑ j, (W (InfinitePlace.mk τ)).w j + (n : ℤ) * m (InfinitePlace.mk τ) := by
          rw [Finset.sum_add_distrib]
          simp
        rw [if_pos hv.symm] at hs
        rw [hw, ← hs]
        push_cast at hsum ⊢
        rw [hsum]
        linarith
    · have hn : τ ≠ (InfinitePlace.mk τ).embedding := by
        rw [hv]; exact (conjugate_ne τ).symm
      have l1 : ∀ i, ((lamOf W m τ i : ℕ) : ℤ) = (W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m τ i = ((W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ)).toNat := if_neg hn
        rw [h]
        exact Int.toNat_of_nonneg (hm _ _)
      have l2 : ∀ i, lamOf W m (ComplexEmbedding.conjugate τ) i = m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m (ComplexEmbedding.conjugate τ) i = m (InfinitePlace.mk (ComplexEmbedding.conjugate τ)) :=
          if_pos (by rw [InfinitePlace.mk_conjugate_eq, hv])
        rw [h, InfinitePlace.mk_conjugate_eq]
      have hw : W.at τ = (W (InfinitePlace.mk τ)).dual := if_neg fun h => hn h.symm
      refine ⟨fun i => ((n - 1) * m (InfinitePlace.mk τ) + R) + (lamOf W m τ i + (n - 1 - (i : ℕ))), Fin.rev k,
        Or.inl ⟨m (InfinitePlace.mk τ), fun i => by rw [c2, l2], fun i => ?_⟩, ?_⟩
      · simp only [c1, hR]
      · have e3 : n - 1 - ((Fin.rev k : Fin n) : ℕ) = k := by
          have := k.isLt
          rw [Fin.val_rev]
          omega
        have e4 : (((n - 1 : ℕ) : ℤ)) = (n : ℤ) - 1 := by
          rw [Nat.cast_sub hk]; simp
        rw [if_neg hn] at hs
        rw [hw, ← hs]
        simp only [e3, DomWeight.dual]
        push_cast
        rw [l1, e4]
        ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpSum
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem imag_of_sq {c : ℂ} {d : ℕ} (hd : 0 < d) (h : c ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) c = -c ∧ c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qh67.imag_of_sq hd h

private theorem sum_emb {E : Type} [Field E] [NumberField E]
    (hc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ) (f : (E →+* ℂ) → ℤ) :
    ∑ φ, f φ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq φ with h | h
      · left; exact h.symm
      · right; rw [h]; exact (ComplexEmbedding.involutive_conjugate E φ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hfib, Finset.sum_pair (hc _).symm]

theorem UpperTheory.Gal.CertificateRingHomMap.pExpSum_of :
    UpperTheory.Gal.CertificateRingHomMap.ExpSum := by
  intro E _ _ _ n d x hd hx W m hm τ
  have hsq : ∀ φ : E →+* ℂ, (φ x) ^ 2 = -(d : ℂ) := fun φ => by
    rw [← map_pow, hx]; simp
  have hτ0 : τ x ≠ 0 := (imag_of_sq hd (hsq τ)).2
  have hcj : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ x = -φ x := fun φ => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact (imag_of_sq hd (hsq φ)).1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ h => by
    have h1 := hcj φ
    rw [h] at h1
    have h2 : φ x ≠ 0 := (imag_of_sq hd (hsq φ)).2
    exact h2 (self_eq_neg.1 h1)
  have hpm : ∀ φ : E →+* ℂ, φ x = τ x ∨ φ x = -τ x := fun φ =>
    sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq φ).trans (hsq τ).symm)
  have hnn : τ x ≠ -τ x := fun h => hτ0 (self_eq_neg.1 h)
  have hl0 : ∀ v : InfinitePlace E, ∑ j, lamOf W m v.embedding j = n * m v := fun v => by
    simp [lamOf, InfinitePlace.mk_embedding]
  have hl1 : ∀ v : InfinitePlace E, ((∑ j, lamOf W m (ComplexEmbedding.conjugate v.embedding) j : ℕ) : ℤ) =
      ∑ i, (W v).w i + n * m v := fun v => by
    have hv : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
      rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    have h1 : ∀ j, lamOf W m (ComplexEmbedding.conjugate v.embedding) j = ((W v).w j + m v).toNat := fun j => by
      unfold lamOf
      rw [hv, if_neg (hne _)]
    simp only [h1]
    push_cast
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hm v i), Finset.sum_add_distrib]
    simp
  set F : (E →+* ℂ) → ℤ := fun φ => (((if φ x = -τ x then 1 else 0) * ∑ j, lamOf W m φ j : ℕ) : ℤ) with hF
  have hFv : ∀ v : InfinitePlace E, F v.embedding + F (ComplexEmbedding.conjugate v.embedding) =
      n * m v + if v.embedding x = -τ x then 0 else ∑ i, (W v).w i := fun v => by
    simp only [hF, hcj]
    rcases hpm v.embedding with h | h
    · have h1 : v.embedding x ≠ -τ x := by rw [h]; exact hnn
      have h2 : -v.embedding x = -τ x := by rw [h]
      rw [if_neg h1, if_pos h2, if_neg h1, zero_mul, one_mul, hl1]
      push_cast; ring
    · have h2 : -v.embedding x ≠ -τ x := by rw [h, neg_neg]; exact hnn
      rw [if_pos h, if_neg h2, if_pos h, zero_mul, one_mul, hl0]
      push_cast; ring
  have hF1 : ∑ φ, F φ = mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ := by
    rw [sum_emb hne, Finset.sum_congr rfl fun v _ => hFv v]
    unfold mOf
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  have hmem : ComplexEmbedding.conjugate τ ∈ Finset.univ.erase τ :=
    Finset.mem_erase.2 ⟨hne τ, Finset.mem_univ _⟩
  have hF2 : ∑ φ, F φ = F τ + (F (ComplexEmbedding.conjugate τ) +
      ∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), F φ) := by
    rw [Finset.add_sum_erase _ F hmem, Finset.add_sum_erase _ F (Finset.mem_univ τ)]
  have hFτ : F τ = 0 := by simp only [hF]; rw [if_neg hnn]; simp
  have hFc : F (ComplexEmbedding.conjugate τ) = n * m (InfinitePlace.mk τ) +
      if τ = (InfinitePlace.mk τ).embedding then ∑ i, (W (InfinitePlace.mk τ)).w i else 0 := by
    simp only [hF]
    rw [if_pos (hcj τ), one_mul]
    split_ifs with h
    · conv_lhs => rw [h]
      rw [hl1]
      ring
    · have h' : ComplexEmbedding.conjugate τ = (InfinitePlace.mk τ).embedding := by
        rcases InfinitePlace.embedding_mk_eq τ with h1 | h1
        · exact absurd h1.symm h
        · exact h1.symm
      rw [h', hl0]
      push_cast; ring
  rw [← hF1, hF2, hFτ, hFc, zero_add]
  simp only [hF]
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSchHom
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSchHom_of :
    UpperTheory.Gal.CertificateRingHomMap.SchHom := by
  intro n t _
  refine ⟨fun lam c _ => UpperTheory.Gal.Schur.SchurHomog_holds ℂ n lam t c, fun m => ?_⟩
  obtain ⟨h0, h1⟩ := UpperTheory.Gal.Schur.SchurDet_holds ℂ n t
  have h := h1 (fun _ => 0) m
  simp only [zero_add] at h
  rw [h, h0, mul_one]
end

