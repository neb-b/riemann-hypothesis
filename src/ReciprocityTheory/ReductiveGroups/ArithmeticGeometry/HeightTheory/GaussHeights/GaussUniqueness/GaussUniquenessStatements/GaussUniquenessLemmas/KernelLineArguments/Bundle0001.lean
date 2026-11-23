module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ImgRSuccAbove

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.NotInjOfTrdeg
section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem not_inj_of_trdeg {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (S : Set E)
    (j0 : Fin (N + 1)) (ρ : Fin N → IntermediateField.adjoin F S) (hD : 1 ≤ D)
    (htr : Algebra.trdeg F (IntermediateField.adjoin F S) = ((D - 1 : ℕ) : Cardinal)) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) (imgR (D := D) j0 ρ)) := by
  intro hinj
  have hai : AlgebraicIndependent F (imgR (D := D) j0 ρ) := hinj
  have h1 := hai.cardinalMk_le_trdeg
  first
  | rw [← Algebra.trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  | rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  rw [htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h1
  have hT : Fintype.card (TVar D N) = (D + 1) * (N + 1) := by simp [TVar]
  have hS : Fintype.card (SVar D N) = 1 + (D + 1) * N := by simp [SVar]
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS] at h1
  norm_cast at h1
  rw [show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring] at h1
  generalize (D + 1) * N = P at h1
  omega

section Tr

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

noncomputable def gK (hv : IsTrivOn K v) :
    K →+* IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)) :=
  (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict ((vRing v).comap (algebraMap K Ω))
    (fun x => by rw [ValuationSubring.mem_comap]; exact alg_mem v hv x))

theorem gK_surj (hv : IsTrivOn K v) : Function.Surjective (gK v hv) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨x.1, rfl⟩

end Tr

end GaussValuationUniqueness
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.SHomFactor
section
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (jc : Fin (N + 1)) (b : Fin (N + 1) → Ω)
    (hb : b jc = 1) (i : Fin (D + 1)) (hi : i ≠ 0) :
    ∑ j, sImg (D := D) jc (fun k => b (jc.succAbove k)) (i, j) *
      algebraMap Ω (OmS Ω D N) (b j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc]
  simp only [sImg, GaussValuationUniqueness.sac_same, GaussValuationUniqueness.sac_succAbove, if_neg hi, hb, map_one,
    mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum, ← map_add, neg_add_cancel, map_zero]

noncomputable def eS {Ω : Type} [Field Ω] {D N : ℕ} (jc j0 : Fin (N + 1)) (x : Fin N → Ω) :
    SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun ik => sImg jc x (ik.1, j0.succAbove ik.2))

section Fac

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem sub_apply (y : vRing v) : (vRing v).subtype y = (y : Ω) := rfl

theorem sHom_factor (hv : IsTrivOn K v) (jc j0 : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → Ω) (ha : ∀ j, a j ∈ vRing v) (ha0 : a j0 = 1)
    (hrel : ∀ i : Fin (D + 1), i ≠ 0 →
      ∑ j, sImg jc x (i, j) * algebraMap Ω (OmS Ω D N) (a j) = 0) (f : MvPolynomial (TVar D N) K) :
    sHom (K := K) jc x f = MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
      (eS jc j0 x) (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) := by
  have key : ((sHom (K := K) jc x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) :
      MvPolynomial (TVar D N) K →+* OmS Ω D N) =
      (MvPolynomial.eval₂Hom ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
        (eS jc j0 x)).comp (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, sHom,
        MvPolynomial.aeval_C, psiT, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rfl
    · rintro ⟨i, j⟩
      rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same]
        · have h := hrel i hi
          rw [Fin.sum_univ_succAbove _ j, ha0, map_one, mul_one] at h
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same, hi, GaussValuationUniqueness.sub_apply]
          linear_combination h
      · simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_succAbove]
  exact RingHom.congr_fun key f

end Fac

end GaussValuationUniqueness
end

