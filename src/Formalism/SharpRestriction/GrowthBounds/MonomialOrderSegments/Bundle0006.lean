module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyLabel

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.OmegaValue
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem omega_value (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gp gm : D.EM → K) (hgp0 : ∀ ζ, 0 ≤ v (gp ζ))
    (happ : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZi : Integral v Z) (hZg : D.Good p Z) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (dg gp Z))) - D.abelian₂ p F Z) := by
  have key : ∀ W, D.abelian₂ p F W = fock F (dg D.ga (D.ph p W)) := fun W => by
    simp only [TwistData.abelian₂, gaAct_eq_dg]
  have hLsum : ∀ (s : Finset D.EM) (f : D.EM → MvPolynomial (D.ML × Fin D.r) K),
      D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
    intro s f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [key, map_sum, fock_sum_right]
  have hLsmul : ∀ (c : K) (W : MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (c • W) = c * D.abelian₂ p F W := by
    intro c W
    simp only [key, map_smul, fock_smul_right]
  have hmon : ∀ (g : D.EM → K) (ζ : D.EM), dg g (monomial ζ (1 : K)) = g ζ • monomial ζ (1 : K) := by
    intro g ζ
    rw [dg_monomial, MvPolynomial.smul_monomial, smul_eq_mul]
  have hZ : Z = ∑ ζ ∈ Z.support, Z.coeff ζ • monomial ζ (1 : K) := by
    conv_lhs => rw [Z.as_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hp2 : 2 ≤ p := by have := hD.five_le; omega
  have hr1 : 1 ≤ D.r := hV.1
  have hkap : 0 ≤ D.kapD p := by
    unfold TwistData.kapD kap
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (lg_nonneg' hp2 hr1 _)
  have hDm : 0 ≤ D.Dm p C0 := TwistData.Dm_nonneg (D := D) hp2 hr1 h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hZ, map_sum (dg gp), map_sum Pj, map_sum (dg gm), hLsum, hLsum, ← Finset.sum_sub_distrib]
  simp only [map_smul, hLsmul]
  apply vge_sum'
  intro ζ hζ
  rw [← mul_sub]
  have hgood : D.GoodE p ζ := hZg ζ hζ
  have hlow : D.LabLowE p ζ := hgood.1
  have h1' : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) =
      gp ζ * D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) := by
    rw [hmon, map_smul, map_smul, hLsmul]
  have h2' : D.abelian₂ p F (dg gm (monomial ζ (1 : K))) = gm ζ * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [hmon, hLsmul]
  have hexp : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) - D.abelian₂ p F (monomial ζ (1 : K)) =
      gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))) +
        (gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [h1', h2']
    ring
  rw [hexp]
  have hval := TwistData.value_monomial (D := D) hD h1 hV hH hE hF hF0 hdig Pj hP1 hP2 hP4 gm
    (fun ζ h => (happ ζ h).2) hgood
  have hZζ : vge v 0 (Z.coeff ζ) := (vge_zero_iff v _).mpr (hZi ζ)
  have hgp' : vge v 0 (gp ζ) := (vge_zero_iff v _).mpr (hgp0 ζ)
  have t1 : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K))))) := by
    have := vge_mul' v hgp' hval
    simpa using this
  have hgaP : v (D.gaP p gam ζ) = 0 := TwistData.v_gaP (D := D) hV hdig hlow
  have hg0 : D.gaP p gam ζ ≠ 0 := by
    intro h
    rw [h] at hgaP
    simp at hgaP
  have hgaP' : vge v 0 (D.gaP p gam ζ) := (vge_zero_iff v _).mpr (le_of_eq hgaP.symm)
  have hc1 : vge v (D.c : ℝ) (gp ζ - D.gaP p gam ζ) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gp ζ - D.gaP p gam ζ)).mpr (by exact_mod_cast (happ ζ hlow).1)
    simpa using this
  have hc2 : vge v (D.c : ℝ) (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gm ζ - (D.gaP p gam ζ)⁻¹)).mpr (by exact_mod_cast (happ ζ hlow).2)
    simpa using this
  have hgm' : vge v 0 (gm ζ) := by
    have h3 : gm ζ = (gm ζ - (D.gaP p gam ζ)⁻¹) + (D.gaP p gam ζ)⁻¹ := by ring
    rw [h3]
    refine vge_add' v (vge_mono' v (by positivity) hc2) ?_
    rw [vge_zero_iff v, AddValuation.map_inv, hgaP, neg_zero]
  have hsplit : gp ζ * gm ζ - 1 =
      (gp ζ - D.gaP p gam ζ) * gm ζ + D.gaP p gam ζ * (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    rw [mul_sub (D.gaP p gam ζ), mul_inv_cancel₀ hg0]
    ring
  have t2 : vge v (D.c : ℝ) (gp ζ * gm ζ - 1) := by
    rw [hsplit]
    refine vge_add' v ?_ ?_
    · simpa using vge_mul' v hc1 hgm'
    · simpa using vge_mul' v hgaP' hc2
  have hΛ := TwistData.vge_Lam_monomial (D := D) hD hV hF0 hgood
  have t3 := vge_mul' v t2 hΛ
  have t3' : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      ((gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K))) := vge_mono' v (by linarith) t3
  simpa using vge_mul' v hZζ (vge_add' v t1 t3')

theorem stepDEF_of (h1 : 1 ≤ C0) (hDIG : DIG K v p) (hG : StepG K v p) (hP : StepP K v p C0)
    (hE : StepE K v p) : StepDEF K v p C0 := by
  intro hD D hV hH _ F hF hF0
  have hF0' := (exists_of_vBB_zero v F hF0).2
  obtain ⟨Pj, hP1, hP2, hP3, hP4, hP5⟩ := hP hD D hV
  obtain ⟨cst, gam, hdig⟩ := D.digOK_exists hDIG hD hV.2.2.1
  obtain ⟨gp, gm, hgp, hgm, happ, hcost⟩ := hG hD D hV cst gam hdig
  obtain ⟨hN, hI, hGd, hch, hY⟩ :=
    omega_clauses hD h1 D hV Pj ⟨hP1, hP2, hP3, hP4, hP5⟩ gp gm hgp hgm hcost
  refine ⟨(dg gm).comp (Pj.comp (dg gp)), ⌈D.Dm p C0 + D.kapD p / 2⌉₊, hN, hI, hGd, hch, hY, ?_⟩
  intro Z hZi hZg
  exact omega_value hD h1 D hV hH hE hF hF0' hdig Pj hP1 hP2 hP4 gp gm hgp happ Z hZi hZg

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutionXFirstEmbedding
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem PsiP_integral {v : AddValuation K (WithTop ℚ)} {nc : ℕ}
    (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) (h : Integral v (∏ k, col k)) :
    Integral v (D.PsiP j col occ) :=
  integral_prod_rename col (fun k => Prod.map (D.fk j (occ k)) id)
    (fun k => (D.fk_inj j (occ k)).prodMap Function.injective_id) h

theorem ph_X_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.fk j o l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold fk ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · split_ifs <;> simp [mb]
  · split_ifs
    · rw [second_embedding_natAdd]
      split_ifs <;> simp [mlab, mtp]
    · simp [mlab]

theorem substitution_X_first_embedding (p : ℕ) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.e0 j l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · simp [mb]
  · simp [mlab]

theorem ph_rename_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r)))
    (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.fk j o) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.fk j o) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.ph_X_fk j p o l a
  exact DFunLike.congr_fun this G

theorem substitution_rename_first_embedding (p : ℕ) (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.e0 j) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.substitution_X_first_embedding j p l a
  exact DFunLike.congr_fun this G

theorem PsiP_ph (p : ℕ) {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) :
    D.ph p (D.PsiP j col occ) = rename (Prod.map (D.eA j) id) (∏ k, col k) := by
  unfold PsiP
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => D.ph_rename_fk j p _ _

theorem card_unmarked (o : Finset (Fin (D.nB j + D.r))) (hM : ¬ D.Marked j o) (m : Fin D.r) :
    (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card < D.r := by
  have h1 : (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card ≤
      (Finset.Ico (D.nB j) (D.stg j m)).card := by
    refine Finset.card_le_card_of_injOn (fun l => l.val) ?_ ?_
    · intro l hl
      have hl' := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, hl'.2.1⟩
      by_contra hlt
      exact hM ⟨l, hl'.1, not_le.mp hlt⟩
    · intro x _ y _ h
      exact Fin.ext h
  rw [Nat.card_Ico] at h1
  have := m.2
  have h2 : D.stg j m - D.nB j < D.r := by unfold stg; omega
  omega

theorem PsiP_val {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (cidx : Fin nc → ℤ) (hts : Fin nc → ℕ) (m : Fin D.r)
    (h14 : ∀ k, 1 ≤ cidx k →
      hts k ≤ ((occ k).filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card)
    (h16 : ∀ k, ((colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) (col k)) :
    ((∑ k, colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS D.msg (D.YPset j m) (D.PsiP j col occ) := by
  unfold PsiP
  refine le_trans ?_ (valS_prod_le D.msg (D.YPset j m) Finset.univ _)
  rw [WithTop.coe_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hM : D.Marked j (occ k)
  · have hf : D.fk j (occ k) = D.e1 j := by unfold fk; rw [if_pos hM]
    rw [hf, valS_rename (D.e1 j) (D.second_embedding_injective j), YP_preimage1]
    have : D.msg ∘ D.e1 j = D.msg ∘ D.e0 j := funext fun l => D.second_embedding_mark_eq_first j l
    rw [this]
    exact h16 k
  · have hf : D.fk j (occ k) = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [hf, valS_rename (D.e0 j) (D.index_embedding_injective j)]
    have h0 : (0 : WithTop ℤ) ≤ valS (D.msg ∘ D.e0 j)
        ((D.YPset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn) (col k) := by
      apply valS_nonneg_of_free
      intro α hα i hi a
      have hlt := D.YP_preimage0 j m i hi
      have hi2 : i ∉ occ k := fun h => hM ⟨i, h, hlt⟩
      have hd := (mem_PolK_iff _ _).mp (hcol k) α hα i
      rw [if_neg hi2] at hd
      unfold ldeg at hd
      exact (Finset.sum_eq_zero_iff.mp hd) a (Finset.mem_univ a)
    refine le_trans ?_ h0
    have : colVal (cidx k) (hts k) D.r ≤ 0 := by
      unfold colVal
      by_cases hc : 1 ≤ cidx k
      · have h1 := h14 k hc
        have h2 := D.card_unmarked j (occ k) hM m
        have h3 : ¬ (1 ≤ cidx k ∧ hts k = D.r) := by
          rintro ⟨-, h⟩; omega
        rw [if_neg h3]
        split_ifs <;> simp
      · have h3 : ¬ (1 ≤ cidx k ∧ hts k = D.r) := fun h => hc h.1
        rw [if_neg h3]
        split_ifs <;> simp
    exact_mod_cast this

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

