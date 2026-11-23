module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SecondProjDiagonalEmbed
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem zzPlus_firstProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) =
      (g.q : F)⁻¹ * ph1 g (Zh a b) + (if a = Fin.last r ∧ b = Fin.last r then T / (g.q : F) else 0) := by
  have h1 : ∀ x : E, ph1 g x = (g.e x).1 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h1, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.fst_zero, Prod.fst_sub,
    sub_zero, add_zero] <;> ring

theorem zzPlus_secondProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) =
      -((g.q : F)⁻¹ * ph2 g (Zh b a)) + (if a = Fin.last r ∧ b = Fin.last r then -(T' / (g.q : F)) else 0) := by
  have h2 : ∀ x : E, ph2 g x = (g.e x).2 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h2, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.snd_zero, Prod.snd_sub,
    sub_zero, add_zero] <;> ring

def lamV (g : SplitG M.L) (m : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => -(ph2 g (m a)) / (g.q : F)) (fun a => ph1 g (m a) / (g.q : F))

theorem firstProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph1 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph1 g (f j : E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]

theorem secondProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph2 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph2 g (f j : E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]

theorem firstProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph1 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).1 = c
  rw [AlgEquiv.commutes]
  rfl

theorem secondProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph2 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).2 = c
  rw [AlgEquiv.commutes]
  rfl

theorem uV_llMap (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : M.Mat (r + 1)) (TT : M.R) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (hTT : g.e (TT : E) = (T, T')) (m : Fin (r + 1) → M.R) :
    uV g (llMap hs Z TT m) = Matrix.vecMul (lamV g m) (gHat g Zh T T') := by
  have hZe : ∀ i j, ((Z.Z i j : M.R) : E) = HermSp.ZZplusOf M Zh T T' i j := fun i j => by
    rw [← hZ]; rfl
  have hT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have hT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  have hq := q_ne g
  obtain ⟨Zf, rfl⟩ : ∃ Zf : Fin (r + 1) → Fin (r + 1) → E, Matrix.of Zf = Zh := ⟨Zh, rfl⟩
  have hsum1 : ∀ i, ∑ x, (g.e (Zf i x)).1 * (g.e (m x : E)).1 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).1 * (g.e (Zf i x)).1 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum2 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).2 * (g.e (Zf x i)).2 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum3 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 / (g.q : F) =
      ∑ x, (g.e (m x : E)).2 * (g.e (Zf x i)).2 / (g.q : F) := fun i => Finset.sum_congr rfl fun x _ => by ring
  funext k
  rcases k with i | i
  · simp only [uV, Sum.elim_inl, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, firstProj_ring_sum,
      hZe, zzPlus_firstProj_corner hs, hT1, firstProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inr,
      gHat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
  · simp only [uV, Sum.elim_inr, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, secondProj_ring_sum,
      hZe, zzPlus_secondProj_corner hs, hT2, secondProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inl,
      gHat, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)

theorem lamV_dot_mem (hs : M.split = some g) (m w : Fin (r + 1) → M.R) :
    dotProduct (lamV g m) (uV g w) ∈ 𝒪[F] := by
  classical
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  unfold dotProduct lamV uV
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  apply sum_mem
  intro a _
  obtain ⟨hm1, hm2, cm, hcm⟩ := comp_of_mem_R hs (m a).2
  obtain ⟨hw1, hw2, cw, hcw⟩ := comp_of_mem_R hs (w a).2
  have key : -(ph2 g (m a : E)) / (g.q : F) * ph1 g (w a : E) + ph1 g (m a : E) / (g.q : F) * ph2 g (w a : E) =
      (cm : F) * (g.e (w a : E)).2 - (g.e (m a : E)).2 * (cw : F) := by
    show -((g.e (m a : E)).2) / (g.q : F) * (g.e (w a : E)).1 +
      (g.e (m a : E)).1 / (g.q : F) * (g.e (w a : E)).2 = _
    have e1 : (g.e (m a : E)).1 = (g.e (m a : E)).2 + (g.q : F) * cm := by linear_combination hcm
    have e2 : (g.e (w a : E)).1 = (g.e (w a : E)).2 + (g.q : F) * cw := by linear_combination hcw
    rw [e1, e2]
    field_simp
    ring
  rw [key]
  exact sub_mem (mul_mem cm.2 hw2) (mul_mem hm2 cw.2)

theorem dot_inv_vecMul {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (lam x : n → F) : dotProduct (Matrix.vecMul lam G) (Matrix.mulVec G⁻¹ x) = dotProduct lam x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]

theorem dot_inv_mulVec {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (mu x : n → F) : dotProduct x (Matrix.mulVec G⁻¹ (Matrix.mulVec G mu)) = dotProduct x mu := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]

theorem gHat_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    gHat g (Zh.map M.L.cj) T T' = (gHat g Zh T T').transpose := by
  have hcj1 : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have hcj2 : ∀ x : E, ph2 g (M.L.cj x) = ph1 g x := fun x => by
    show (g.e (M.L.cj x)).2 = (g.e x).1
    rw [g.e_cj]
    rfl
  unfold gHat
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_transpose]
  congr 1
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl
  · ext a b
    simp only [Matrix.map_apply, hcj2]
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, hcj1]
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.ThetaPMem
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
theorem elim_sub (a b c d : Fin (r + 1) → O) :
    (Sum.elim a b : Ix r → O) - Sum.elim c d = Sum.elim (a - c) (b - d) := by
  funext i; cases i <;> rfl

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

def thetaP (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) (p : PairSet O cj hO Z₁ Z₂) :
    DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t' :=
  thetaOf O cj hO t t' p.1.1 p.1.2 p.2.1.1 p.2.1.2 (pair_b O cj hcj hO hu₁ hu₂ p)
    (pair_e O cj hcj hO hu₁ hu₂ hκ₁ hκ₂ p)

private theorem thetaP_mk_eq_mk_sum_elim_liftOf (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) (p : PairSet O cj hO Z₁ Z₂)
    (Y : Ix r → O) :
    thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) =
      Submodule.Quotient.mk (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
        (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j))) := rfl

private theorem mk_sum_elim_eq_of_sub_mem_headCols (a a' b b' : Fin (r + 1) → O) (ha : a - a' ∈ headCols Z₂)
    (hb : b - b' ∈ headCols (cjT O cj hO Z₂)) :
    (Submodule.Quotient.mk (Sum.elim a b) : DDc O cj (Z₂.map O.subtype) t t') =
      Submodule.Quotient.mk (Sum.elim a' b') := by
  apply (Submodule.Quotient.eq _).mpr
  rw [elim_sub]
  exact mem_relC_of_K O cj hO Z₂ t t' _ _ ha hb

private theorem lamC_eq_of_pairSet_mk_eq (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (p : PairSet O cj hO Z₁ Z₂) (y y₂ : Fin (r + 1) → O)
    (h : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂) :
    lamC (Z₂.map O.subtype) (fun j => ((y₂ j : O) : E)) = lamC (Z₁.map O.subtype) (fun j => ((y j : O) : E)) := by
  have key := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y y₂ h
  simpa [lamL_apply] using key

theorem thetaP_mem (ht : cj (t : E) = t) (ht' : cj (t' : E) = t')
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (p : PairSet O cj hO Z₁ Z₂) :
    thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t' := by
  have hl : ∀ y : Fin (r + 1) → O,
      p.1.1 (Submodule.Quotient.mk (liftOf O p.1.1.symm.toLinearMap y)) = Submodule.Quotient.mk y := by
    intro y
    rw [liftOf_spec]
    exact p.1.1.apply_symm_apply _
  have hr : ∀ y : Fin (r + 1) → O,
      p.1.2 (Submodule.Quotient.mk (liftOf O p.1.2.symm.toLinearMap y)) = Submodule.Quotient.mk y := by
    intro y
    rw [liftOf_spec]
    exact p.1.2.apply_symm_apply _
  have he2 := pair_e O cj hcj hO hu₁ hu₂ hκ₁ hκ₂ p
  refine ⟨?_, ?_, ?_⟩
  · intro Y W Y₂ W₂ hY hW
    rw [thetaP_mk_eq_mk_sum_elim_liftOf] at hY hW
    have hY' := (Submodule.Quotient.eq _).mp hY.symm
    have hW' := (Submodule.Quotient.eq _).mp hW.symm
    have e1 : formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W =
        formC O cj (Z₂.map O.subtype) t t' (Y₂ - Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
            (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j))) W₂ +
          formC O cj (Z₂.map O.subtype) t t' (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
            (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
            (W₂ - Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) +
          (formC O cj (Z₂.map O.subtype) t t'
            (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
            (Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) -
            formC O cj (Z₁.map O.subtype) t t' Y W) := by
      rw [formC_sub_left, formC_sub_right]
      ring
    rw [e1]
    exact O.add_mem (O.add_mem (formC_rel_left O cj _ _ _ hG₂ hO _ _ hY')
      (formC_rel_right O cj hcj _ _ _ ht ht' hG₂ hO _ _ hW'))
      (form_pair O cj hcj hO t t' ht ht' hu₁ hu₂ hκ₁ hκ₂ hG₁ hG₂ p Y W)
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨Y, hY0, rfl⟩, rfl⟩
      simp only [GamC, Set.mem_setOf_eq]
      refine ⟨Sum.elim (Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
        (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)), fun a => ?_, ?_⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) = _
          rw [thetaP_mk_eq_mk_sum_elim_liftOf, supp_inl O Y hY0]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_e_mem O (f := p.1.1.toLinearMap) p.2.1.2 _)
            (by rw [sub_self]; exact zero_mem _)
        · simp
        · exact (p.2.2.1 _ _ (liftOf_spec O _ _).symm).symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      refine ⟨(Submodule.Quotient.mk (Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
          (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j))),
          (((Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
            (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j)) : Ix r → O) (Sum.inl (Fin.last r)) : O) : E),
          lamStarC cj (Z₁.map O.subtype) fun b => (((Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
            (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j)) : Ix r → O) (Sum.inr b) : O) : E)), ?_, ?_⟩
      · simp only [GamC, Set.mem_setOf_eq]
        refine ⟨_, fun a => ?_, rfl⟩
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      · have hY₂ : Y₂ = Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1) (fun j => Y₂ (Sum.inr j)) := by
          rw [← supp_inl O Y₂ hY0]
          exact elim_eta O Y₂
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk _) = Submodule.Quotient.mk Y₂
          rw [thetaP_mk_eq_mk_sum_elim_liftOf]
          conv_rhs => rw [hY₂]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_e_mem O (f := p.1.1.toLinearMap) p.2.1.2 _)
            (lift_rep_mem O p.1.2 _ _ (liftOf_spec O _ _))
        · simp
        · exact (p.2.2.1 _ _ (hr _)).symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨Y, hY0, rfl⟩, rfl⟩
      simp only [GamC', Set.mem_setOf_eq]
      refine ⟨Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
        (Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1), fun a => ?_, ?_⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) = _
          rw [thetaP_mk_eq_mk_sum_elim_liftOf, supp_inr O Y hY0]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (by rw [sub_self]; exact zero_mem _)
            (lift_e_mem O (f := p.1.2.toLinearMap) he2 _)
        · exact (lamC_eq_of_pairSet_mk_eq O cj hcj hO hu₁ hu₂ p _ _ (liftOf_spec O _ _).symm).symm
        · simp
    · rintro _ ⟨Y₂, hY0, rfl⟩
      refine ⟨(Submodule.Quotient.mk (Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
          (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1)),
          lamC (Z₁.map O.subtype) fun a => (((Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
            (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) : Ix r → O) (Sum.inl a) : O) : E),
          (((Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
            (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) : Ix r → O) (Sum.inr (Fin.last r)) : O) : E)),
          ?_, ?_⟩
      · simp only [GamC', Set.mem_setOf_eq]
        refine ⟨_, fun a => ?_, rfl⟩
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      · have hY₂ : Y₂ = Sum.elim (fun j => Y₂ (Sum.inl j)) (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) := by
          rw [← supp_inr O Y₂ hY0]
          exact elim_eta O Y₂
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk _) = Submodule.Quotient.mk Y₂
          rw [thetaP_mk_eq_mk_sum_elim_liftOf]
          conv_rhs => rw [hY₂]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_rep_mem O p.1.1 _ _ (liftOf_spec O _ _))
            (lift_e_mem O (f := p.1.2.toLinearMap) he2 _)
        · exact (lamC_eq_of_pairSet_mk_eq O cj hcj hO hu₁ hu₂ p _ _ (hl _)).symm
        · simp

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

