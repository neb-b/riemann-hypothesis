module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.LiftMemHead
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleIso

variable {R : Type} [CommRing R] {r : ℕ}

theorem isoMbeTransport_inv {Z₁ Z₂ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (e₁ : MbMod Z₁ ≃ₗ[R] MbMod Z₁') (e₂ : MbMod Z₂ ≃ₗ[R] MbMod Z₂') (s t v : R) (hs : IsUnit s) (hv : IsUnit v)
    (hb₁ : e₁ (s • bCls Z₁ + t • eCl Z₁) = bCls Z₁') (hb₂ : e₂ (s • bCls Z₂ + t • eCl Z₂) = bCls Z₂')
    (he₁ : e₁ (v • eCl Z₁) = eCl Z₁') (he₂ : e₂ (v • eCl Z₂) = eCl Z₂') (φ : MbMod Z₁' ≃ₗ[R] MbMod Z₂')
    (hφb : φ (bCls Z₁') = bCls Z₂') (hφe : φ (eCl Z₁') = eCl Z₂') :
    φ (e₁ (bCls Z₁)) = e₂ (bCls Z₂) ∧ φ (e₁ (eCl Z₁)) = e₂ (eCl Z₂) := by
  have he : φ (e₁ (eCl Z₁)) = e₂ (eCl Z₂) := by
    obtain ⟨w, hw⟩ := hv.exists_left_inv
    have k₁ : e₁ (eCl Z₁) = w • eCl Z₁' := by rw [← he₁, map_smul, smul_smul, hw, one_smul]
    have k₂ : e₂ (eCl Z₂) = w • eCl Z₂' := by rw [← he₂, map_smul, smul_smul, hw, one_smul]
    rw [k₁, map_smul, hφe, k₂]
  refine ⟨?_, he⟩
  obtain ⟨w, hw⟩ := hs.exists_left_inv
  have k2 : ∀ x y : MbMod Z₂', s • x = s • y → x = y := fun x y h => by
    rw [← one_smul R x, ← one_smul R y, ← hw, mul_smul, mul_smul, h]
  apply k2
  have h0 : φ (e₁ (s • bCls Z₁ + t • eCl Z₁)) = e₂ (s • bCls Z₂ + t • eCl Z₂) := by rw [hb₁, hb₂]; exact hφb
  simp only [map_add (f := _), map_smul, he] at h0
  exact add_right_cancel h0

def isoMbeTransport {Z₁ Z₂ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (e₁ : MbMod Z₁ ≃ₗ[R] MbMod Z₁') (e₂ : MbMod Z₂ ≃ₗ[R] MbMod Z₂') (s t v : R) (hs : IsUnit s) (hv : IsUnit v)
    (hb₁ : e₁ (s • bCls Z₁ + t • eCl Z₁) = bCls Z₁') (hb₂ : e₂ (s • bCls Z₂ + t • eCl Z₂) = bCls Z₂')
    (he₁ : e₁ (v • eCl Z₁) = eCl Z₁') (he₂ : e₂ (v • eCl Z₂) = eCl Z₂') : IsoMbe Z₁ Z₂ ≃ IsoMbe Z₁' Z₂' where
  toFun γ := ⟨(e₁.symm.trans γ.1).trans e₂, by
      have h1 : e₁.symm (bCls Z₁') = s • bCls Z₁ + t • eCl Z₁ := by rw [← hb₁, LinearEquiv.symm_apply_apply]
      simp only [LinearEquiv.trans_apply, h1, map_add (f := _), map_smul, γ.2.1, γ.2.2]
      simpa only [map_add, map_smul] using hb₂,
    by
      have h1 : e₁.symm (eCl Z₁') = v • eCl Z₁ := by rw [← he₁, LinearEquiv.symm_apply_apply]
      simp only [LinearEquiv.trans_apply, h1, map_smul, γ.2.2, he₂]⟩
  invFun γ := ⟨(e₁.trans γ.1).trans e₂.symm, by
      simp only [LinearEquiv.trans_apply,
        (isoMbeTransport_inv e₁ e₂ s t v hs hv hb₁ hb₂ he₁ he₂ γ.1 γ.2.1 γ.2.2).1, LinearEquiv.symm_apply_apply],
    by
      simp only [LinearEquiv.trans_apply,
        (isoMbeTransport_inv e₁ e₂ s t v hs hv hb₁ hb₂ he₁ he₂ γ.1 γ.2.1 γ.2.2).2, LinearEquiv.symm_apply_apply]⟩
  left_inv γ := by apply Subtype.ext; ext x; simp
  right_inv γ := by apply Subtype.ext; ext x; simp

theorem card_isoMbe_transport {Z₁ Z₂ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (e₁ : MbMod Z₁ ≃ₗ[R] MbMod Z₁') (e₂ : MbMod Z₂ ≃ₗ[R] MbMod Z₂') (s t v : R) (hs : IsUnit s) (hv : IsUnit v)
    (hb₁ : e₁ (s • bCls Z₁ + t • eCl Z₁) = bCls Z₁') (hb₂ : e₂ (s • bCls Z₂ + t • eCl Z₂) = bCls Z₂')
    (he₁ : e₁ (v • eCl Z₁) = eCl Z₁') (he₂ : e₂ (v • eCl Z₂) = eCl Z₂') :
    Nat.card (IsoMbe Z₁ Z₂) = Nat.card (IsoMbe Z₁' Z₂') :=
  Nat.card_congr (isoMbeTransport e₁ e₂ s t v hs hv hb₁ hb₂ he₁ he₂)

def dlast (r : ℕ) (δ : R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.diagonal fun i => if i = Fin.last r then δ else 1

theorem headCols_eq_of (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h : ∀ i (a : Fin r), Z' i a.castSucc = Z i a.castSucc) : headCols Z' = headCols Z := by
  unfold headCols; congr 2; funext a; funext i; exact h i a

def mbEqv (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (h : ∀ i (a : Fin r), Z' i a.castSucc = Z i a.castSucc) :
    MbMod Z ≃ₗ[R] MbMod Z' :=
  Submodule.quotEquivOfEq _ _ (headCols_eq_of Z Z' h).symm

theorem mbEqv_mk (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (h) (v : Fin (r + 1) → R) :
    mbEqv Z Z' h (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := rfl

theorem card_isoMbe_lastCol (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (δ c : R) (hδ : IsUnit δ) :
    Nat.card (IsoMbe Z₁ Z₂) =
      Nat.card (IsoMbe (Z₁ * dlast r δ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0)
        (Z₂ * dlast r δ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0)) := by
  have hcol : ∀ (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i (a : Fin r),
      (Z * dlast r δ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0) i a.castSucc =
        Z i a.castSucc := by
    intro Z i a
    simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]
  refine card_isoMbe_transport (mbEqv _ _ (hcol Z₁)) (mbEqv _ _ (hcol Z₂)) δ c 1 hδ isUnit_one ?_ ?_ ?_ ?_
  · simp only [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, mbEqv_mk]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mul_diagonal, hi, mul_comm])
  · simp only [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, mbEqv_mk]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mul_diagonal, hi, mul_comm])
  · simp [eCl, mbEqv_mk]
  · simp [eCl, mbEqv_mk]

def mbRowEqv (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (D Dinv : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h1 : D * Dinv = 1) (h2 : Dinv * D = 1) : MbMod Z ≃ₗ[R] MbMod (D * Z) :=
  Submodule.Quotient.equiv (headCols Z) (headCols (D * Z))
    { toFun := D.mulVec, invFun := Dinv.mulVec,
      map_add' := Matrix.mulVec_add D, map_smul' := fun c v => by simp [Matrix.mulVec_smul],
      left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2],
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    (by
      unfold headCols
      rw [Submodule.map_span]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, by funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨_, ⟨a, rfl⟩, by funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]⟩)

theorem mbRowEqv_mk (Z D Dinv : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (h1 h2) (v : Fin (r + 1) → R) :
    mbRowEqv Z D Dinv h1 h2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (D.mulVec v) := rfl

theorem card_isoMbe_lastRow (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (δ δi : R) (hδ : δ * δi = 1) :
    Nat.card (IsoMbe Z₁ Z₂) = Nat.card (IsoMbe (dlast r δ * Z₁) (dlast r δ * Z₂)) := by
  have h1 : dlast r δ * dlast r δi = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [hi, hδ])
  have h2 : dlast r δi * dlast r δ = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [hi, hδ, mul_comm])
  have hu : IsUnit δi := ⟨⟨δi, δ, by rw [mul_comm, hδ], hδ⟩, rfl⟩
  refine card_isoMbe_transport (mbRowEqv Z₁ _ _ h1 h2) (mbRowEqv Z₂ _ _ h1 h2) 1 0 δi isUnit_one hu ?_ ?_ ?_ ?_
  · simp only [bCls, one_smul, zero_smul, add_zero, mbRowEqv_mk]
    rw [lift_col_mul]
  · simp only [bCls, one_smul, zero_smul, add_zero, mbRowEqv_mk]
    rw [lift_col_mul]
  · simp only [eCl, ← Submodule.Quotient.mk_smul, mbRowEqv_mk]
    congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mulVec_diagonal, hi, mul_comm, hδ]
  · simp only [eCl, ← Submodule.Quotient.mk_smul, mbRowEqv_mk]
    congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mulVec_diagonal, hi, mul_comm, hδ]

end ScaleIso

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjEqFirstProj
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section DuU

theorem firstProj_conj_eq_secondProj (x : E) : ph1 g ((M.L.cj : E →+* E) x) = ph2 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_conj_eq_firstProj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem firstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  simp [firstProj_apply]

theorem ph2_algebraMap_eq (a : F) : ph2 g (algebraMap F E a) = a := by
  simp [secondProj_apply]

theorem firstProj_corner (a b : Fin (r + 1)) (X : E) : ph1 g (cor r a b X) = cor r a b (ph1 g X) := by
  unfold cor; split_ifs <;> simp

theorem firstProj_iotaOne_inl (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inl a) : M.L.O) : E) = ph1 g (l a : E) := by
  simp [iota1, firstProj_apply]

theorem firstProj_iotaOne_inr (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inr a) : M.L.O) : E) = (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) := by
  simp [iota1, firstProj_apply, secondProj_apply]

theorem firstProj_conj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((M.L.cj : E →+* E) ((iota2 hs l i : M.L.O) : E)) = ph1 g ((iota1 hs l i : M.L.O) : E) := by
  simp [iota2, firstProj_apply, g.e_cj, M.L.cj_cj]

theorem duU_formG_sub (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y W - formG O cj qi Z T T' Y W' =
      ∑ i, (Y i : E) * (Matrix.mulVec (gramG cj qi Z T T')⁻¹ fun j => cj (W j) - cj (W' j)) i := by
  unfold formG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, mul_assoc]

theorem firstProj_sum_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (c : Ix r → E) :
    ph1 g (∑ i, ((iota1 hs l i : M.L.O) : E) * c i) =
      ∑ a, ph1 g (l a : E) * ph1 g (c (Sum.inl a)) +
        ∑ a, (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) * ph1 g (c (Sum.inr a)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, firstProj_iotaOne_inl, firstProj_iotaOne_inr]

theorem duU_sum_single1 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) * f b = ph1 g (x : E) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem duU_sum_single2 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, (ph2 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) - ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E)) / (g.q : F) * f b =
      (ph2 g (x : E) - ph1 g (x : E)) / (g.q : F) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem ph1_mem_integers_of_mem_O {y : E} (hy : y ∈ M.L.O) : ph1 g y ∈ 𝒪[F] := by
  have hidem : (g.e.symm (1, 0) : E) * g.e.symm (1, 0) = g.e.symm (1, 0) := by
    rw [← map_mul]
    simp
  have hu : y * g.e.symm (1, 0) ∈ M.L.O := M.L.O.mul_mem hy (idem_mem_O M.L hidem)
  have hw : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) ∈ M.L.O :=
    M.L.O.add_mem hu (cj_mem_O M.L hu)
  have heq : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) = algebraMap F E (ph1 g y) := by
    apply g.e.injective
    refine Prod.ext ?_ ?_ <;> simp [g.e_cj, firstProj_apply]
  haveI : Nontrivial E := g.e.toEquiv.nontrivial
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (heq ▸ hw)

theorem duU_c_int (hs : M.split = some g) (c : Ix r → E)
    (h : ∀ l : Fin (r + 1) → M.R, ∑ i, ((iota1 hs l i : M.L.O) : E) * c i ∈ M.L.O) :
    ∀ i, ph1 g (c i) ∈ 𝒪[F] := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    exact g.q_irr.ne_zero (Subtype.ext h0)
  intro i
  rcases i with a | a
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a 1))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa using h1
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a (q2 hs)))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa [firstProj_apply, secondProj_apply, embedding_uniformizer hs, hq] using h1

theorem duU_sum_cor (a : Fin (r + 1)) (X : F) (f : Fin (r + 1) → F) :
    ∑ b, cor r a b X * f b = if a = Fin.last r then X * f (Fin.last r) else 0 := by
  unfold cor
  split_ifs with ha
  · simp [ha, ite_mul]
  · simp [ha]

theorem firstProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      ph2 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

end DuU

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

