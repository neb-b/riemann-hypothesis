module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.LiftMemHead

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FGInvariant
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA3

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def phiEq (A A' : Matrix (Ix r) (Ix r) O) (h1 : A * A' = 1) (h2 : A' * A = 1) : (Ix r → O) ≃ₗ[O] (Ix r → O) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear A) (Matrix.vecMulLinear A')
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one,
        LinearMap.id_apply])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one,
        LinearMap.id_apply])

theorem coe_vecMul (Y : Ix r → O) (A : Matrix (Ix r) (Ix r) O) (j : Ix r) :
    ((Matrix.vecMul Y A j : O) : E) = Matrix.vecMul (fun i => (Y i : E)) (A.map O.subtype) j := by
  simp [Matrix.vecMul, dotProduct]

theorem relC_fwd (G G' C C' : Matrix (Ix r) (Ix r) E) (hC : C * C' = 1) (hG : G' = C.transpose * G * C.map cj)
    (A : Matrix (Ix r) (Ix r) O) (hA : A.map O.subtype = C.map cj) (hC'O : ∀ i j, C' j i ∈ O)
    (Y : Ix r → O) (hY : ∃ c : Ix r → O, ∀ j, (Y j : E) = ∑ i, (c i : E) * G i j) :
    ∃ c : Ix r → O, ∀ j, ((Matrix.vecMul Y A j : O) : E) = ∑ i, (c i : E) * G' i j := by
  obtain ⟨c, hc⟩ := hY
  let c' : Ix r → O := fun i => ⟨∑ k, (c k : E) * C' i k, Subring.sum_mem _ fun k _ => O.mul_mem (c k).2 (hC'O k i)⟩
  refine ⟨c', fun j => ?_⟩
  have hcE : (fun i => (c' i : E)) = Matrix.vecMul (fun k => (c k : E)) C'.transpose := by
    funext i; simp [c', Matrix.vecMul, dotProduct]
  have hYE : (fun i => (Y i : E)) = Matrix.vecMul (fun k => (c k : E)) G := by
    funext j; rw [hc j]; simp [Matrix.vecMul, dotProduct]
  rw [coe_vecMul, hA, hYE]
  show _ = Matrix.vecMul (fun i => (c' i : E)) G' j
  rw [hcE, hG, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, hC, Matrix.transpose_one, Matrix.one_mul]

def fG (G : Matrix (Ix r) (Ix r) E) (Y W : Ix r → E) : E := ∑ i, ∑ j, Y i * G⁻¹ i j * cj (W j)

theorem fG_eq (G : Matrix (Ix r) (Ix r) E) (Y W : Ix r → E) :
    fG cj G Y W = Matrix.vecMul Y G⁻¹ ⬝ᵥ (fun j => cj (W j)) := by
  unfold fG
  simp only [dotProduct, Matrix.vecMul, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem fG_invariant (hcj : ∀ x, cj (cj x) = x) (G G' C : Matrix (Ix r) (Ix r) E)
    (hG : G' = C.transpose * G * C.map cj) (hCu : IsUnit C.det) (hCcu : IsUnit (C.map cj).det) (Y W : Ix r → E) :
    fG cj G' (Matrix.vecMul Y (C.map cj)) (Matrix.vecMul W (C.map cj)) = fG cj G Y W := by
  have hcw : (fun j => cj (Matrix.vecMul W (C.map cj) j)) = C.transpose.mulVec fun j => cj (W j) := by
    funext j; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, hcj, mul_comm]
  have hCt : IsUnit C.transpose.det := by rw [Matrix.det_transpose]; exact hCu
  rw [fG_eq, fG_eq, hcw, hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hCcu, Matrix.one_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCt, Matrix.mul_one]

end ScaleA3

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjZzPlusConjEq
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section LiftM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem lift_cj_mem_R (hs : M.split = some g) (x : M.R) : M.L.cj (x : E) ∈ M.R := by
  obtain ⟨h1, h2, c, hc⟩ := comp_of_mem_R hs x.2
  refine mem_R_of hs _ ⟨_, h2⟩ ⟨_, h1⟩ (-c) ?_ ?_
  · rw [g.e_cj]; rfl
  · show (g.e (x : E)).2 - (g.e (x : E)).1 = (g.q : F) * ((-c : 𝒪[F]) : F)
    push_cast; linear_combination -hc

def sigR (hs : M.split = some g) : M.R →+* M.R where
  toFun x := ⟨M.L.cj x, lift_cj_mem_R hs x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

theorem sigR_coe (hs : M.split = some g) (x : M.R) : ((sigR hs x : M.R) : E) = M.L.cj (x : E) := rfl

theorem lift_eps_mem {T T' : F} (h : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) : (T - T') / (g.q : F) ∈ 𝒪[F] := by
  obtain ⟨c, hc⟩ := h
  rw [hc, pow_two, mul_assoc, mul_div_cancel_left₀ _ (q_ne g)]
  exact mul_mem g.q.2 c.2

def epsR (hs : M.split = some g) {T T' : F} (h : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) : M.R :=
  dgR hs ⟨_, lift_eps_mem h⟩

theorem firstProj_zzPlus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) = ph1 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [firstProj_apply, cor, h]
  · simp [firstProj_apply, cor, h]

theorem secondProj_zzPlus (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) = -(ph2 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [secondProj_apply, cor, h]
  · simp [secondProj_apply, cor, h]

theorem secondProj_zzPlus_conj_eq (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := secondProj_zzPlus_conj hs Zh T T' a b

theorem lift_zsig (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (hG : GHyp M g T T' TT Zh Z Zσ) :
    Zσ.Z = -lstar (sigR hs) Z.Z + epsR hs hG.2.1 • liftE r := by
  have hZ : ∀ a b, ((Z.Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := fun a b => by
    have := congrFun (congrFun hG.2.2.2.1 a) b; simpa using this
  have hZσ : ∀ a b, ((Zσ.Z a b : M.R) : E) = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b := fun a b => by
    have := congrFun (congrFun hG.2.2.2.2.1 a) b; simpa using this
  have hq := q_ne g
  ext a b
  rw [eq_iff_ph (g := g)]
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, lstar_apply, Subring.coe_add,
    Subring.coe_neg, Subring.coe_mul, sigR_coe, hZ, hZσ, liftE, Matrix.of_apply, epsR, dgR_coe, map_add, map_neg,
    map_mul, firstProj_algebraMap, ph2_algebraMap_eq]
  constructor
  · rw [firstProj_zzPlus_conj hs, firstProj_conj_apply, secondProj_zzPlus hs]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [cor, ha, hb] <;> field_simp <;> ring
  · rw [secondProj_zzPlus_conj_eq hs, secondProj_conj_apply, firstProj_zzPlus hs]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [cor, ha, hb] <;> field_simp <;> ring

theorem lift_cancel (Z : M.Mat (r + 1)) (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (h : Z.Z * A = Z.Z * B) :
    A = B := by
  have h1 := congrArg (fun X => X.map M.R.subtype) h
  simp only [Matrix.map_mul] at h1
  have h2 : A.map M.R.subtype = B.map M.R.subtype := by
    rw [← Matrix.one_mul (A.map M.R.subtype), ← Matrix.nonsing_inv_mul _ Z.unit, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mul]
  ext i j
  exact congrFun (congrFun h2 i) j

end LiftM

section LiftK

variable {R : Type} [CommRing R] {r : ℕ}

end LiftK

def isoMbeSymm {R : Type} [CommRing R] {r : ℕ} {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (γ : IsoMbe Z₁ Z₂) :
    IsoMbe Z₂ Z₁ :=
  ⟨γ.1.symm, by rw [LinearEquiv.symm_apply_eq]; exact γ.2.1.symm,
    by rw [LinearEquiv.symm_apply_eq]; exact γ.2.2.symm⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

