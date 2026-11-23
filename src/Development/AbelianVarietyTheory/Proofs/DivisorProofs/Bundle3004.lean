module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductLevelStructureEqMkPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrderAction_rosati_adjoint : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Adj (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) (GlobalTheory.ZarhinFam.bar d) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (exact GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (intros; apply GlobalTheory.ZarhinFam.AdjPf.adj_actZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrder_isRingAction_on_product : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (exact GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (intros; apply GlobalTheory.ZarhinFam.RAct.actZ_isRAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductLevelStructureEqMkPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProductLevelStructure_eq_mkPoint : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (d h h' : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (κ : Fin 8 → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ), GlobalTheory.ZarhinFam.levZ lev (GlobalTheory.ZarhinFam.incZ A B) (GlobalTheory.ZarhinFam.actZ A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ a = GlobalTheory.ZarhinFam.mkZ A B (fun i => lev (κ (Fin.castAdd 4 i) a)) (fun j => lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
  first | (exact @GlobalTheory.ZarhinFam.levZ_eq_mkZ) | (exact GlobalTheory.ZarhinFam.levZ_eq_mkZ) | (intros; apply GlobalTheory.ZarhinFam.levZ_eq_mkZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFacts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.PtFacts

theorem mkZ_facts : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T T' : Over S} (f : T' ⟶ T) (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (g : T ⟶ GlobalTheory.ZarhinFam.Zob A B) (n : ℕ), f ≫ GlobalTheory.ZarhinFam.mkZ A B u v = GlobalTheory.ZarhinFam.mkZ A B (fun i => f ≫ u i) (fun j => f ≫ v j) ∧ GlobalTheory.ZarhinFam.mkZ A B u v ^ n = GlobalTheory.ZarhinFam.mkZ A B (fun i => u i ^ n) (fun j => v j ^ n) ∧ (GlobalTheory.ZarhinFam.mkZ A B u v = 1 ↔ (∀ i, u i = 1) ∧ ∀ j, v j = 1) ∧ g = GlobalTheory.ZarhinFam.mkZ A B (fun i => g ≫ GlobalTheory.ZarhinFam.pa A B i) (fun j => g ≫ GlobalTheory.ZarhinFam.pb A B j) := by
  intro S A B _ _ _ _ T T' f u v g n
  refine ⟨?_, ?_, ⟨fun h => ⟨fun i => ?_, fun j => ?_⟩, fun ⟨hu, hv⟩ => ?_⟩, ?_⟩
  · apply LevAlg.zob_ext
    · intro i; simp only [Category.assoc, LevAlg.mkZ_pa]
    · intro j; simp only [Category.assoc, LevAlg.mkZ_pb]
  · apply LevAlg.zob_ext
    · intro i; rw [MonObj.pow_comp, LevAlg.mkZ_pa, LevAlg.mkZ_pa]
    · intro j; rw [MonObj.pow_comp, LevAlg.mkZ_pb, LevAlg.mkZ_pb]
  · rw [← LevAlg.mkZ_pa A B u v i, h, MonObj.one_comp]
  · rw [← LevAlg.mkZ_pb A B u v j, h, MonObj.one_comp]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa, MonObj.one_comp, hu]
    · intro j; rw [LevAlg.mkZ_pb, MonObj.one_comp, hv]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa]
    · intro j; rw [LevAlg.mkZ_pb]

end GlobalTheory.ZarhinFam.PtFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClausesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProduct_relation_algebraic_clauses : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  first | (exact @GlobalTheory.ZarhinFam.zRel_alg) | (exact GlobalTheory.ZarhinFam.zRel_alg) | (intros; apply GlobalTheory.ZarhinFam.zRel_alg  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinSymplecticTransferBijectiveModStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod : ∀ (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), 1 ≤ M → GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a, (∀ k, ∃ b, κ k a = M • b) ↔ ∃ b, a = M • b) ∧ ∀ cc : Fin 8 → (Fin h ⊕ Fin h → ℤ), ∃ a, ∀ k, ∃ b, κ k a = cc k + M • b := by
  first | (exact @GlobalTheory.ZarhinFam.kappaOK_mod) | (exact GlobalTheory.ZarhinFam.kappaOK_mod) | (intros; apply GlobalTheory.ZarhinFam.kappaOK_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef
section
open Matrix

namespace GlobalTheory.ZarhinFam

theorem zW_symm_blocks (d : ℕ) (i j : Fin 4 ⊕ Fin 4) :
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 i j +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 j i =
    2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1 i j := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.zero_apply, smul_eq_mul]
  all_goals (try simp only [@eq_comm _ b a])
  all_goals (try split_ifs)
  all_goals ring

theorem zarhin_block_posDef {d : ℕ} (hd : 0 < d) :
    (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
      (Int.cast : ℤ → ℝ) |>.PosDef := by
  set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx
  have hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢
    rw [h0]
    split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]
  set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC
  set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'
  have hCC : C' * C = 1 := by
    rw [hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg (C'.mulVec) hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C =
      (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
        (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
    congr 1
    · rw [Matrix.transpose_one, Matrix.one_mul, hxx]; ext i j
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    · simp [hx, Matrix.transpose_map]
    · simp [hx]
    · simp
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

theorem zW_symm_posDef : ∀ (d : ℕ), 0 < d →
    ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  intro d hd
  have hsig : Function.Injective sig := by
    intro a b h; revert a b h; decide
  have h := ((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e := zW_symm_blocks d (sig k) (sig l)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

end GlobalTheory.ZarhinFam
end

