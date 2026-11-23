module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0105
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.TwistLG

open Formalism.MainNotions.SumRepresentations.At

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have h1 := W.smul_mem (((χ g)⁻¹ : kˣ) : k) (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at h1
    exact h1
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 h1, h2⟩

theorem cont_twGL [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_val]
  refine Continuous.smul (M := k) ?_ hρ
  have e : ∀ g, (((Matrix.GeneralLinearGroup.det.comp χ) g : kˣ) : k) =
      (χ g : Matrix (Fin 1) (Fin 1) k).det := fun g => rfl
  simp only [e]
  exact hχ.matrix_det

theorem charpoly_eq_of_dense [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Infinite k] (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem etaT_char_etaTinv (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} := by
  have u1 := A.etaT_unr w
  obtain ⟨u2, f2⟩ := A.etaTinv_def w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  obtain ⟨b, hb⟩ : ∃ b, A.frobEig (A.locG A.etaT w) = {b} :=
    Multiset.card_eq_one.mp (by rw [A.frobEig_card _ u1, A.locG_dim])
  have hb0 : b ≠ 0 := by
    intro h0
    apply A.frobEig_ne_zero _ u1
    rw [hb, h0]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at f2
  have hu := A.unr_char _ _ d2 u1 u2
  have hf := A.frobEig_char _ _ b⁻¹ u1 u2 d2 f2
  rw [hb, Multiset.map_singleton, mul_inv_cancel₀ hb0] at hf
  rw [A.unr_eq_lpUnr _ hu, hf]

theorem param_twist (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u s : ℝ) :
    A.lpChar (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpTw (A.locG A.etaTinv w) s) =
      A.lpTw (A.locG π w) (s + u) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  have c3 := (hLP w (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) s d2 d2).2.2.1
  have c2 := (hLP w (A.locG (A.tw π A.etaT) w) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) u
    d2 d2).2.1
  have c4 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3, c2, A.lpTw_add, A.locG_tw, c4, etaT_char_etaTinv N A w, c5, add_comm]

end Glob

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end Main

end GlobalTheory.TwistLG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceDiv

section Abstract

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem single_mem (j i : n) : (Pi.single j (1 : R) : n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simpa using O.one_mem
  · simpa [Pi.single_eq_of_ne h] using O.zero_mem

theorem exists_factor (P Q : Matrix n n R)
    (H : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ P.mulVec y = Q.mulVec z) :
    ∃ M : Matrix n n O, P = Q * M.map O.subtype := by
  choose z hz1 hz2 using fun j => H (Pi.single j 1) (single_mem O j)
  refine ⟨Matrix.of fun i j => ⟨z j i, hz1 j i⟩, ?_⟩
  ext i j
  have := congrFun (hz2 j) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this]
  rfl

theorem mem_range_of_mul_eq_one (M N : Matrix n n O) (h : M.map O.subtype * N.map O.subtype = 1) :
    ∃ k ∈ (Formalism.UG.bc (n := n) O.subtype).range, k.1 = M.map O.subtype := by
  have h1 : M * N = 1 := by
    apply Matrix.map_injective O.subtype_injective
    simp only [Matrix.map_mul]
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨_, ⟨⟨M, N, h1, mul_eq_one_comm.1 h1⟩, rfl⟩, rfl⟩

theorem double_coset (B m T T' : Matrix n n R) (hT : T' * T = 1)
    (h1 : ∀ z : n → R, (∀ i, z i ∈ O) → ∀ i, B.mulVec z i ∈ O)
    (h2 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ y = B.mulVec z)
    (h3 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ m.mulVec y = (B * T).mulVec z)
    (h4 : ∀ z : n → R, (∀ i, z i ∈ O) → ∃ y : n → R, (∀ i, y i ∈ O) ∧ m.mulVec y = (B * T).mulVec z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := n) O.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := n) O.subtype).range,
      m = k₁.1 * T * k₂.1 := by
  obtain ⟨B0, hB0⟩ := exists_factor O B 1 fun y hy => ⟨_, h1 y hy, by rw [Matrix.one_mulVec]⟩
  rw [Matrix.one_mul] at hB0
  obtain ⟨C, hC⟩ := exists_factor O 1 B fun y hy => by rw [Matrix.one_mulVec]; exact h2 y hy
  obtain ⟨M, hM⟩ := exists_factor O m (B * T) h3
  obtain ⟨N, hN⟩ := exists_factor O (B * T) m fun z hz => (h4 z hz).imp fun y hy => ⟨hy.1, hy.2.symm⟩
  have hCB : C.map O.subtype * B = 1 := mul_eq_one_comm.1 hC.symm
  have hinv : T' * C.map O.subtype * (B * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ B, hCB, Matrix.one_mul, hT]
  have hMN : M.map O.subtype * N.map O.subtype = 1 := by
    have e : B * T * (M.map O.subtype * N.map O.subtype) = B * T := by
      rw [← Matrix.mul_assoc, ← hM, ← hN]
    calc _ = T' * C.map O.subtype * (B * T) * (M.map O.subtype * N.map O.subtype) := by
          rw [hinv, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc, e, hinv]
  obtain ⟨k₁, hk₁, e₁⟩ := mem_range_of_mul_eq_one O B0 C (by rw [← hB0, ← hC])
  obtain ⟨k₂, hk₂, e₂⟩ := mem_range_of_mul_eq_one O M N hMN
  exact ⟨k₁, hk₁, k₂, hk₂, by rw [e₁, e₂, ← hB0, hM]⟩

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sgT_mem_intA (v : HeightOneSpectrum (𝓞 F)) {y : Fv F v ⊗[F] E} (hy : y ∈ ordAt E v) :
    sgT E v y ∈ intA F E := by
  refine (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).2 fun w => ?_
  by_cases h : w = v
  · subst h; rwa [evF_sgT_self]
  · rw [evF_sgT_ne h]; exact zero_mem _

theorem sgT_mem_lamHat [StarRing E] (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    (fun i => sgT E v (y i)) ∈ lamHat F V := by
  refine (mem_lamHat_iff V _).2 fun w => ?_
  by_cases h : w = v
  · subst h; simpa only [evF_sgT_self] using hy
  · simp only [evF_sgT_ne h]; exact zero_mem _

omit [NumberField E] in
theorem evF_mulVec {n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F)) {f : Af F ⊗[F] E} (hf : evF E v f = 1)
    (A : Matrix n n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    (fun a => evF E v (f * A.mulVec z a)) = (A.map (evF E v)).mulVec fun i => evF E v (z i) := by
  funext a
  rw [map_mul, hf, one_mul, RingHom.map_mulVec]
  rfl

theorem double_coset_of_divG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  intro F E _ _ _ _ _ _ hc V v e h ϖ d g he hh hϖ ⟨B, h1, h2, h3, h4⟩
  have he1 := he.2.1
  have hfr : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y i ∈ ordAt E v) →
      h.1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := fun y hy => by
    refine (hh _).2 ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hy
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1.mulVec ((h⁻¹).1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1.mulVec (h.1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have key : ∀ y z : Fin V.rank → Af F ⊗[F] E,
      ((fun a => finP F E e * (finMat hc.sig V.gram g).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) →
      (locMat hc V v g).1.mulVec (fun i => evF E v (y i)) =
        (B.map (evF E v) * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec fun i => evF E v (z i) := by
    intro y z hyz
    rw [locMat_val, ← evF_mulVec v he1, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec (fun i => evF E v (z i)) =
        fun i => evF E v (finP F E (inclR (AF F) (ϖ ^ d i)) * z i) := by
      funext i
      rw [Matrix.mulVec_diagonal, map_mul, evF_finP_incl]
    rw [e2, ← evF_mulVec v he1]
    funext a
    rw [congrFun hyz a]
  refine double_coset (ordAt E v) ((h⁻¹).1 * B.map (evF E v)) _ _
    (Matrix.diagonal fun i => inclR (Fv F v) (ϖ ^ d i)⁻¹) ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ), map_one]
  · intro z hz
    have := (mem_lamHat_iff V _).1 (h1 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)) v
    rw [evF_mulVec v he1] at this
    simp only [evF_sgT_self] at this
    rw [← Matrix.mulVec_mulVec]
    exact (hh _).1 this
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h2 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← evF_mulVec v he1, ← hback' y]
    congr 1; funext a
    rw [← congrFun e2 a, map_mul, he1, one_mul, evF_sgT_self]
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h3 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · intro z hz
    obtain ⟨y, hy, e2⟩ := h4 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)
    refine ⟨(h⁻¹).1.mulVec fun i => evF E v (y i), (hh _).1 ((mem_lamHat_iff V _).1 hy v), ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hback]

end GlobalTheory.PlaceDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
section
noncomputable section

namespace GlobalTheory.GoodDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem charSum_of_tie (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut)
    (hc : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b) :
    GlobalTheory.LiftLeaf.CharSum D.nd D.naut := by
  intro w a b χ s hχ
  obtain ⟨h1, h2, -⟩ := hT w a b χ χ s hχ hχ
  refine ⟨h1, h2, ?_⟩
  have h := (hT w (D.naut.lpZero w) (D.naut.lpZero w) χ χ 0 hχ hχ).1
  rw [D.naut.lpSum_zero] at h
  refine hc w _ _ (D.naut.lpChar (D.naut.lpZero w) χ) ?_
  rw [← h, D.naut.lpSum_comm, D.naut.lpSum_zero]

theorem lpChar_eta_back (D : D7) (hT : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut) (w : PlE D.host) (a : D.naut.LP w) :
    D.naut.lpChar (D.naut.lpChar a (D.naut.locG D.naut.etaTinv w)) (D.naut.locG D.naut.etaT w) = a := by
  have hu := D.naut.etaT_unr w
  obtain ⟨hu', he⟩ := D.naut.etaTinv_def w
  have hcard := D.naut.frobEig_card _ hu
  rw [D.naut.locG_dim] at hcard
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hc0 : c ≠ 0 := by
    intro h0
    apply D.naut.frobEig_ne_zero _ hu
    rw [hc, h0]
    exact Multiset.mem_singleton_self _
  rw [hc, Multiset.map_singleton] at he
  have key := GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c hu' hu (D.naut.locG_dim _ w) he hc
    (inv_mul_cancel₀ hc0)
  obtain ⟨-, -, -, h4, h5, -⟩ := hT w a a (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0
    (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)
  rw [h4, key, h5]

end GlobalTheory.GoodDepthZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTieLP

open GlobalTheory.WeilDeligne

theorem matrix_charpoly_smul {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (c : ℂ) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  by_cases hc : c = 0
  · subst hc
    ext i
    rw [zero_smul, Matrix.charpoly_zero, coeff_scaleRoots, M.charpoly_natDegree_eq_dim, coeff_X_pow]
    by_cases hi : i = Fintype.card n
    · subst hi
      have := M.charpoly_monic.coeff_natDegree
      rw [M.charpoly_natDegree_eq_dim] at this
      simp [this]
    · rcases lt_or_gt_of_ne hi with h | h
      · have : Fintype.card n - i ≠ 0 := by omega
        simp [hi, this]
      · simp [hi, coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by rwa [M.charpoly_natDegree_eq_dim])]
  · apply Polynomial.funext
    intro t
    have h1 : (M.charpoly.scaleRoots c).eval (c * (t / c)) = c ^ M.charpoly.natDegree * M.charpoly.eval (t / c) := by
      simpa using scaleRoots_eval₂_mul (RingHom.id ℂ) (t / c) c (p := M.charpoly)
    rw [mul_div_cancel₀ _ hc, M.charpoly_natDegree_eq_dim] at h1
    rw [h1, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
    split_ifs <;> field_simp

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, matrix_charpoly_smul,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_line {V L : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L] (hL : Module.finrank ℂ L = 1)
    (f : Module.End ℂ V) (c : ℂ) :
    (TensorProduct.map f (c • (1 : Module.End ℂ L))).charpoly = f.charpoly.scaleRoots c := by
  let e : L ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq L ℂ (by simp [hL])
  let E : TensorProduct ℂ V L ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ x, E (TensorProduct.map f (c • (1 : Module.End ℂ L)) x) = (c • f) (E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v l =>
      simp [E, TensorProduct.map_tmul, smul_comm c, map_smul]
  have h2 : E.conj (TensorProduct.map f (c • (1 : Module.End ℂ L))) = c • f := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := E.surjective v
    simpa [LinearEquiv.conj_apply] using key x
  rw [← charpoly_smul_end, ← h2, LinearEquiv.charpoly_conj]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_char {a c : WD h} (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (a.inePol σ).scaleRoots z := by
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    rw [WD.lpDim_mk] at hc
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk,
      WDRep.tensor_ρ, h1, charpoly_map_line hc]

end GlobalTheory.RowTieLP

theorem GlobalTheory.RowTieLP.main : ∀ (D : D7), WDTie D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut := by
  intro D T w a b χ χ' s h1 h2
  obtain ⟨l1, l2, l3, l4, l5⟩ := (_root_.GlobalTheory.RowLaws.main _ _ _ _ _ T).2.1 w a b χ χ' s h1 h2
  refine ⟨l1, l2, l3, l4, l5, fun σ hσ => ⟨⟨?_, ?_⟩, fun c hc => ?_⟩⟩
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
    exact GlobalTheory.WeilDeligne.WD.charPol_monic _ _
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.charPol_natDegree, T.dim]
  · rw [T.inePol w χ σ hσ] at hc
    have hd : (T.e w χ).lpDim = 1 := by rw [T.dim, h1]
    rw [T.inePol w _ σ hσ, T.char _ _ _ h1, T.inePol w a σ hσ]
    exact GlobalTheory.RowTieLP.inePol_char hd hσ hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueEqOfGenerators
section
namespace GlobalTheory.ClassResidueGenerators

theorem residue_eq_of_generators {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    (S : Set A) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O)
    (h : ∀ (a : A) (ha : a ∈ S),
      IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin ha⟩) =
        IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin ha⟩))
    (x : A) (hx : x ∈ Algebra.adjoin O S) :
    IsLocalRing.residue O (ψ ⟨x, hx⟩) = IsLocalRing.residue O (ψ' ⟨x, hx⟩) := by
  induction hx using Algebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap r =>
    have e : (⟨algebraMap O A r, Subalgebra.algebraMap_mem _ r⟩ : ↥(Algebra.adjoin O S)) =
        algebraMap O _ r := rfl
    rw [e, ψ.commutes, ψ'.commutes]
  | add a b ha hb iha ihb =>
    have e : (⟨a + b, add_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), iha, ihb]
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, mul_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_mul, iha, ihb]

theorem cls_eq_of_generators : ∀ {O K V : Type} [inst : CommRing O] [inst_1 : Field K] [inst_2 : Algebra O K] [inst_3 : AddCommGroup V] [inst_4 : Module K V] [inst_5 : Module O V] [inst_6 : IsScalarTower O K V] [inst_7 : IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O), (∀ (a : Module.End K V) (h : a ∈ S), (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S))) = (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ' : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S)))) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  intro O K V _ _ _ _ _ _ _ _ S ψ ψ' h
  unfold Formalism.L2.NCov.cls
  congr 1
  ext ⟨x, hx⟩
  exact residue_eq_of_generators S ψ ψ' h x hx

end GlobalTheory.ClassResidueGenerators
end

