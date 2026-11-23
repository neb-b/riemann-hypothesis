module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped TensorProduct InnerProductSpace Classical Kronecker
open GlobalTheory.Chain.IoLift

noncomputable section

namespace GlobalTheory.Chain.IoLift.UImg

variable {p q : ℕ}

def sumAct (M : GKMod p q) (Y : Type) : Mat p q →ₗ[ℂ] Module.End ℂ (Y →₀ M.V) where
  toFun X := Finsupp.mapRange.linearMap (M.act X)
  map_add' X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp
  map_smul' c X := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp

theorem sumAct_apply (M : GKMod p q) (Y : Type) (X : Mat p q) (v : Y →₀ M.V) (y : Y) :
    sumAct M Y X v y = M.act X (v y) := by
  simp [sumAct]

theorem sumAct_single (M : GKMod p q) (Y : Type) (X : Mat p q) (y : Y) (x : M.V) :
    sumAct M Y X (Finsupp.single y x) = Finsupp.single y (M.act X x) := by
  simp [sumAct]

def sumMod (M : GKMod p q) (Y : Type) : GKMod p q where
  V := Y →₀ M.V
  act := sumAct M Y
  lie X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    rw [sumAct_apply, M.lie X X']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply, sumAct_apply]
  kfin v := by
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
        rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]⟩
    | add f g hf hg =>
      obtain ⟨W, hW, hf, hK⟩ := hf
      obtain ⟨W', hW', hg, hK'⟩ := hg
      refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup hf hg, fun X hX w hw => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hK X hX a ha) (hK' X hX b hb)
    | single y x =>
      obtain ⟨W, hW, hx, hK⟩ := M.kfin x
      refine ⟨W.map (Finsupp.lsingle y), inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
      rintro X hX _ ⟨w, hw, rfl⟩
      rw [Finsupp.lsingle_apply, sumAct_single]
      exact Submodule.mem_map_of_mem (f := Finsupp.lsingle y) (hK X hX w hw)
  wts v := by
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => exact Submodule.add_mem _ hf hg
    | single y x =>
      have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
          (⨆ μ : Ix p q → ℚ, wtSub (sumAct M Y) μ).comap (Finsupp.lsingle y) := by
        refine iSup_le fun μ x hx => ?_
        rw [Submodule.mem_comap]
        refine Submodule.mem_iSup_of_mem μ ?_
        simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
        intro a
        rw [Finsupp.lsingle_apply, sumAct_single, Finsupp.smul_single, ← Finsupp.single_sub, hx a,
          Finsupp.single_zero]
      exact h (M.wts x)

def fockMod (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie X X' := by
    have h : ∀ U : Mat p q, fockAct1 p q r s U = omAct p q r s (U ⊗ₖ (1 : Mat r s)) := fun _ => rfl
    rw [map_sub]
    simp only [h]
    rw [← GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, map_sub]
  kfin P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
  wts P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2

theorem exists_unitary_image (M : GKMod p q) (Y Z : Type) [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z)
    (hB : ∀ (X : Mat p q) P P' y y',
      ⟪B (M.act X P) y, B P' y'⟫_ℂ = ⟪B P y, B (M.act (adjZ X) P') y'⟫_ℂ) :
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧
        Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (M.act X P) y = A.M.act X (B' P y) := by
  let E : (Y →₀ M.V) →ₗ[ℂ] Z := Finsupp.lsum ℂ fun y => B.flip y
  have hE1 : ∀ y P, E (Finsupp.single y P) = B P y := fun y P => by
    simp [E]
  have hE : ∀ X (x x' : Y →₀ M.V), ⟪E (sumAct M Y X x), E x'⟫_ℂ =
      ⟪E x, E (sumAct M Y (adjZ X) x')⟫_ℂ := by
    intro X x x'
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), inner_add_left, hf, hg]
    | single y P =>
      induction x' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add (f := _), inner_add_right, hf, hg]
      | single y' P' => simp only [sumAct_single, hE1, hB]
  obtain ⟨A, f, j, hf, hj, hjf, hact⟩ :=
    GlobalTheory.GKQuot.exists_unitary_quotient p q (sumMod M Y) Z E hE
  let g : (Y →₀ M.V) →ₗ[ℂ] A.M.V := f
  have hjg : ∀ y P, j (g (Finsupp.single y P)) = B P y := fun y P => (hjf _).trans (hE1 y P)
  let B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => g (Finsupp.single y P))
      (fun P P' y => by rw [Finsupp.single_add, map_add (f := _)])
      (fun c P y => by rw [← Finsupp.smul_single, map_smul, RingHom.id_apply])
      (fun P y y' => hj (by rw [map_add (f := _), hjg, hjg, hjg, map_add (f := _)]))
      (fun c P y => hj (by rw [map_smul, hjg, hjg, map_smulₛₗ]))
  have hB' : ∀ P y, B' P y = g (Finsupp.single y P) := fun _ _ => rfl
  refine ⟨A, j, B', hj, fun P y => hjg y P, ?_, fun X P y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ : ∃ v, g v = x := hf x
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | single y P => exact Submodule.subset_span ⟨P, y, rfl⟩
  · rw [hB', hB', ← sumAct_single]
    exact hact X _

theorem unitaryImage : ∀ p q r s : ℕ, UnitaryImage p q r s :=
  fun p q r s Y Z _ _ _ _ B hB => exists_unitary_image (fockMod p q r s) Y Z B hB

end GlobalTheory.Chain.IoLift.UImg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped GlobalTheory.MixModel

namespace GlobalTheory.WittSect

theorem sub_one_mulVec_eq_zero {R : Type*} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R) (v : Fin n → R) (p : Fin a → R) (q : Fin b → R)
    (hv : v = P *ᵥ p + Q *ᵥ q) (hP : M * P = P) (hQ : M * Q = Q) : (M - 1) *ᵥ v = 0 := by
  rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP, hQ,
    sub_self]

theorem exists_hypDec_mem_NI : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B →
    ∃ d : GlobalTheory.MixModel.HypDec V V' r, d.e = C ∧ d.i₀ = B ∧ ∀ m : GA D V,
      HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = C.map (incA D) →
      HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = B.map (incA D) → m ∈ NI V C := by
  intro D V V' r C B hs
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D M = Mᴴ := fun _ => rfl
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  rw [e] at h1 h2 h3
  have hee : Cᴴ * V.gram * C = 0 := hs.frame.2.2
  have horth : Cᴴ * V.gram * B = 0 := by rw [← e]; exact hs.orth
  have hiso : Bᴴ * V.gram * B = V'.gram := by rw [← e]; exact hs.isom
  have h1' : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose horth
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  let d : GlobalTheory.MixModel.HypDec V V' r :=
    { e := C, e' := C', i₀ := B, ee := hee, e'e' := h2, e'e := h1', iso := hiso, i₀e := h0e, i₀e' := h0e',
      rank_add := hs.rank.symm }
  refine ⟨d, rfl, rfl, fun m hC hB => Subgroup.subset_closure ?_⟩

  have hu := GlobalTheory.MixModel.mt_unitary V m
  have hsum : C * (C'ᴴ * V.gram) + B * (V'.gram⁻¹ * (Bᴴ * V.gram)) + C' * (Cᴴ * V.gram) = 1 :=
    d.sum_eq_one_rat
  have hCm : GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    calc GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m
        = GlobalTheory.MixModel.adj (mt V m * C.map (incA D)) * GlobalTheory.MixModel.gA V * mt V m := by rw [hC]
      _ = GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.adj (mt V m) * (GlobalTheory.MixModel.gA V * mt V m)) := by
          simp only [GlobalTheory.MixModel.adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hu]
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · change (mt V m - 1) * C.map (incA D) = 0
    rw [Matrix.sub_mul, hC, Matrix.one_mul, sub_self]
  · rw [Matrix.map_mul]
    change GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V * (mt V m - 1) = 0
    rw [Matrix.mul_sub, hCm, Matrix.mul_one, sub_self]
  · intro x hx
    refine ⟨0, ?_⟩
    rw [Matrix.mulVec_zero]
    have hx0 : (Cᴴ * V.gram) *ᵥ x = 0 := hx
    obtain ⟨u, hu⟩ : ∃ u, u = (C'ᴴ * V.gram) *ᵥ x := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (V'.gram⁻¹ * (Bᴴ * V.gram)) *ᵥ x := ⟨_, rfl⟩
    have hx' : x = C *ᵥ u + B *ᵥ w := by
      have := congrArg (fun M => M *ᵥ x) hsum
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec (M := C),
        ← Matrix.mulVec_mulVec (M := B), ← Matrix.mulVec_mulVec (M := C'), hx0, Matrix.mulVec_zero, add_zero] at this
      rw [hu, hw]; exact this.symm
    have hxA : (fun i => incA D (x i)) = C.map (incA D) *ᵥ (incA D ∘ u) + B.map (incA D) *ᵥ (incA D ∘ w) := by
      funext i
      have hi : x i = (C *ᵥ u) i + (B *ᵥ w) i := congrFun hx' i
      have ha := RingHom.map_mulVec (incA D) C u i
      have hb := RingHom.map_mulVec (incA D) B w i
      rw [Pi.add_apply, ← ha, ← hb, hi]
      exact RingHom.map_add (incA D) _ _
    refine sub_one_mulVec_eq_zero _ (C.map (incA D)) (B.map (incA D)) _ (incA D ∘ u) (incA D ∘ w) ?_ ?_ ?_
    · exact hxA
    · exact hC
    · exact hB

end GlobalTheory.WittSect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtFock

section Perm

variable {n : ℕ} (π : Fin n → Fin n)

theorem submatrix_eq_mul (P : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π = P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply]

variable {π}

theorem perm_mul_self (hπ : ∀ a, π (π a) = a) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
  simp [mul_ite, Finset.sum_ite_eq', hπ]

theorem perm_single_perm (hπ : ∀ a, π (π a) = a) (c d : Fin n) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.single c d 1 * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.single (π c) (π d) 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.single_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  have key : ∀ x y, x = π y ↔ π x = y := fun x y => ⟨fun h => by rw [h, hπ], fun h => by rw [← h, hπ]⟩
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [key d b]
  by_cases h1 : π c = a
  · subst h1; simp
  · have h2 : ¬ a = π c := fun h => h1 h.symm
    simp [h1, h2]

theorem perm_diag_perm (hπ : ∀ a, π (π a) = a) (t : Fin n → ℂ) :
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * Matrix.diagonal t * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π =
      Matrix.diagonal (fun a => t (π a)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, Matrix.diagonal_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, hπ]
  split_ifs with h
  · rw [h]
  · rfl

theorem conj_submatrix (hπ : ∀ a, π (π a) = a) (P X : Matrix (Fin n) (Fin n) ℂ) :
    P.submatrix id π * X * (P.submatrix id π)⁻¹ =
      P * ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π * X * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id π) * P⁻¹ := by
  rw [submatrix_eq_mul π P, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (perm_mul_self hπ)]
  simp only [Matrix.mul_assoc]

end Perm

theorem killPair_rev {n p : ℕ} (hpn : p ≤ n) {c d : Fin n} (h : d < c) :
    GlobalTheory.HolRead.KillPair (fun a : Fin n => decide ((a : ℕ) < p)) (GlobalTheory.AdSpan.revPos p c) (GlobalTheory.AdSpan.revPos p d) := by
  have hdc : (d : ℕ) < c := h
  unfold GlobalTheory.HolRead.KillPair GlobalTheory.AdSpan.revPos
  by_cases hc : (c : ℕ) < p <;> by_cases hd : (d : ℕ) < p
  · left
    simp only [dif_pos (And.intro hc hpn), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, by omega⟩
  · omega
  · right; right
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_pos (And.intro hd hpn), Fin.lt_def]
    refine ⟨by simp; omega, by omega⟩
  · right; left
    simp only [dif_neg (fun h' : (c : ℕ) < p ∧ p ≤ n => hc h'.1), dif_neg (fun h' : (d : ℕ) < p ∧ p ≤ n => hd h'.1), Fin.lt_def]
    refine ⟨by simp; omega, by simp; omega, hdc⟩

end GlobalTheory.ExtFock

namespace GlobalTheory.ExtFock


open GlobalTheory.HolRead.ExtKill in
set_option maxHeartbeats 4000000 in
theorem ext_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (p : ℕ), (∀ τ, ((Wc D i).sig (tauE D τ)).1 = p) → p ≤ (Wc D i).rank → IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ) → ∀ T ∈ R.Wall i (sg0 D A), LowKilled R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) (T fun ρ => u ρ) ∧ ∀ (ρ : D.what₂.Tau) (s : Fin (Wc D i).rank → ℝ), ∃ l : ℂ, R.ωP i t (1, torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) = l • R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w) ∧ ∀ g, T (fun ρ => u ρ) (g * torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s) = l * T (fun ρ => u ρ) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hP i t u w p hp hpn hext T hT
  have hTm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  have hεd : ∀ ρ, (R.MW i (sg0 D A)).ε ρ = fun a : Fin (Wc D i).rank => decide ((a : ℕ) < p) := by
    intro ρ; funext a; rw [hM.order i ρ a, hp ρ]
  have hε : ∀ ρ (a : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε ρ a = if (a : ℕ) < p then true else !true := by
    intro ρ a; rw [hεd ρ]; by_cases h : (a : ℕ) < p <;> simp [h]
  let V := Wc D i
  let M := R.MW i (sg0 D A)
  let v : M.Vec := fun ρ => u ρ
  have KW (ρ : D.what₂.Tau) :
      (∀ a b, GlobalTheory.HolRead.KillPair (M.ε ρ) a b →
        RderC R.θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧
      ∀ (s : Fin V.rank → ℝ) (g : GA D V),
        T v (g * atTau R.θ V ρ ((M.fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) * M.fr ρ)) =
        Complex.exp (((∑ a, extWt M ρ a * s a : ℝ) : ℂ) * Complex.I) * T v g := by
    have hFrame := M.fr_unit ρ
    have hGram := M.fr_gram ρ
    obtain ⟨-, hlow, hwt⟩ := hext ρ
    have hlow' : (v ρ : M.H ρ) ∈ Formalism.MainNotions.S.lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
    refine ⟨fun a b hab => ?_, fun s g => ?_⟩
    · have hs := GlobalTheory.HolRead.MultDer.smoothVec_of_mem M ρ (v ρ).2
      have hd (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V ρ) :
          ∃ z : M.sm ρ, (z : M.H ρ) = dRep (M.rep ρ) X (v ρ : M.H ρ) ∧
            Rder R.θ V ρ X (T v) = T (Function.update v ρ z) := by
        have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V ρ
        have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V ρ
        have hRep := (GlobalTheory.HolDict.ModelRep.model_rep D V _ M ρ).2.1
        obtain ⟨hOrbit, -, hDeriv⟩ :=
          _root_.GlobalTheory.SmVecCalc.smooth_calculus _ _ _ _ hH hU hRep _ hs
        refine ⟨⟨_, Submodule.subset_span (hDeriv X hX).1⟩, rfl, ?_⟩
        funext x
        obtain ⟨ℓ, hℓ, hℓT⟩ := hTm.cont ρ v x
        have hDerivAt :=
          _root_.GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit _ _ _ _ hH hU hRep _ hs ℓ hℓ X hX
        rw [← hℓT]
        have e : (fun t : ℝ => T v (x * oneP R.θ V ρ X t)) =
            fun t : ℝ => ℓ (M.rep ρ (NormedSpace.exp (t • X)) (v ρ : M.H ρ)) := by
          funext t
          have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
          let z : M.sm ρ := ⟨_, Submodule.subset_span (hOrbit _ hg)⟩
          have hEquiv := congrFun (hTm.equiv ρ _ hg v z rfl) x
          exact ((hℓT z).trans hEquiv).symm
        show deriv (fun t : ℝ => T v (x * oneP R.θ V ρ X t)) 0 = _
        rw [e]
        exact hDerivAt.deriv
      have hs' := smoothVec_conj (σ := M.σ ρ) hFrame hGram hs
      set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
      obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
      have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
      unfold RderC
      generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
      generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
      obtain ⟨z, hz, ez⟩ := hd X hX
      obtain ⟨z', hz', ez'⟩ := hd Y hY
      have hX' := lie_conj hFrame hGram hX
      have hY' := lie_conj hFrame hGram hY
      have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) =
          Matrix.single a b 1 := by
        rw [← conj_cancel hFrame (Matrix.single a b 1), ← hZ, ← hXY]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
          Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
        rcases hab with h | h | h
        · exact _root_.GlobalTheory.HolRead.KCpt.extremal_killed_compact _ _ _ _ _
            (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
        · exact _root_.GlobalTheory.HolRead.KCpt.extremal_killed_compact _ _ _ _ _
            (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
        · exact _root_.GlobalTheory.LowestKilled.lowK_killed _ _ _ _ _ p true
            (hε ρ) (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
      have h0 : z + Complex.I • z' = 0 := by
        apply Subtype.ext
        show (z : M.H ρ) + Complex.I • (z' : M.H ρ) = 0
        rw [hz, hz', ← key, ← dRep_conj hFrame, ← dRep_conj hFrame]
        rfl
      have hSmul : T (Function.update v ρ (Complex.I • z')) =
          Complex.I • T (Function.update v ρ z') := by
        simpa only [RingHom.id_apply] using T.map_update_smul v ρ Complex.I z'
      rw [ez, ez', ← hSmul, ← T.map_update_add v ρ z (Complex.I • z'), h0, T.map_update_zero]
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) s
      have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hFrame hGram (kset_uj hK)
      have h := hTm.equiv ρ _ hg v
        (Complex.exp (((∑ a, extWt M ρ a * s a : ℝ) : ℂ) * Complex.I) • v ρ) (by
          unfold DSModel.rep
          rw [conj_cancel hFrame, hwt s hK]
          rfl)
      rw [T.map_update_smul, Function.update_eq_self] at h
      exact (congrFun h g).symm
  have hπ : ∀ a : Fin (Wc D i).rank, revPos p (revPos p a) = a := revPos_revPos p
  have hinv : ∀ ρ, ((onb (R.MW i (sg0 D A)) ρ))⁻¹ = (R.MW i (sg0 D A)).fr ρ := fun ρ =>
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))
  refine ⟨⟨(hTm.aut _).smooth, fun ρ c d hdc => ?_⟩, fun ρ s => ?_⟩
  · have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.single c d 1 * (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.single (revPos p c) (revPos p d) 1 * (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_single_perm hπ, hinv]
      rfl
    rw [e]
    apply (KW ρ).1
    rw [hεd ρ]
    exact killPair_rev hpn hdc
  · set l : ℂ := Complex.exp (((∑ a, extWt (R.MW i (sg0 D A)) ρ a * s (revPos p a) : ℝ) : ℂ) * Complex.I) with hl
    have e : revB p (onb (R.MW i (sg0 D A))) ρ * Matrix.diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) *
        (revB p (onb (R.MW i (sg0 D A))) ρ)⁻¹ =
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) *
          (R.MW i (sg0 D A)).fr ρ := by
      show (onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p) * _ * ((onb (R.MW i (sg0 D A)) ρ).submatrix id (revPos p))⁻¹ = _
      rw [conj_submatrix hπ, perm_diag_perm hπ, hinv]
      rfl
    have htor : torAt R.θ (Wc D i) (revB p (onb (R.MW i (sg0 D A)))) ρ s =
        atTau R.θ (Wc D i) ρ (((R.MW i (sg0 D A)).fr ρ)⁻¹ *
          Matrix.diagonal (fun a => Complex.exp ((s (revPos p a) : ℂ) * Complex.I)) * (R.MW i (sg0 D A)).fr ρ) := by
      unfold torAt; rw [e]
    refine ⟨l, ?_, fun g => ?_⟩
    · have hK := Formalism.IndefR.FWT.diag_mem (ε := (R.MW i (sg0 D A)).ε ρ) (fun a => s (revPos p a))
      obtain ⟨-, -, hwt⟩ := hext ρ
      have h2 := (hP.ioP i t).2.1 ρ _ hK u (l • u ρ) (by
        show l • (((u ρ : (R.MW i (sg0 D A)).sm ρ)) : (R.MW i (sg0 D A)).H ρ) = _
        rw [hwt _ hK]) w
      rw [htor, h2, MultilinearMap.map_update_smul, Function.update_eq_self, map_smul, LinearMap.smul_apply]
      unfold RealDat.ptP
      exact map_smul _ _ _
    · rw [htor]
      exact (KW ρ).2 _ g

end GlobalTheory.ExtFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdeleTensorCoordsMulDenominatorBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordDenom

theorem finCoord_mul_denom : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  intro D
  set B := Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E) with hB
  obtain ⟨c, hc, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (GlobalTheory.HolDict.ShortVec.intRing D.host.F)
    (fun p : Fin (Module.finrank D.host.F D.host.E) × Fin (Module.finrank D.host.F D.host.E) ×
      Fin (Module.finrank D.host.F D.host.E) => B.repr (B p.1 * B p.2.1) p.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  refine ⟨c, hc, fun e₁ e₂ a b ha hb k => ?_⟩
  have ha' : ∀ i, (e₁ : Af D.host.F) * B.repr a i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := ha
  have hb' : ∀ i, (e₂ : Af D.host.F) * B.repr b i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := hb
  change ((c * e₁ * e₂ : ℕ) : Af D.host.F) * B.repr (a * b) k ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr a, ← B.sum_repr b, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e : ((c * e₁ * e₂ : ℕ) : Af D.host.F) * (B.repr a i * B.repr b j * B.repr (B i * B j) k) =
      ((e₁ : Af D.host.F) * B.repr a i) * ((e₂ : Af D.host.F) * B.repr b j) * ((c : Af D.host.F) * B.repr (B i * B j) k) := by
    push_cast; ring
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (ha' i) (hb' j)) (h (i, j, k))

end GlobalTheory.CoordDenom
end

