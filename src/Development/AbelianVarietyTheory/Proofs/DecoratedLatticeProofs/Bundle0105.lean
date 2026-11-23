module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TransvLast

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N * (gA S * M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = N.map (cA D) *ᵥ (fun i => cA D (y i)) :=
    funext fun i => RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.vecMul_transpose (N.map (cA D)), ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

theorem conj_smul {n : ℕ} (c : AE D) (y : Fin n → AE D) :
    (fun i => cA D ((c • y) i)) = cA D c • fun i => cA D (y i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem conj_ratV {n : ℕ} (z : Fin n → D.host.E) : (fun i => cA D (ratV z i)) = ratV (star z) :=
  funext fun i => GlobalTheory.DualPairCheck.cA_incA (z i)

theorem ratV_dotProduct {n : ℕ} (x y : Fin n → D.host.E) : ratV x ⬝ᵥ ratV y = incA D (x ⬝ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul]
  rfl

theorem incA_inv_mul {x : D.host.E} (hx : x ≠ 0) : incA D x⁻¹ * incA D x = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]

section Lemmas

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hermSpaceAdelicForm_isotropic_anisotropic_zero (b : Fin ρ → AE D) (y : Fin V₀.rank → AE D) : form V (vecX d b) (d.j0 *ᵥ y) = 0 := by
  rw [vecX, form_mulVec, d.gram_0X, Matrix.zero_mulVec, dotProduct_zero]

theorem form_vecX_vecX (b b' : Fin ρ → AE D) : form V (vecX d b) (vecX d b') = 0 := by
  rw [vecX, vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_isotropic_zero (y : Fin V₀.rank → AE D) (b : Fin ρ → AE D) : form V (d.j0 *ᵥ y) (vecX d b) = 0 := by
  rw [vecX, form_mulVec, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_rational_smul (z : Fin V₀.rank → D.host.E) (c : AE D) :
    form V (d.j0 *ᵥ ratV z) (d.j0 *ᵥ (c • ratV z)) = cA D c * incA D (star z ⬝ᵥ V₀.gram *ᵥ z) := by
  rw [form_mulVec, d.gram_00, conj_smul, smul_dotProduct, conj_ratV, gA, ← GlobalTheory.MixPer.ratV_mulVec, ratV_dotProduct,
    smul_eq_mul]

theorem mt_jX_of_isTransv {w v : VA V} {u : GA D V} (hu : IsTransv V w v u)
    (hw : ∀ b, form V (vecX d b) w = 0) (hv : ∀ b, form V (vecX d b) v = 0) : mt V u * d.jX = d.jX := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have h : act V u (vecX d (Pi.single i 1)) = transv V w v (vecX d (Pi.single i 1)) := hu _
  rw [transv, hv, hw, zero_smul, zero_smul, mul_zero, zero_smul, add_zero, sub_zero, sub_zero] at h
  rw [← Matrix.mulVec_mulVec]
  exact h

theorem mt_of_isTransv {S : HSp D} {w v y : VA S} {u : GA D S} (hu : IsTransv S w v u) (hy : form S y w = 0) :
    mt S u *ᵥ y = y + form S y v • w := by
  have h : act S u y = transv S w v y := hu _
  rw [transv, hy, zero_smul, mul_zero, zero_smul, sub_zero, sub_zero] at h
  exact h

theorem simpleSum_of {z : Fin V₀.rank → D.host.E} {u : GA D V} {c : Fin ρ → AE D} (s : AE D)
    (hX : mt V u * d.jX = d.jX) (hy : mt V u *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + s • (d.jX *ᵥ c)) :
    simpleSum d z u = s * (ell D ρ ⬝ᵥ c) := by
  rw [simpleSum, blockX, hX, d.pX_jX, upSum_one, zero_add, coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.pX_j0,
    d.pX_jX, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, dotProduct_smul, smul_eq_mul]

theorem mem_fixer_column {u : GA D V} (hX : mt V u * d.jX = d.jX) (i : Fin ρ) :
    u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [mem_fixer]
  ext k l
  have h := congrFun (congrFun hX k) i
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using h

theorem ell_dotProduct_last {j : Fin ρ} (hj : j.1 + 1 = ρ) {a : Fin ρ → D.host.E} (haj : a j = 1) :
    ell D ρ ⬝ᵥ ratVec a = 1 := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [ell, hj, ratVec, haj]
  · intro i _ hij
    have : ¬ (i.1 + 1 = ρ) := fun h => hij (Fin.ext (Nat.add_right_cancel (h.trans hj.symm)))
    simp [ell, this]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Lemmas

theorem exists_transv_simpleSum_last : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z hz j a haj _ hj s
  refine ⟨d.j0 *ᵥ (cA D (s * incA D (star z ⬝ᵥ V₀.gram *ᵥ z)⁻¹) • ratV z), hermSpaceAdelicForm_isotropic_anisotropic_zero d _ _,
    fun i k _ => by rw [hermSpaceAdelicForm_isotropic_anisotropic_zero, zero_mul], fun u hu => ?_⟩
  have hX := mt_jX_of_isTransv d hu (fun b => form_vecX_vecX d b _) (fun b => hermSpaceAdelicForm_isotropic_anisotropic_zero d b _)
  have hy := mt_of_isTransv hu (hermSpaceAdelicForm_anisotropic_isotropic_zero d (ratV z) (ratVec a))
  rw [hermSpaceAdelicForm_anisotropic_rational_smul, cA_cA, mul_assoc, incA_inv_mul hz, mul_one] at hy
  exact ⟨fun i => mem_fixer_column d hX i.1, (simpleSum_of d s hX hy).trans (by rw [ell_dotProduct_last hj haj, mul_one])⟩

end GlobalTheory.TransvLast

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryEmbeddingPreimageOfFixesAnisotropic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory

theorem mt_jB_eq_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    mt S k ⬝ o.jB = o.jB := by
  obtain ⟨hL, hq⟩ := hζ
  obtain ⟨j0, hall⟩ : ∃ j0 : Fin L.rank, ∀ j : Fin L.rank, j = j0 :=
    ⟨⟨0, by omega⟩, fun j => Fin.ext (by have := j.isLt; show j.val = 0; omega)⟩
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hq
    have : ζ = 0 := funext fun j => by rw [hall j, h0]; rfl
    simp [this]
  have hv : ratV (o.iB *ᵥ ζ) = o.jB *ᵥ ratV ζ := by
    funext i; exact RingHom.map_mulVec (incA D) o.iB ζ i
  rw [hv, Matrix.mulVec_mulVec] at hk
  have hM : (mt S k ⬝ o.jB - o.jB) *ᵥ ratV ζ = 0 := by rw [Matrix.sub_mulVec, hk, sub_self]
  rw [← sub_eq_zero]
  funext i j
  rw [hall j]
  have h1 := congrFun hM i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
  rw [Fintype.sum_eq_single j0 (fun j hj => absurd (hall j) hj)] at h1
  have hu : incA D (ζ j0) * incA D (ζ j0)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hζ0, map_one]
  have e : (mt S k ⬝ o.jB - o.jB) i j0 = (mt S k ⬝ o.jB - o.jB) i j0 * ratV ζ j0 * incA D (ζ j0)⁻¹ := by
    rw [mul_assoc]; show _ = _ * (incA D (ζ j0) * _); rw [hu, mul_one]
  rw [e, h1, zero_mul]; rfl

theorem mat_eq_of_splitting {R : Type} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (jA : Matrix (Fin n) (Fin a) R) (pA : Matrix (Fin a) (Fin n) R) (jB : Matrix (Fin n) (Fin b) R)
    (pB : Matrix (Fin b) (Fin n) R) (H : Matrix (Fin a) (Fin a) R) (hX : M * jA = jA * H) (hfix : M * jB = jB)
    (hsum : jA * pA + jB * pB = 1) : M = jA * H * pA + jB * pB := by
  calc M = M * (jA * pA + jB * pB) := by rw [hsum, Matrix.mul_one]
    _ = M * jA * pA + M * jB * pB := by rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = jA * H * pA + jB * pB := by rw [hX, hfix]

theorem exists_emb_of_mt_jB_eq (D : D7) (S A B : HSp D) (o : OrthDec S A B) (k : GA D S)
    (hfix : mt S k ⬝ o.jB = o.jB) : ∃ h : GA D A, k = o.emb (h, 1) := by
  have hu : adj (mt S k) ⬝ (gA S ⬝ mt S k) = gA S := GlobalTheory.MixModel.mt_unitary S k
  have hBA : adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = 0 := by
    calc adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = adj (mt S k ⬝ o.jB) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) := by rw [hfix]
      _ = adj o.jB ⬝ (gA S ⬝ o.jA) := by
        rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
      _ = 0 := o.gram_BA
  have hpB : o.pB ⬝ (mt S k ⬝ o.jA) = 0 := by
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hX : mt S k ⬝ o.jA = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) := by
    calc mt S k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) + o.jB ⬝ (o.pB ⬝ (mt S k ⬝ o.jA)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hpB, Matrix.mul_zero, add_zero]
  have e1 : adj (mt S k ⬝ o.jA) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = gA A := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
    exact o.gram_AA
  set H := o.pA ⬝ (mt S k ⬝ o.jA) with hHdef
  have e2 : adj (o.jA ⬝ H) ⬝ (gA S ⬝ (o.jA ⬝ H)) = adj H ⬝ (gA A ⬝ H) := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA H]
  rw [← hX] at e2
  have hH : adj H * (gA A * H) = gA A := e2.symm.trans e1
  refine ⟨GlobalTheory.MixModel.ofMat A H hH, GlobalTheory.MixModel.mt_injective S ?_⟩
  rw [o.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  exact mat_eq_of_splitting (mt S k) o.jA o.pA o.jB o.pB H hX hfix o.sum_eq_one

theorem exists_emb_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    ∃ h : GA D A, k = o.emb (h, 1) :=
  exists_emb_of_mt_jB_eq D S A L o k (mt_jB_eq_of_fixes_lineVec D S A L o ζ hζ k hk)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7}

theorem mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
    M *ᵥ colMul X i a = fun r => a * (M * X) r i := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adj_diagonal {n : ℕ} (f : Fin n → AE D) :
    adj (Matrix.diagonal f) = Matrix.diagonal (fun i => cA D (f i)) := by
  ext i j; simp [adj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
    (h : A * (B * B') = C) (X : Mx D p k) :
    A * (B * (B' * X)) = C * X := by
  rw [← h]; simp only [Matrix.mul_assoc]

theorem mul_tail₄ {a m n p q k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {B'' : Mx D p q} {C : Mx D a q}
    (h : A * (B * (B' * B'')) = C) (X : Mx D q k) :
    A * (B * (B' * (B'' * X))) = C * X := by
  rw [← h]; simp only [Matrix.mul_assoc]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem gXX {k : ℕ} (X : Mx D ρ k) : adj d.jX * (gA S * (d.jX * X)) = 0 := by
  rw [mul_tail₃ d.gram_XX, Matrix.zero_mul]
theorem gYX {k : ℕ} (X : Mx D ρ k) : adj d.jY * (gA S * (d.jX * X)) = X := by
  rw [mul_tail₃ d.gram_YX, Matrix.one_mul]
theorem g0X {k : ℕ} (X : Mx D ρ k) : adj d.j0 * (gA S * (d.jX * X)) = 0 := by
  rw [mul_tail₃ d.gram_0X, Matrix.zero_mul]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_eq_of_mem {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {x : Mx D m n} (hx : ∀ i j, x i j ∈ idAt D P) : ε • x = x := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul, (hε _).1 (hx i j)]

theorem one_sub_mul_self {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hεε, sub_self]

theorem one_sub_sq {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [mul_sub, mul_one, one_sub_mul_self hεε, sub_zero]

theorem kill_left {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    (1 - ε) • (x * X) = 0 := by
  rw [← Matrix.smul_mul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.zero_mul]

theorem diag_absorb {ε : AE D} {n : ℕ} {α : Fin n → AE D} (hαε : ∀ i, ε * α i = α i) :
    ε • Matrix.diagonal α = Matrix.diagonal α := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · exact hαε i
  · rw [mul_zero]

theorem diag_const {ε : AE D} {n : ℕ} {α β : Fin n → AE D} (hαβ : ∀ i, α i * β i = ε) :
    (Matrix.diagonal fun i => α i * β i) = ε • (1 : Mx D n n) := by
  have : (fun i => α i * β i) = fun _ => ε := funext hαβ
  rw [this]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

set_option maxHeartbeats 1000000 in
theorem imYX {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α β : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    (hαβ : ∀ i, α i * β i = ε) {b : Mx D ρ ρ} (hb : ε • b = b) {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ)) :
    adj (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) *
      (gA S * (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 1 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₄ H1, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, gYX d, d.gram_YX, kill_left hεε (diag_absorb hαε), kill_left hεε hb, add_zero, smul_smul]
  rw [zero_add, Matrix.diagonal_mul_diagonal, one_sub_sq hεε]
  rw [diag_const hαβ, smul_smul, hεε, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem kill_mid₂ {ε : AE D} (hεε : ε * ε = ε) {m n p q k : ℕ} {x : Mx D p q} (hx : ε • x = x)
    (A : Mx D m n) (B : Mx D n p) (X : Mx D q k) : (1 - ε) • (A * (B * (x * X))) = 0 := by
  rw [← Matrix.mul_smul, ← Matrix.mul_smul, kill_left hεε hx, Matrix.mul_zero, Matrix.mul_zero]

theorem absorb_mul {ε : AE D} {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    x * (ε • X) = x * X := by
  rw [Matrix.mul_smul, ← Matrix.smul_mul, hx]

theorem imXX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} :
    adj (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))) *
      (gA S * (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  rw [adj_mul, Matrix.mul_assoc, gXX, Matrix.mul_zero]

set_option maxHeartbeats 1000000 in
theorem imYY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c') (H2 : adj c' * (gA S * c') = 0) :
    adj (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) *
      (gA S * (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₃ H2, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, d.gram_YY, smul_zero,
    kill_mid₂ hεε hc, kill_left hεε (diag_absorb hαε), add_zero, Matrix.zero_mul]

set_option maxHeartbeats 1000000 in
theorem imOO {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0))) * (gA S * (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0)))) = gA S₀ := by
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, d.gram_00, d.wittDecomp_gram_X_anisotropic,
    gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0))) * (gA S * (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  simp only [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} {b : Mx D ρ ρ} (hb : ε • b = b)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ)) :
    adj (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0))) * (gA S * (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have adjH1 : adj b * (adj d.jX * (gA S * c')) = ε • (1 : Mx D ρ ρ) := by
    have := congrArg adj H1
    simpa only [adj_mul, adj_gA, adj_adj, adj_smul, adj_one, hεc, Matrix.mul_assoc] using this
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [mul_tail₄ adjH1, Matrix.smul_mul, Matrix.one_mul, absorb_mul hc, sub_self, zero_add]
  simp only [Matrix.mul_smul, d.gram_0Y, d.gram_XY, Matrix.mul_one, smul_zero, kill_mid₂ hεε hc, sub_zero]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)


set_option maxHeartbeats 1000000 in
theorem smul_sub_one {ε : AE D} (M : Mx D S.rank S.rank)
    (hX : ε • (M * d.jX - d.jX) = M * d.jX - d.jX) (h0 : ε • (M * d.j0 - d.j0) = M * d.j0 - d.j0)
    (hY : ε • (M * d.jY - d.jY) = M * d.jY - d.jY) : ε • (M - 1) = M - 1 := by
  have e : M - 1 = (M * d.jX - d.jX) * d.pX + (M * d.j0 - d.j0) * d.p0 + (M * d.jY - d.jY) * d.pY := by
    have e1 : M - 1 = (M - 1) * (d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY) := by
      rw [d.sum_eq_one, Matrix.mul_one]
    rw [e1]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  rw [e, smul_add, smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, hX, h0, hY]

theorem smul_shift {ε : AE D} (hεε : ε * ε = ε) {m n : ℕ} {x : Mx D m n} (hx : ε • x = x) (y : Mx D m n) :
    ε • (x + (1 - ε) • y - y) = x + (1 - ε) • y - y := by
  have e : x + (1 - ε) • y - y = x - ε • y := by
    rw [sub_smul, one_smul]; abel
  rw [e, smul_sub, hx, smul_smul, hεε]

theorem scalar_X {R : Type*} [CommRing R] {ε a b x y : R} (ha : ε * a = a) (hab : a * b = ε) (hx : ε * x = x) :
    a * (x * b + (1 - ε) * y) = x := by
  linear_combination x * hab + hx - y * ha

end GlobalTheory.IwaPlace.BuildQ


open GlobalTheory.IwaPlace.BuildQ in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → adj c' * (gA S * c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q * d.jX = d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX * b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  intro D S S₀ ρ d v ε hεε hεc _ hε α β b c' hα hβ hαβ hb hc' H1 H2
  have hb' : ε • b = b := smul_eq_of_mem hε hb
  have hc : ε • c' = c' := smul_eq_of_mem hε hc'
  have hαε : ∀ i, ε * α i = α i := fun i => (hε _).1 (hα i)
  have hβε : ∀ i, ε * β i = β i := fun i => (hε _).1 (hβ i)
  have h : HypDec.Images S S₀ (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))
      (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0)))
      (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) :=
    ⟨imXX d, imYY d hεε hεc hαε hc H2, imYX d hεε hεc hαε hαβ hb' hc H1, imOO d, imOX d, imOY d hεε hεc hb' hc H1⟩
  have hjb : ε • (d.jX * b) = d.jX * b := by rw [← Matrix.mul_smul, hb']
  have hE : d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))
      = (d.jX * b) * Matrix.diagonal β + (1 - ε) • d.jX := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨d.ofImages _ _ _ h, ?_, d.ofImages_jX h, fun i => ?_, fun i => ?_⟩
  · have key := smul_sub_one d (ε := ε) (Formalism.L2.Theta.mt S (d.ofImages _ _ _ h))
      (by rw [d.ofImages_jX h, hE]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hjb]) _)
      (by rw [d.wittDecomp_ofImages_inclAnisotropic h, sub_sub_cancel_left, smul_neg, ← Matrix.smul_mul, hjb])
      (by rw [d.ofImages_jY h]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hc]) _)
    refine (mem_congGrp_iff S _ _).2 fun i j => (hε _).2 ?_
    exact congrFun (congrFun key i) j
  · rw [mulVec_colMul, d.ofImages_jX h, hE]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    exact scalar_X (hαε i) (hαβ i) (congrFun (congrFun hjb k) i)
  · rw [mulVec_colMul, d.ofImages_jY h]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    refine scalar_X ?_ ?_ (congrFun (congrFun hc k) i)
    · rw [← hεc, ← map_mul, hβε]
    · rw [← map_mul, mul_comm, hαβ, hεc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FubiniCompactQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem fubini_compact_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H), Countable Γ → DiscreteTopology Γ → (∃ K : Set H, IsCompact K ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (f : H → X → ℂ), Measurable (Function.uncurry f) → (∀ γ ∈ Γ, ∀ h x, f (γ * h) x = f h x) → (∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ h ∈ K, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B) → Integrable (Function.uncurry f) ((μ.restrict 𝓕).prod m) := by
  intro H _ _ _ _ _ _ _ _ μ _ Γ hΓc hΓd hK 𝓕 h𝓕 X _ m _ f hf hinv hB
  obtain ⟨K, hKc, hKcov⟩ := hK
  obtain ⟨B, hB⟩ := hB K hKc
  haveI : Countable Γ := hΓc

  have hbd : ∀ h, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B := by
    intro h
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    have := hB _ hk
    simpa only [hinv γ hγ h] using this

  have hfin : μ 𝓕 < ⊤ := by
    have hcover : 𝓕 ⊆ ⋃ g : Γ, (g • K) := by
      intro h _
      obtain ⟨γ, hγ, hk⟩ := hKcov h
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
      refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
      simp [Subgroup.smul_def]
    have hle : μ 𝓕 ≤ μ K := by
      calc μ 𝓕 = μ ((⋃ g : Γ, (g • K)) ∩ 𝓕) := by
              rw [Set.inter_eq_right.2 hcover]
        _ = μ (⋃ g : Γ, (g • K ∩ 𝓕)) := by rw [Set.iUnion_inter]
        _ ≤ ∑' g : Γ, μ (g • K ∩ 𝓕) := measure_iUnion_le _
        _ = μ K := (h𝓕.measure_eq_tsum K).symm
    exact hle.trans_lt hKc.measure_lt_top
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hm : AEMeasurable (fun z : H × X => ‖Function.uncurry f z‖ₑ) ((μ.restrict 𝓕).prod m) :=
    hf.enorm.aemeasurable
  rw [HasFiniteIntegral, lintegral_prod _ hm]
  calc ∫⁻ h, ∫⁻ x, ‖Function.uncurry f (h, x)‖ₑ ∂m ∂(μ.restrict 𝓕)
      ≤ ∫⁻ _, (B : ENNReal) ∂(μ.restrict 𝓕) := lintegral_mono (fun h => hbd h)
    _ = B * μ 𝓕 := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end GlobalTheory
end

