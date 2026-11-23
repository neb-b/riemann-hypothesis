module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0211

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCommuteShiftedEmbedding
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.DConj

open GlobalTheory.CompanionTheory.BZPhiPG.Cells GlobalTheory.CompanionTheory.LeibPhi GlobalTheory.CompanionTheory.BZPhiPhi
open GlobalTheory.CompanionTheory.BZMir.GpExists (unip_apply_of_ne_last unip_apply_last_last)

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blockIndex_false_eq_castAdd₂ (i t : ℕ) (a : Fin (i + 1)) :
    eGP (i + 1) t ⟨false, a⟩ = (Fin.castAdd (t + 1) a : Fin ((i + 1) + (t + 1))) :=
  Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_false_val]; simp)

theorem blockIndex_true_eq_natAdd₂ (i t : ℕ) (b : Fin (t + 1)) :
    eGP (i + 1) t ⟨true, b⟩ = (Fin.natAdd (i + 1) b : Fin ((i + 1) + (t + 1))) :=
  Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val]; simp)

theorem gpProj_snd_apply (m j : ℕ) (g : MirabolicParabolic k m j) (a b : Fin (j + 1)) :
    (((gpProj k m j g).2 : Mir k j) : GL (Fin (j + 1)) k).val a b =
      ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k).val (eGP m j ⟨true, a⟩) (eGP m j ⟨true, b⟩) := by
  show (leviProj k (eGP m j) (hgpIncl k m j g) true).val a b = _
  rw [leviProj_apply]
  rfl

theorem inv_mulVec_natAdd (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k) (x : Fin (t + 1)) :
    ((((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ
        (Fin.append (0 : Fin (i + 1) → k) d : Fin ((i + 1) + (t + 1)) → k)) (Fin.natAdd (i + 1) x) =
      (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) x := by
  have hinv : ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k) =
      (((gpProj k (i + 1) t h⁻¹).2 : Mir k t) : GL (Fin (t + 1)) k) := by
    rw [map_inv]
    rfl
  have hcoe : (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) =
      (((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) := rfl
  rw [hinv, hcoe]
  have hz : ∀ a : Fin (i + 1), ((((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) :
      GL (Fin ((i + 1) + t + 1)) k)).val (Fin.natAdd (i + 1) x) (Fin.castAdd (t + 1) a) = 0 := by
    intro a
    have := (mem_mirabolicParabolic_iff k _ _ _).1 (h⁻¹ : MirabolicParabolic k (i + 1) t).2 x a
    rwa [blockIndex_true_eq_natAdd₂, blockIndex_false_eq_castAdd₂] at this
  show ∑ y : Fin ((i + 1) + (t + 1)), _ = ∑ y : Fin (t + 1), _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [gpProj_snd_apply, blockIndex_true_eq_natAdd₂, blockIndex_true_eq_natAdd₂]

theorem pgProj_fst_apply (I T : ℕ) (g : HPG k I T) (a b : Fin (I + 1)) :
    (((pgProj k I T g).1 : Mir k I) : GL (Fin (I + 1)) k).val a b =
      ((g : Mir k (I + T)) : GL (Fin (I + T + 1)) k).val (ePG I T ⟨false, a⟩) (ePG I T ⟨false, b⟩) := by
  show (leviProj k (ePG I T) (hpgIncl k I T g) false).val a b = _
  rw [leviProj_apply]
  rfl

theorem pgProj_snd_apply (I T : ℕ) (g : HPG k I T) (a b : Fin T) :
    ((pgProj k I T g).2 : GL (Fin T) k).val a b =
      ((g : Mir k (I + T)) : GL (Fin (I + T + 1)) k).val (ePG I T ⟨true, a⟩) (ePG I T ⟨true, b⟩) := by
  show (leviProj k (ePG I T) (hpgIncl k I T g) true).val a b = _
  rw [leviProj_apply]
  rfl

theorem one_ePG (I T : ℕ) (x : Bool) (a b : Two (Fin (I + 1)) (Fin T) x) :
    (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨x, a⟩) (ePG I T ⟨x, b⟩) =
      (1 : Matrix (Two (Fin (I + 1)) (Fin T) x) (Two (Fin (I + 1)) (Fin T) x) k) a b := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
    intro e
    exact hab (by simpa using (ePG I T).injective e)


variable (k) in
def uEl (i t : ℕ) (c : Fin (i + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k))), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem uEl_mem (i t : ℕ) (c : Fin (i + 1) → k) : uEl k i t c ∈ HPG k (i + 1) (t + 1) := by
  refine mem_HPG_of (I := i + 1) (T := t + 1) (uEl k i t c) ?_ ?_
  · intro x y
    refine unip_castSucc_castSucc _ _ _ _ ?_
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega
  · intro x
    refine (unip_apply_castSucc_last k _ _ _).trans ?_
    show (Fin.append c (0 : Fin (t + 1) → k)) (Fin.natAdd (i + 1) x) = 0
    simp

theorem uEl_fst (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 ∈ MirUin k (i + 1) := by
  refine ⟨Multiplicative.ofAdd c, ?_⟩
  apply Units.ext
  ext a b
  show (unip k (i + 1) (Multiplicative.ofAdd c)).val a b =
    (((pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k).val a b
  rw [pgProj_fst_apply]
  show _ = (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _
  induction b using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    induction a using Fin.lastCases with
    | last => rw [ePG_false_last, unip_apply_last_last, unip_apply_last_last]
    | cast a =>
      have e : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) :=
        Fin.ext (by rw [ePG_false_val]; simp)
      rw [e, unip_apply_castSucc_last, unip_apply_castSucc_last]
      simp
  | cast b =>
    have hq : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc b⟩ ≠ Fin.last ((i + 1) + (t + 1)) := fun h =>
      Fin.castSucc_ne_last b ((ePG_false_eq_last_iff _ _ _).1 h)
    rw [unip_apply_of_ne_last _ _ _ _ hq, unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last b), one_ePG]

theorem uEl_snd (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).2 = 1 := by
  apply Units.ext
  ext a b
  rw [pgProj_snd_apply]
  show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _ = _
  have hq : ePG (i + 1) (t + 1) ⟨true, b⟩ ≠ Fin.last ((i + 1) + (t + 1)) := by
    intro h
    have := congrArg Fin.val h
    rw [ePG_true_val] at this
    have hb := b.2
    simp at this
    omega
  rw [unip_apply_of_ne_last _ _ _ _ hq, one_ePG]
  rfl

end

theorem dEmb_mul_sEmb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k), ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧ dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) * dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := by
  intro k _ _ _ _ i t h d
  let A : GL (Fin ((i + 1) + t + 1)) k := ((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
  let v : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  let w : Fin ((i + 1) + (t + 1)) → k := (A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v
  let c : Fin (i + 1) → k := fun x => w (Fin.castAdd (t + 1) x)
  let e : Fin (t + 1) → k :=
    ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append c (0 : Fin (t + 1) → k)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) e
  have hsum : a + b = w := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b, c]
    | right x =>
      simp only [a, b, Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add]
      exact (inv_mulVec_natAdd i t h d x).symm
  refine ⟨⟨uEl k i t c, uEl_mem i t c⟩, uEl_fst i t c, uEl_snd i t c, ?_⟩
  apply Subtype.ext
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e3 : A.val *ᵥ w = v := by
    show A.val *ᵥ ((A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  have e2 : glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A := by
    have := glEmb_mul_unip' k _ A (Multiplicative.ofAdd w)
    rw [toAdd_ofAdd, e3] at this
    exact this
  show unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A =
    glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b)
  rw [mul_assoc, e1, e2]

end GlobalTheory.CompanionTheory.BZPhiPG.DConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFrameLevelTriangular
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

section Frame

variable {E : Type} [Field E] {n r : ℕ} {S : E →+* E} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem cT_pre_mul (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (s : Fin r) :
    cT S (pre X s) * J = (cT S X * J).submatrix (Fin.castLE s.2) id := by
  ext i l
  simp [Matrix.mul_apply, cT, pre]

theorem mul_pre (A : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (s : Fin r) :
    A * pre X s = (A * X).submatrix id (Fin.castLE s.2) := by
  ext i l
  simp [Matrix.mul_apply, pre]

theorem castLE_ne {s i : Fin r} (hi : ¬ i ≤ s) (j : Fin (s.val + 1)) : Fin.castLE s.2 j ≠ i := by
  intro e
  apply hi
  have : (j : ℕ) = i := congrArg Fin.val e
  have hj := j.2
  exact Fin.le_def.2 (by omega)

theorem exists_frameIdem_eq_pre_mul (s : Fin r) {β : FrameIx r} (h : frameLev s β = 2) :
    ∃ Q : Matrix (Fin (s.val + 1)) (Fin n) E, frameIdem S J X Y β = pre X s * Q := by
  rcases β with _ | b | b
  · simp [frameLev] at h
  · have hb : b ≤ s := by
      by_contra hb
      simp [frameLev, hb] at h
    have hlt : b.val < s.val + 1 := Nat.lt_succ_of_le (Fin.le_def.1 hb)
    let P : Matrix (Fin (s.val + 1)) (Fin r) E := single ⟨b.val, hlt⟩ b (1 : E)
    refine ⟨P * (cT S Y * J), ?_⟩
    have e : X * (single b b (1 : E) : Matrix (Fin r) (Fin r) E) = pre X s * P := by
      ext k j
      by_cases hj : j = b
      · subst hj
        simp [P, pre, Matrix.mul_apply, Matrix.single_apply]
      · simp [P, Matrix.mul_apply, Matrix.single_apply, Ne.symm hj]
    simp only [frameIdem]
    rw [e, Matrix.mul_assoc]
  · by_cases hb : b ≤ s <;> simp [frameLev, hb] at h

theorem exists_frameIdem_eq_mul_form (s : Fin r) {α : FrameIx r} (h : frameLev s α = 0) :
    ∃ Q : Matrix (Fin n) (Fin (s.val + 1)) E, frameIdem S J X Y α = Q * (cT S (pre X s) * J) := by
  rcases α with _ | a | a
  · simp [frameLev] at h
  · by_cases ha : a ≤ s <;> simp [frameLev, ha] at h
  · have ha : a ≤ s := by
      by_contra ha
      simp [frameLev, ha] at h
    have hlt : a.val < s.val + 1 := Nat.lt_succ_of_le (Fin.le_def.1 ha)
    let P : Matrix (Fin r) (Fin (s.val + 1)) E := single a ⟨a.val, hlt⟩ (1 : E)
    refine ⟨Y * P, ?_⟩
    have e : (single a a (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J) = P * (cT S (pre X s) * J) := by
      rw [cT_pre_mul]
      ext i l
      by_cases hi : i = a
      · subst hi
        simp [P, Matrix.mul_apply, Matrix.single_apply]
      · simp [P, Matrix.mul_apply, Matrix.single_apply, Ne.symm hi]
    simp only [frameIdem]
    rw [Matrix.mul_assoc, e, Matrix.mul_assoc]

variable (hxx : cT S X * J * X = 0) (hxy : cT S X * J * Y = 1) (hyx : cT S Y * J * X = 1)
include hxx hxy hyx

theorem frameIdem_mul_pre (s : Fin r) {α : FrameIx r} (h : frameLev s α = 1) : frameIdem S J X Y α * pre X s = 0 := by
  rw [mul_pre]
  rcases α with _ | i | i
  · have : (1 - X * (cT S Y * J) - Y * (cT S X * J)) * X = 0 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, Matrix.mul_one, Matrix.mul_assoc, hxx,
        Matrix.mul_zero, sub_self, sub_zero]
    simp only [frameIdem, this]
    rfl
  · have hi : ¬ i ≤ s := by
      intro hi
      simp [frameLev, hi] at h
    have : X * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S Y * J) * X =
        X * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) := by
      rw [Matrix.mul_assoc _ _ X, hyx, Matrix.mul_one]
    ext k j
    simp only [frameIdem, this, Matrix.submatrix_apply, id]
    simp [Matrix.mul_apply, Matrix.single_apply, (castLE_ne hi j).symm]
  · have : Y * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J) * X = 0 := by
      rw [Matrix.mul_assoc _ _ X, hxx, Matrix.mul_zero]
    simp only [frameIdem, this]
    rfl

theorem form_mul_frameIdem (s : Fin r) {β : FrameIx r} (h : frameLev s β = 1) :
    (cT S (pre X s) * J) * frameIdem S J X Y β = 0 := by
  have e : ∀ A : Matrix (Fin n) (Fin n) E, (cT S (pre X s) * J) * A = ((cT S X * J) * A).submatrix (Fin.castLE s.2) id := fun A => by
    rw [cT_pre_mul]
    ext i l
    simp [Matrix.mul_apply]
  rw [e]
  rcases β with _ | i | i
  · have : (cT S X * J) * (1 - X * (cT S Y * J) - Y * (cT S X * J)) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ X, hxx, Matrix.zero_mul,
        ← Matrix.mul_assoc _ Y, hxy, Matrix.one_mul, sub_zero, sub_self]
    simp only [frameIdem, this]
    rfl
  · have : (cT S X * J) * (X * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S Y * J)) = 0 := by
      rw [Matrix.mul_assoc X, ← Matrix.mul_assoc _ X, hxx, Matrix.zero_mul]
    simp only [frameIdem, this]
    rfl
  · have hi : ¬ i ≤ s := by
      intro hi
      simp [frameLev, hi] at h
    have : (cT S X * J) * (Y * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J)) =
        (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J) := by
      rw [Matrix.mul_assoc Y, ← Matrix.mul_assoc _ Y, hxy, Matrix.one_mul]
    ext j l
    simp only [frameIdem, this, Matrix.submatrix_apply, id]
    simp [Matrix.mul_apply, Matrix.single_apply, (castLE_ne hi j).symm]

end Frame

theorem map_mul_mul_map_eq_zero {E : Type} [Field E] {n k : ℕ} (t : E →+* ℂ) {C : Matrix (Fin n) (Fin k) E}
    {T : Matrix (Fin k) (Fin n) E} {M : Matrix (Fin n) (Fin n) ℂ}
    (h3 : ∀ x : Fin n → E, T *ᵥ x = 0 → ∃ b : Fin k → ℂ, M *ᵥ (fun i => t (x i)) = C.map t *ᵥ b)
    {P Q : Matrix (Fin n) (Fin n) E} (hP : P * C = 0) (hQ : T * Q = 0) : P.map t * M * Q.map t = 0 := by
  ext i j
  obtain ⟨b, hb⟩ := h3 (fun l => Q l j) (funext fun a => congrFun (congrFun hQ a) j)
  have e1 : P.map t * C.map t = 0 := by
    rw [← Matrix.map_mul, hP]
    exact Matrix.map_zero _ (map_zero _)
  have e2 : (P.map t * M * Q.map t) i j = (P.map t *ᵥ (M *ᵥ fun l => t (Q l j))) i := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [e2, hb, Matrix.mulVec_mulVec, e1, Matrix.zero_mulVec]
  rfl

section Unip

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem arch_of_mem_unipRad (h : IsCMExt F E σ) (hJ : IsHermND σ J) {C : Matrix (Fin n) (Fin r) E}
    (hC : GlobalTheory.UAut.IsIsoCols σ J C) {m : GAd σ J} (hm : m ∈ unipRad σ J C) (w : InfinitePlace F) (τ : EmbOver E w) :
    (archMat σ J τ (projArch σ J w m) - 1) * C.map τ.1 = 0 ∧
    (cT (σ : E →+* E) C * J).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) = 0 ∧
    ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 → ∃ b : Fin r → ℂ,
      (archMat σ J τ (projArch σ J w m) - 1) *ᵥ (fun i => τ.1 (x i)) = C.map τ.1 *ᵥ b := by
  have hg : m ∈ GlobalTheory.UAut.unipSet σ J C fun _ => 0 := by
    refine (GlobalTheory.UAut.mem_unipFlag hJ (GlobalTheory.SiegelSet.sigma_sigma h) hC _).1 ?_
    rw [GlobalTheory.UAut.unipFlag_const]
    exact hm
  obtain ⟨A, hA, e1⟩ := GlobalTheory.UAut.lower_iff.1 hg.1
  have h1 : ((matHom _ σ J m).1 - 1) * adMat F C = 0 := by
    rw [e1, show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero]
  have h2 : adMat F (cT (σ : E →+* E) C * J) * ((matHom _ σ J m).1 - 1) = 0 := by
    have e : (matHom _ σ J m).1 * adMat F C = adMat F C * (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [h1, Matrix.mul_one]
    have e2 := GlobalTheory.UAut.form_mul_of_mul_cols e
    have hi : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := Units.inv_mul m.1
    rw [Formalism.UG.cT_one, Matrix.one_mul] at e2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
    conv_lhs => rw [← e2, Matrix.mul_assoc, hi, Matrix.mul_one]
  let φ := (infEmb τ).comp (compInf F E w)
  have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
    change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
    simp
  have hM : archMat σ J τ (projArch σ J w m) - 1 = ((matHom _ σ J m).1 - 1).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (adMat F Z).map φ = Z.map τ.1 := fun Z =>
    Matrix.ext fun i j => h0 _
  rw [hM]
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← hZ, ← Matrix.map_mul, h1]
    exact Matrix.map_zero _ (map_zero _)
  · rw [← hZ, ← Matrix.map_mul, h2]
    exact Matrix.map_zero _ (map_zero _)
  · obtain ⟨a, ha⟩ := hg.2 x hx
    refine ⟨fun i => φ (a i), ?_⟩
    have e3 := congrArg (fun v : Fin n → AF F ⊗[F] E => fun i => φ (v i)) ha
    rw [show (fun i => τ.1 (x i)) = fun i => φ (inclR (F := F) (AF F) (x i)) from funext fun i => (h0 _).symm, ← hZ]
    funext i
    have l1 := RingHom.map_mulVec φ ((matHom _ σ J m).1 - 1) (fun i => inclR (F := F) (AF F) (x i)) i
    have l2 := RingHom.map_mulVec φ (adMat F C) a i
    exact l1.symm.trans ((congrFun e3 i).trans l2)

end Unip

theorem frameIdem_mul_unipRad_mul_frameIdem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (s : Fin r) (m : GAd σ J)
    (hm : m ∈ unipRad σ J (pre X s)) (w : InfinitePlace F) (τ : EmbOver E w) (α β : FrameIx r)
    (hαβ : frameLev s α ≤ frameLev s β) :
    (frameIdem (σ : E →+* E) J X Y α).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) *
      (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => hσ _, GlobalTheory.UAut.cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) :=
    GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2
  obtain ⟨h1, h2, h3⟩ := arch_of_mem_unipRad h hJ hC hm w τ
  have hβ : frameLev s β ≤ 2 := by
    rcases β with _ | b | b <;> simp only [frameLev] <;> try split_ifs
    all_goals omega
  by_cases e2 : frameLev s β = 2
  · obtain ⟨Q, hQ⟩ := exists_frameIdem_eq_pre_mul (S := (σ : E →+* E)) (J := J) (Y := Y) s e2
    rw [hQ, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ ((pre X s).map τ.1), h1, Matrix.zero_mul,
      Matrix.mul_zero]
  by_cases e0 : frameLev s α = 0
  · obtain ⟨Q, hQ⟩ := exists_frameIdem_eq_mul_form (S := (σ : E →+* E)) (J := J) (X := X) (Y := Y) s e0
    rw [hQ, Matrix.map_mul, Matrix.mul_assoc (Q.map τ.1), h2, Matrix.mul_zero, Matrix.zero_mul]
  have hα : frameLev s α = 1 := by omega
  have hβ' : frameLev s β = 1 := by
    have : frameLev s β ≠ 0 := by omega
    omega
  exact map_mul_mul_map_eq_zero τ.1 h3 (frameIdem_mul_pre hW.xx hW.xy yx s hα) (form_mul_frameIdem hW.xx hW.xy yx s hβ')

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.JacSph

theorem hecke_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : CassData G) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π) (t : D.T) (ht : D.IsDom t)
    (U : Module.End ℂ (fixed π D.J)) (hU : PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U) (r : ℕ) :
    D.IsDom (t ^ r) ∧ PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
  induction r with
  | zero =>
    refine ⟨by simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1, ?_⟩
    intro w l _
    simp
  | succ r ih =>
    rw [pow_succ, pow_succ U]
    exact ⟨(GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih.1 ht,
      _root_.GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract G D V π hπ (t ^ r) t ih.1 ht _ _ ih.2 hU⟩

theorem jacNeU : JacNeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hu hadm _ hsat
  obtain ⟨v₀, hv₀⟩ := hsat.exists_vec
  have hfixK : v₀ ∈ fixed ρ (KU σ n) := hv₀.2.1
  refine ⟨v₀, fun hjac => ?_, fun k hk _ => ?_⟩
  · obtain ⟨D, hJ, hN, hNm, hT⟩ := _root_.GlobalTheory.CompanionTheory.IwUnit.iwahoriU L ϖ σ q hu n
    obtain ⟨hKo, hKc, hIK, t₀, ht₀d, ht₀s⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n hu
    have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
      (_root_.GlobalTheory.CompanionTheory.DomUnitary.domU L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
    have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
    have hproj0 : D.proj ρ v₀ = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hker]
      exact hjac
    have hJK : ∀ x ∈ D.J, x ∈ KU σ n := fun x hx => hIK (hJ ▸ hx)
    have hfixJ : v₀ ∈ fixed ρ D.J :=
      GlobalTheory.LGrp.mem_fixed.2 fun x hx => GlobalTheory.LGrp.mem_fixed.1 hfixK x (hJK x hx)
    obtain ⟨U, hU, -⟩ := _root_.GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique (GU σ n) D.J D.isOpen_J D.isCompact_J V ρ hadm.1 t₀
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Cass.hecke_pow_kills_of_proj_eq_zero (GU σ n) D V ρ hadm.1 _ hstr U hU
      ⟨v₀, hfixJ⟩ hproj0
    obtain ⟨l, hlK, hl1⟩ := GlobalTheory.CompanionTheory.KAvg.kInvForm (GU σ n) (KU σ n) hKo hKc V ρ hadm.1 v₀ hfixK hv₀.1
    obtain ⟨j, hj, hS⟩ := _root_.GlobalTheory.CompanionTheory.SatPow.satPowNonvan L ϖ σ q n hu α t₀ ht₀d ht₀s j₀
    have hUj : (U ^ j) ⟨v₀, hfixJ⟩ = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, pow_add, Module.End.mul_apply, hj₀, map_zero]
    have hl0 : l (ρ (t₀ ^ j) v₀) = 0 := by
      have h := (hecke_pow D ρ hadm.1 _ hstr.1 U hU j).2 ⟨v₀, hfixJ⟩ l fun x hx => hlK x (hJK x hx)
      rw [hUj] at h
      simpa using h
    have hc := GlobalTheory.CompanionTheory.SphComp.sphCompare L ϖ σ q n hu V ρ α v₀ hv₀ l hlK (t₀ ^ j)
    rw [hl0, mul_zero, hl1, mul_one] at hc
    exact hS hc.symm
  · rw [GlobalTheory.LGrp.mem_fixed.1 hfixK k hk, sub_self]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.JacSph
end

