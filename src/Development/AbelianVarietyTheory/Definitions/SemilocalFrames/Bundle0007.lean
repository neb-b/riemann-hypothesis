module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem isUnit_det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem isUnit_det_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ isUnit_det_Hpk).2.2 g hg).1

theorem norm_det_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : ‖g.det‖ = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h3 : star g.det * g.det = 1 := by
    have h4 : (star g.det * g.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
      rw [one_mul]; linear_combination h2
    exact (isUnit_det_Hpk (k := k) (r := r)).mul_right_cancel h4
  have h5 : Complex.normSq g.det = 1 := by
    have h6 := Complex.normSq_eq_conj_mul_self (z := g.det)
    rw [starRingEnd_apply, h3] at h6
    exact_mod_cast h6
  have h7 : ‖g.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h5]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h7

theorem IsClosedSub.isClosedSubgroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) :
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup S := by
  obtain ⟨hG, hc, h1, hm, hi⟩ := hS
  exact ⟨h1, hm, hi, fun a ha => isUnit_det_of_mem_GG (hG ha), hc⟩

theorem isClosedSub_of {S : Set (Mat k r)} (hS : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) (h : S ⊆ GG k r) :
    IsClosedSub k r S := by
  unfold IsClosedSub
  exact ⟨h, hS.closed, hS.one_mem, hS.mul_mem, hS.inv_mem⟩

theorem isClosedSub_GG : IsClosedSub k r (GG k r) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.unitary_group_closed k r) subset_rfl

theorem isClosedSub_Nset : IsClosedSub k r (Nset k r) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) fun _ hg => hg.1

theorem isClosedSub_UWset (z : Fin (2 * r + k + 1) → ℂ) : IsClosedSub k r (UWset k r z) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) fun _ hg => hg.1

private theorem inv_eq_Hpk_conjTranspose_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', (hpkFacts k r).2.1]

theorem isClosedSub_Sset {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsClosedSub k r (Sset k r z) := by
  obtain ⟨h1, hmul, hinv⟩ := sGroup k r z hz
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hK : IsCompact (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.compactW k r z hz hT
  have hsub : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, m, hm, rfl⟩
    exact (uHGroup _ _ isUnit_det_Hpk).2.1 h hh.1 m hm.1
  have hclosed : IsClosed (Sset k r z) := by
    have : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
    have hC : IsClosed {p : UWset k r z × Mat k r | Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2 ∈ Nset k r} :=
      IsClosed.preimage (f := fun p : UWset k r z × Mat k r => Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2)
        (((continuous_const.mul (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose).mul
          continuous_const).mul continuous_snd) hN.closed
    have himg : Sset k r z =
        Prod.snd '' {p : UWset k r z × Mat k r | Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
      ext s
      constructor
      · rintro ⟨h, hh, m, hm, rfl⟩
        refine ⟨(⟨h, hh⟩, h * m), ?_, rfl⟩
        show Hpk k r * hᴴ * Hpk k r * (h * m) ∈ Nset k r
        rw [← inv_eq_Hpk_conjTranspose_of_mem_GG hh.1, ← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hh.1), Matrix.one_mul]
        exact hm
      · rintro ⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩
        refine ⟨h, hh, Hpk k r * hᴴ * Hpk k r * s', hp, ?_⟩
        show s' = h * (Hpk k r * hᴴ * Hpk k r * s')
        rw [← inv_eq_Hpk_conjTranspose_of_mem_GG hh.1, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_GG hh.1), Matrix.one_mul]
    rw [himg]
    exact isClosedMap_snd_of_compactSpace _ hC
  unfold IsClosedSub
  exact ⟨hsub, hclosed, h1, hmul, hinv⟩

theorem haar_unimod_of_biinv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn S μ) : IsHaarOn S μ ∧ IsUnimod S μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  have hsf : SigmaFinite μ := inferInstance
  constructor
  · unfold Formalism.MainNotions.S.IsHaarOn
    exact ⟨hsf, h.ne_zero, h.conc, h.left⟩
  · unfold IsUnimod
    exact ⟨h.right, Formalism.FourierDecayAlt.P.haar_measure_inversion k r S μ hS.isClosedSubgroup h⟩

theorem exists_unimod_GG : ∃ μ : Measure (Mt k r), IsHaarOn (GG k r) μ ∧ IsUnimod (GG k r) μ := by
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  exact ⟨μ, haar_unimod_of_biinv isClosedSub_GG hμ⟩

def zStd (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))

theorem Tz_zStd : Tz k r (zStd k r) = 1 := by
  have hH : herm (Hpk k r) (zStd k r) (zStd k r) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, zStd, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Tz, hH]
  simp [Hpk, wI]

def detRep (k r m : ℕ) (h : Mat k r) : ℂ →L[ℂ] ℂ := h.det ^ m • ContinuousLinearMap.id ℂ ℂ

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
section
noncomputable section

namespace GlobalTheory.GLm

open Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def InMir {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (i : ℕ) + 1 = n → M i j = (1 : Mt g n) i j

def IsMirClass {n : ℕ} (F : Gn g n → ℂ) : Prop :=
  ∀ p x : Gn g n, InMir (p : Mt g n) → InMir (x : Mt g n) → F (p * x * p⁻¹) = F x

def InR (i : ℕ) {n : ℕ} (M : Mt g n) : Prop := InPar i M ∧ IsUniUp (br i (n - i) M)

def supFrom (i : ℕ) {n : ℕ} (M : Mt g n) : ZMod g := ∑ j ∈ Finset.Ico i (n - 1), entN M j (j + 1)

def diag1 {k : ℕ} (h : Gn g k) (n : ℕ) : Gn g n :=
  toG fun i j : Fin n => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (h : Mt g k) i j else (1 : Mt g n) i j

def tail (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (F : Gn g n → ℂ) : Gn g m → ℂ := fun p =>
  ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹ * ∑ x : Gn g n,
    if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
      F x * (ψ₀ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0

def indR (ψ₀ : AddChar (ZMod g) ℂ) (i n : ℕ) (ρ : Gn g i → ℂ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InR i (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InMir (y : Mt g n) ∧ InR i ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ρ (toG (tl i ((y⁻¹ * x * y : Gn g n) : Mt g n))) * ψ₀ (supFrom i ((y⁻¹ * x * y : Gn g n) : Mt g n)) else 0

def indV (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) : Gn g (m + 1) → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1)))).card : ℂ)⁻¹ *
    ∑ y : Gn g (m + 1), if InMir (y : Mt g (m + 1)) ∧ InMir ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) ∧
        InMir (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1))) then
      f (toG (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)))) *
        ψ₀ (entN ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) (m - 1) m) else 0

def InPat {N : ℕ} (Φ : Fin N → Fin N → Prop) (M : Mt g N) : Prop := ∀ a b, ¬ Φ a b → M a b = (1 : Mt g N) a b

def sumAt {N : ℕ} (E : Fin N → Fin N → Prop) (M : Mt g N) : ZMod g := ∑ a, ∑ b, if E a b then M a b else 0

def ePat (g N : ℕ) [Fact g.Prime] (Φ E : Fin N → Fin N → Prop) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (Gn g N) :=
  eDat g N (InPat Φ) (sumAt E) ψ₀

def IsW (k s a : ℕ) : Prop := s ≤ a ∧ a < s + k

def phI (k s i : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  (IsW k s a ∧ IsW k s b ∧ a < b) ∨ (¬ IsW k s a ∧ ¬ IsW k s b ∧ a < b) ∨ ((a : ℕ) < i ∧ IsW k s b) ∨
    (IsW k s a ∧ ((i < (b : ℕ) ∧ (b : ℕ) < s) ∨ ((b : ℕ) = s + k ∧ i < s) ∨ s + k < (b : ℕ)))

def eeI (k s : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  ((b : ℕ) = a + 1 ∧ (b : ℕ) < s) ∨ ((a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) ∨ ((b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ)) ∨
    ((b : ℕ) = a + 1 ∧ IsW k s a ∧ IsW k s b)

def pm (g : ℕ) [Fact g.Prime] {n : ℕ} (σ : Equiv.Perm (Fin n)) : Gn g n :=
  toG fun r j : Fin n => if r = σ j then 1 else 0

def sigI (a c i j : ℕ) : ℕ := if j < i then j else if j < a then c + (j - i) else if j < a + (c - i) then i + (j - a) else j

def wI (g : ℕ) [Fact g.Prime] (a c i n : ℕ) : Gn g n :=
  toG fun r j : Fin n => if (r : ℕ) = sigI a c i j then 1 else 0

def mean {G : Type} [Fintype G] (f : G → ℂ) : ℂ := (Fintype.card G : ℂ)⁻¹ * ∑ x, f x

theorem inMir_one (n : ℕ) : InMir (1 : Mt g n) := fun _ _ _ => rfl

end GlobalTheory.GLm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
section
open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count.Test

open Formalism.MainNotions.S GlobalTheory.Count

variable (I : AutInst)

theorem mem_lamX (x : I.GA) (y : Fin I.n → I.E) : y ∈ lamX I x ↔
    I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
  constructor
  · intro hy
    unfold lamX at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      have e0 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
        ext i; simp
      rw [e0, Matrix.mulVec_zero]
      exact zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ =>
      have e2 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z₁ + z₂) i)) =
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₁ i)) +
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₂ i)) := by
        ext i; simp
      rw [e2, Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul a z _ hz =>
      have hc : Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) ∈ IntAf I.F I.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((a • z) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) •
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z i)) := by
        ext i; simp [Algebra.smul_def]
      rw [e1, Matrix.mulVec_smul]
      exact I.Lf.smul_mem ⟨_, hc⟩ hz
  · intro hy
    exact Submodule.subset_span hy

theorem le_lamX_one : I.L ≤ lamX I 1 := by
  intro y hy
  rw [mem_lamX]
  have h1 : I.fmat (1 : I.GA).2⁻¹ = 1 := by simp [AutInst.fmat]
  rw [h1, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem one_mem_GF : (1 : I.GA) ∈ I.GFset := by
  simp only [AutInst.GFset, Set.mem_ofPred_eq]
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hdet]
  · simp [AutInst.fmat]

theorem lamX_equivariant (g x : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (y : Fin I.n → I.E) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (g * x) ↔ y ∈ lamX I x := by
  have hm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by
    simp [AutInst.fmat]
  have h1 : I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hinc : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F)
      (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat g.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    ext i
    rw [h, RingHom.map_mulVec]
    rfl
  rw [mem_lamX, mem_lamX, hinc, Prod.snd_mul, _root_.mul_inv_rev, hm, Matrix.mulVec_mulVec, mul_assoc,
    ← hm g.2⁻¹ g.2, inv_mul_cancel, h1, mul_one]

theorem embedding_cases (w : InfinitePlace I.E) :
    w.embedding = I.φ (w.comap (algebraMap I.F I.E)) ∨
      w.embedding = ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E))) := by
  have hcm := I.cm.cmUnram.2.1
  have hF : ∀ a : I.F, w.embedding (algebraMap I.F I.E a) =
      I.φ (w.comap (algebraMap I.F I.E)) (algebraMap I.F I.E a) := by
    have := I.cm.totReal
    have hv : w.comap (algebraMap I.F I.E) =
        InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    have hψ : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := RingHom.ext (I.φ_over _)
    have hreal : ComplexEmbedding.conjugate (w.embedding.comp (algebraMap I.F I.E)) =
        w.embedding.comp (algebraMap I.F I.E) :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _))
    have hmk : InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) =
        InfinitePlace.mk ((I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E)) := by
      rw [hψ, InfinitePlace.mk_embedding, hv]
    have key : w.embedding.comp (algebraMap I.F I.E) =
        (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) := by
      rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
      · exact h
      · rwa [hreal] at h
    intro a
    exact RingHom.congr_fun key a
  set ψ := I.φ (w.comap (algebraMap I.F I.E)) with hψdef
  have hpt : ∀ e : I.E, w.embedding e = ψ e ∨ w.embedding e = starRingEnd ℂ (ψ e) := by
    intro e
    obtain ⟨s, hs⟩ := (I.cm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    obtain ⟨t, ht⟩ := (I.cm.fixed (e * star e)).1 (by rw [star_mul, star_star])
    have h1 : w.embedding e + starRingEnd ℂ (w.embedding e) = ψ e + starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_add (f := _), ← map_add (f := _), ← hs, hF]
    have h2 : w.embedding e * starRingEnd ℂ (w.embedding e) = ψ e * starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_mul, ← map_mul, ← ht, hF]
    have h3 : (w.embedding e - ψ e) * (w.embedding e - starRingEnd ℂ (ψ e)) = 0 := by
      linear_combination (w.embedding e) * h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨a, ha⟩ : ∃ a, w.embedding a ≠ ψ a := by
    by_contra hc
    push Not at hc
    exact hne1 (RingHom.ext hc)
  obtain ⟨b, hb⟩ : ∃ b, w.embedding b ≠ starRingEnd ℂ (ψ b) := by
    by_contra hc
    push Not at hc
    exact hne2 (RingHom.ext fun x => (hc x).trans (ComplexEmbedding.conjugate_coe_eq ψ x).symm)
  have ha' := (hpt a).resolve_left ha
  have hb' := (hpt b).resolve_right hb
  rcases hpt (a + b) with h | h
  · apply ha
    rw [map_add (f := _), map_add (f := _)] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add (f := _), map_add (f := _), map_add (f := _)] at h
    linear_combination h - ha'

theorem frm_frame (x : I.GA) (w : InfinitePlace I.E) :
    (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
  have hU : (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ * Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) *
      uMat (x.1 (w.comap (algebraMap I.F I.E))) = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) :=
    (x.1 (w.comap (algebraMap I.F I.E))).2
  have key : (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
      I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))) =
      Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
          ((I.P (w.comap (algebraMap I.F I.E)))ᴴ * I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
            I.P (w.comap (algebraMap I.F I.E))) * uMat (x.1 (w.comap (algebraMap I.F I.E))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [I.P_spec]; exact hU
  have hc : ∀ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) := by
    intro A; ext i j; simp [Matrix.conjTranspose_apply]
  simp only [frm]
  split_ifs with h
  · rw [h]; exact key
  · rw [(embedding_cases I w).resolve_left h]
    have hJ : I.J.map (ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E)))) =
        (I.J.map (I.φ (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hJ, hc, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, apply_ite (starRingEnd ℂ)]

theorem one_mem_nearSet (x : I.GA) {δ : ℝ} (hδ : 0 ≤ δ) : (1 : I.GA) ∈ nearSet I x δ := by
  simp only [nearSet, Set.mem_ofPred_eq]
  refine ⟨one_mem_GF I, ?_, fun v => ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact one_mem (Formalism.UG.stabGL I.Lf)
  · simp [uMat, Formalism.REAL.hs, hδ]

end GlobalTheory.Count.Test
end
end

