module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0130
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpP
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsR (i : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r + i.val then j.val else j.val + 1, by have := j.isLt; have := i.isLt; split_ifs <;> omega⟩

def ginvH (g : Q.Mx k r) : Q.Mx k r := Hpk k r * gᴴ * Hpk k r

def colR (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : q.val < r then ginvH k r g *ᵥ bvec (eI k r ⟨r - 1 - q.val, by omega⟩)
  else if h2 : q.val = r then ginvH k r g *ᵥ z
  else bvec (J ⟨q.val - r - 1, by have := q.isLt; omega⟩)

def beJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => colR k r z g J q p).det


open Classical in
def jSetR : Finset (Fin (r + k) → Fin (2 * r + k + 1)) := Finset.univ.filter fun J => StrictMono J

def rhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ i : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J) •
      qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) f g

end defs

def JDRRadP : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rhatOp k r z z' Y J x) c g = rhGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvP : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

theorem jDRGrpP_of_parts (hR : JDRRadP) (hI : JDRRealInvP) : JDRGrpP := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

theorem embedding_map_embedded_group : MMapEmbG := by
  intro k p ρ Z γ y₁ y₂
  simp only [U.mMap, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem embedded_group_measure_preserving : EmbGMuP := by
  intro k p ρ y q
  simp only [U.muP, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem wMat_mul_self_eq_one (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  split_ifs <;> simp_all

private theorem wMat_mul_wMat_mul' (d : ℕ) {m : Type*} (X : Matrix (Fin d) m ℂ) : G.wMat d * (G.wMat d * X) = X := by
  rw [← Matrix.mul_assoc, wMat_mul_self_eq_one, Matrix.one_mul]

theorem embedding_map_lower_unipotent : MMapLZU := by
  intro k p ρ l Z u γ hl
  simp only [U.mMap, U.muP, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_nonsing_inv l hl,
    Matrix.mul_assoc, wMat_mul_wMat_mul']

theorem embedded_group_right_action : EmbGRn := by
  intro k p ρ y x hy
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have h2 : (rcAct y x).2 = x.2 := rfl
  have h3 : yᴴ * (Hpk k ρ * y) = Hpk k ρ := by rw [← Matrix.mul_assoc, hy]
  have h4 : ∀ M : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ, yᴴ * (Hpk k ρ * (y * M)) = Hpk k ρ * M := by
    intro M
    rw [← Matrix.mul_assoc (Hpk k ρ), ← Matrix.mul_assoc, h3]
  simp only [U.Rn, U.embG, Ux5.block3_mul_blocks, h1, h2, Matrix.conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3, h4,
    neg_zero, smul_zero]

private theorem wP_inv_mul_wP_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ⁻¹ * U.wP σ = 1 := by
  ext a c
  have h : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
  simp only [U.wP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h]

private theorem isUnit_det_wP {p : ℕ} (σ : Equiv.Perm (Fin p)) : IsUnit (U.wP σ).det :=
  Matrix.isUnit_det_of_left_inverse (wP_inv_mul_wP_eq_one σ)

theorem lh_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : G.IsLowerUni (lhOf σ v) := by
  have hinv : (U.wP σ)⁻¹ = U.wP σ⁻¹ := Matrix.inv_eq_left_inv (wP_inv_mul_wP_eq_one σ)
  have hentry : ∀ a b, lhOf σ v a b = U.lowW σ v (σ a) (σ b) := by
    intro a b
    rw [lhOf, hinv]
    simp only [Matrix.mul_apply, U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.Perm.inv_eq_iff_eq, Finset.sum_ite_eq']
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Matrix.transpose_apply, hentry]
    simp [U.lowW]
  · simp only [Matrix.transpose_apply, hentry]
    have h1 : σ j ≠ σ i := fun h => (ne_of_lt hij) (σ.injective h)
    have h2 : ¬ (i < j) := not_lt.mpr hij.le
    simp [U.lowW, Matrix.one_apply, h1, h2]

theorem head_hermitian_eq : HeadHEq := by
  intro p σ d v u
  refine ⟨?_, lh_lower σ v⟩
  simp only [U.headH, lhOf, U.hMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), Matrix.nonsing_inv_mul _ (isUnit_det_wP σ), Matrix.one_mul]

private theorem blk2_fin_zero_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 0) ℂ)
    (C : Matrix (Fin 0) (Fin p) ℂ) (D : Matrix (Fin 0) (Fin 0) ℂ) : U.blk2 A B' C D = A := by
  ext i j
  have hi : finSumFinEquiv.symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  have hj : finSumFinEquiv.symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  simp [U.blk2, Matrix.reindex_apply, hi, hj]

theorem lower_corner_hermitian_zero : ZjHZero := by
  intro p σ d η Z
  simp only [U.ZjH, U.Zj, blk2_fin_zero_eq, Matrix.one_mul, Matrix.mul_one]

theorem lh_unit {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : IsUnit (lhOf σ v).det := by
  have hL : (U.lowW σ v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ?_]
    · simp [U.lowW]
    · intro i j hij
      have h1 : i < j := OrderDual.toDual_lt_toDual.mp hij
      have h2 : ¬ j < i := not_lt.mpr h1.le
      simp [U.lowW, Matrix.one_apply, ne_of_lt h1, h2]
  simp only [lhOf, Matrix.det_mul, hL, mul_one]
  exact (isUnit_det_wP σ).mul (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_wP σ))

theorem gamma_xi_split : GaXiSplit := by
  intro k p ρ σ d ξ Z h ν h' ν' g hh hν hh'
  have hZ : U.ZjH σ d ξ.2 Z = lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2 := by
    rw [lower_corner_hermitian_zero p σ d ξ.2 Z]
    exact (head_hermitian_eq p σ d ξ.2.2.1 ξ.2.2.2).1
  have hγ : h⁻¹ * ν⁻¹ * g * ν' * h' = (h⁻¹ * ν⁻¹) * g * (ν' * h') := by
    simp only [Matrix.mul_assoc]
  have hE : U.embG k p ρ (ν' * h') = U.embG k p ρ ν' * U.embG k p ρ h' := by
    simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  simp only [U.gaXi]
  rw [PBM.rn_inv, hZ]
  show U.Rn k p ρ (-ξ.1.1) * U.mMap k p ρ (lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2) (h⁻¹ * ν⁻¹ * g * ν' * h') *
      U.Rn k p ρ ξ.1.2 = _
  rw [embedding_map_lower_unipotent k p ρ _ _ _ _ (lh_unit σ ξ.2.2.1), hγ, embedding_map_embedded_group, hE]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.embG k p ρ h') (U.muP k p ρ (G.upper ξ.2.2.2)),
    embedded_group_measure_preserving k p ρ h' (G.upper ξ.2.2.2), Matrix.mul_assoc, embedded_group_right_action k p ρ h' ξ.1.2 hh']

theorem embG_nset {k p ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ QuantumDeterminants.Nset k ρ) : U.embG k p ρ y ∈ QuantumDeterminants.Nset k (p + ρ) := by
  rw [WeylGroupFacts.nset_iff] at hy ⊢
  refine ⟨?_, ?_⟩
  · show (U.embG k p ρ y)ᴴ * Hpk k (p + ρ) * U.embG k p ρ y = Hpk k (p + ρ)
    have hy1 : yᴴ * Hpk k ρ * y = Hpk k ρ := hy.1
    rw [Formalism.FourierDecayAlt.P.hermitian_group_blocks k p ρ, U.embG, Ux3.block3_conjTranspose, Ux3.block3_mul, Ux3.block3_mul]
    congr 1 <;> simp [hy1]
  · intro i c hc hi
    obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
    obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective c
    rw [U.embG, Ux3.block3_apply]
    simp only [(U.eB k p ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases w with ((w | w) | w) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc hi <;>
      first
      | (simp [Matrix.one_apply]; done)
      | (exfalso; have := x.isLt; have := w.isLt; omega)
      | skip
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]
    exact hy.2 x w (by omega) (by omega)

theorem left_factor_mem : LeftMem := by
  intro k p ρ z x l h ν hz hl hh hν
  have hH := Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ
  have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have hclN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)

  have hlH : G.IsUpperUni lᴴ := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_apply, show l i i = lᵀ i i from rfl, hl.1 i, star_one]
    · rw [Matrix.conjTranspose_apply, show l j i = lᵀ i j from rfl, hl.2 i j hij, star_zero]
  have hlu : IsUnit (lᴴ).det := by rw [Formalism.FourierDecayAlt.P.G4.upperUni_det hlH]; exact isUnit_one
  have hmu : U.muP k p ρ (lᴴ)⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) := by
    rw [← Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hlu]
    refine hclN.inv_mem _ (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ ⟨fun i j hij => hlH.2 i j hij, hlH.1⟩)
  have hRn : U.Rn k p ρ (rcAct h x) ∈ QuantumDeterminants.Nset k (p + ρ) :=
    (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨rcAct h x, rfl⟩)
  have hνN : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) :=
    embG_nset ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).inv_mem ν hν)
  have hW : U.embG k p ρ h⁻¹ ∈ UWset k (p + ρ) (liftVec k p ρ z) := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]; exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW p ρ z _ (WeylGroupFacts.uw_inv hh)
  refine ⟨U.embG k p ρ h⁻¹, hW, U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ ν⁻¹,
    hclN.mul_mem _ (hclN.mul_mem _ hRn _ hmu) _ hνN, ?_⟩
  have e1 : U.embG k p ρ h * U.Rn k p ρ x = U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := embedded_group_right_action k p ρ h x hh.1
  have e2 : U.embG k p ρ h⁻¹ * U.embG k p ρ h = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, Matrix.nonsing_inv_mul _ hhu, Formalism.FourierDecayAlt.P.PBM.embG_one]
  have e3 : U.Rn k p ρ x = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  have e4 : U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹) = U.embG k p ρ ν⁻¹ := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  have e5 : U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹ = U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ h := embedded_group_measure_preserving k p ρ h _
  calc U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)
      = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * (U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹) *
          U.embG k p ρ (h⁻¹ * ν⁻¹) := by rw [e3]; simp only [Matrix.mul_assoc]
    _ = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ *
          (U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹)) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e4]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

theorem lift_lift_V (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r)
    (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (liftVec k j n (D.castV hn (liftVec k 1 ρ v))) = D.castV h2 (liftVec k (j + 1) ρ v) := by
  funext i
  simp only [D.castV, liftVec, Fin.coe_cast]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem lift_lift_M (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r) (y : B.Mat k ρ) :
    D.castM h1 (ιLev k j n (D.castM hn (ιLev k 1 ρ y))) = D.castM h2 (ιLev k (j + 1) ρ y) := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.coe_cast, ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem castV_inj {a b : ℕ} (h : a = b) {v w : Fin (2 * a + k + 1) → ℂ} (e : D.castV h v = D.castV h w) : v = w := by
  subst h
  funext i
  simpa [D.castV] using congrFun e i

section tower

variable {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem levTower_bs_z_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z) := by
  have e1 := T.z_lev j (by omega)
  have e2 := T.z_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem levTower_bs_z'_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z' = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z') := by
  have e1 := T.z'_lev j (by omega)
  have e2 := T.z'_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem tower_π (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π y = (T.bs j).π (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π_lev (j + 1) hj y, T.π_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

theorem tower_π' (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π' y = (T.bs j).π' (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π'_lev (j + 1) hj y, T.π'_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

end tower

end Formalism.FourierDecayAlt.P.PBH
end
end

