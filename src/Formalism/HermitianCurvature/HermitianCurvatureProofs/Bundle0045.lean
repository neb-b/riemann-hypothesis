module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDecomposition
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDecomposition

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

def CellDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∀ g ∈ GV k r, (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ c : Fin r → ℂ, (∀ a, c a ≠ 0) ∧
      ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ g = n⁻¹ * bigCell k r c μ * n'

variable {k r : ℕ}

theorem bigCell_one_fixes_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) : bigCell k r c 1 *ᵥ z = z := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have key : ∀ j, bigCell k r c 1 i j * z j = if j = i then z i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hz _ hj).symm
      · rfl
    · have hj1 : ¬ j.val < r := by omega
      have hj2 : j.val ≤ r + k := by omega
      simp only [bigCell, dif_neg hj1, dif_pos hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [dif_pos hi, Matrix.one_apply]
        by_cases hij : j = i
        · subst hij
          simp
        · have hne : (⟨i.val - r, by omega⟩ : Fin (k + 1)) ≠ ⟨j.val - r, by omega⟩ := by
            intro h
            apply hij
            ext
            simp only [Fin.mk.injEq] at h
            omega
          simp [hne, hij]
      · simp only [dif_neg hi, zero_mul]
        rw [if_neg]
        rintro rfl
        omega
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp

theorem n_inv_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, (one_mul _).symm⟩

theorem n_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n, hn, (one_mul n).symm⟩

end Formalism.FourierDecayAlt.P.BigCellDecomposition

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

theorem jf_psiOnto_of_cellDecomp (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.PsiOnto := by
  intro k r Wp Wq _ _ _ _ D g hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, rfl⟩ := hCD k r D.z D.z' g hg.1 hg.2.1
  set ζ := herm (Hb k) (μ *ᵥ wbPart k r D.z') (wbPart k r D.z) with hζdef
  have hmin := bigCellMinors k r D.z D.z' c μ D.z_mem D.z'_mem

  have hG : 0 < Gf k r D.z D.z' (bigCell k r c μ) := by
    have := hg.2.2
    rwa [gInv k r D.z D.z' D.z_mem D.z'_mem _ (BigCellDecomposition.n_inv_S hn) _ (BigCellDecomposition.n_S hn')] at this
  have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq ζ := by
    have hz := hmin.2.2 hc
    rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r c μ) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1)) = ζ * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    unfold Gf at hG
    rw [hlast, ← hP, Complex.normSq_mul] at hG
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

  have hfac := bruhat_big_cell_factorization k r c μ
  have huw := unipotent_weyl_properties k r
  have hm : embWb k r μ ∈ UWb k r := TwoByOneBlock.emb_mem_UWb hμ
  have hmz : herm (Hpk k r) (embWb k r μ *ᵥ D.z') D.z = ζ := by
    have e1 : embWb k r μ *ᵥ D.z' = bigCell k r c μ *ᵥ D.z' := by
      rw [hfac.2, ← Matrix.mulVec_mulVec, BigCellDecomposition.bigCell_one_fixes_vector D.z'_mem]
    rw [e1, BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem]
  obtain ⟨h, hh, h', hh', hmeq⟩ := b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem D.z'_mem D.T_pos
    D.T'_pos D.sec (embWb k r μ) hm (by rw [hmz]; exact hζ)
  rw [hmz] at hmeq
  have hu1 := WeylGroupFacts.isUnit_of_uh hh.1
  have hu2 := WeylGroupFacts.isUnit_of_uh hh'.1
  have hun := WeylGroupFacts.isUnit_of_uh hn.1
  have hcomm : bigCell k r c 1 * h⁻¹ = h⁻¹ * bigCell k r c 1 :=
    (huw.2.2 c h⁻¹ (huw.2.1 D.z (BigCellInversePair.uw_inv hh))).symm

  refine ⟨((h, h * n * h⁻¹), (h', h' * n' * h'⁻¹)), ⟨hh,
      (uWNormal k r D.z D.z_mem h hh n hn).1, hh', (uWNormal k r D.z' D.z'_mem h' hh' n' hn').1⟩,
    (c, ζ), ⟨hc, hζ⟩, ?_⟩
  show n⁻¹ * bigCell k r c μ * n' = h⁻¹ * (h * n * h⁻¹)⁻¹ * bigCell k r c (D.μsec ζ) * (h' * n' * h'⁻¹) * h'
  rw [hfac.1, hmeq, (bruhat_big_cell_factorization k r c (D.μsec ζ)).1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu1]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one]
  rw [← Matrix.mul_assoc (bigCell k r c 1) h⁻¹, hcomm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu1]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Truncated
section
theorem Formalism.FourierDecayAlt.P.derivative_cost_bound : Formalism.FourierDecayAlt.U.DerivativeCost := by
  have hS : Formalism.FourierDecayAlt.U.SliceMem := Formalism.FourierDecayAlt.P.slice_membership
  have h21 : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
    Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses hS Formalism.FourierDecayAlt.P.block3_apply_embedding Formalism.FourierDecayAlt.P.aux_statement_17
      Formalism.FourierDecayAlt.P.hat_z_on_slice
  exact operator_word_cost hS Formalism.FourierDecayAlt.P.radical_parametrisation Formalism.FourierDecayAlt.P.slice_right_coordinates
    Formalism.FourierDecayAlt.P.slice_left_coordinates Formalism.FourierDecayAlt.P.slice_z_coordinates Formalism.FourierDecayAlt.P.directions_in_parabolic h21
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAdm
section
namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt

theorem admissible_in_truncation_holds : AdmInCut := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx
  obtain ⟨w, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := w.2.1.1 v j hj
  have hnode := (hG v).2.2.2.2.2
  have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    intro Y hY
    simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
    simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hY.1, hY.2]
  by_cases hp : ((w.1 v)[j]'hj).1
  · rw [if_pos hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact hcut _ (hnode _ hy).1
  · rw [if_neg hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := hcut _ (hnode _ hy).2.1
    simpa using this

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

noncomputable section

def foldCV (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (a : List C.Letter)
    (H : B.Mat k r → E) : B.Mat k r → E :=
  a.foldr (fun x J => s • Q.CV k r (x.2 : ℂ) J) H

def CVLocal : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (B.Mat k r)) (f₁ f₂ : B.Mat k r → E)
    (Y : ℂ), IsOpen U → B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₁ →
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₂ → (∀ g ∈ U ∩ B.GV k r, f₁ g = f₂ g) →
    ∀ g ∈ U ∩ B.GV k r, Q.CV k r Y f₁ g = Q.CV k r Y f₂ g

def FoldRev : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Dm : Set (Q.Mx k r)), IsOpen Dm →
    (∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm) →
    ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (s : ℂ) (a : List C.Letter), ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      foldCV k r s a.reverse J g = foldCV k r s a J g

def AdmLen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f)
    (a : List C.Letter), D.AdmAt S v a → a.length ≤ S.Ntop

def CVInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F : B.Mat k r → E) (Y s : ℂ),
    B.InCC A (m + (2 * r + k + 1)) F → B.InCC A m (s • Q.CV k r Y F)

def BesselFoldBuilt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, (∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      ∀ a : List C.Letter, a.length ≤ S.Ntop → ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
        B.JF (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) g =
          foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) g

def L2BoundAtTowerPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ ε : ℝ, 0 < ε → ∀ a : List C.Letter, a.length ≤ S.Ntop →
      B.normSq (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) ≠ ⊤

def FibMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        J (B.gq (T v).base q) ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' q.2

def TrSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ ρ,
      (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT

def BetaFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J₁ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
    ∀ J₂ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₁ (B.gq (T v).base q))) ≠ ⊤ →
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₂ (B.gq (T v).base q))) ≠ ⊤ →
      betaBig S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') (T v).base.μsec
          (fun g => B.hsVec (J₁ g)) (fun g => B.hsVec (J₂ g)) =
        MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e J₂)

end

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def OmB {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Set (B.Mat k r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g ∧
    ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def IsFrameB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

def rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Bs q.1)))

def trJB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawJ P Bs e J ρ)

def wR (k : ℕ) (TT : ℝ) (ζ : ℂ) : ℝ := Real.sqrt ((Complex.normSq ζ - TT) ^ (k - 1))

def rawR (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
    inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (Φ q.1.1 (NF.muZ P.k P.r μsec q.1.2)))

def FamR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : Prop :=
  IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ x.2 ∈ Dc x.1} ∧
  (∀ c ∈ OmX P.r, Q.IsDom P.k P.r Bs.z Bs.z' (Fin.last P.r) (Dc c)) ∧
  (∀ q : MA.Qp P.r P.TT, NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Dc q.1.1) ∧
  Q.FamFF P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) Dc Φ

end defs

def GTrChain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs),
      FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs}) (Q.resG P.k P.r (Fin.last P.r) J) ∧
      (∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P),
        rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ) ∧
      ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (Y : ℝ),
        rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ =
          ∑ a : Fin 2, ∑ b : Fin 2, rawR P Bs.μsec e
            (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
              (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
                (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) (Q.resG P.k P.r (Fin.last P.r) J)))) ρ

def GRawSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ ρ, rawR P Bs.μsec e Φ ρ ∈ MA.smSub P.r P.TT

def GQLFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2), FamR P Bs Dc (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ)

def GVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (b : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ) =
          MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def GVsTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ρ) =
          MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a)) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def GCore : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

section act

variable (P : M.Par)

theorem fst_zero : (0 : (MA.DQ P).Pr).1 = 0 := rfl

theorem fst_add (x y : (MA.DQ P).Pr) : (x + y).1 = x.1 + y.1 := rfl

theorem fst_mul (x y : (MA.DQ P).Pr) : (x * y).1 = x.1 * y.1 := rfl

def fstHom : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fst_sum {ι : Type} (s : Finset ι) (x : ι → (MA.DQ P).Pr) : (∑ i ∈ s, x i).1 = ∑ i ∈ s, (x i).1 :=
  map_sum (fstHom P) x s

theorem op_zero_apply (g : (MA.DQ P).R) : (0 : (MA.DQ P).Op) g = 0 := rfl

theorem op_add_apply (X Z : (MA.DQ P).Op) (g : (MA.DQ P).R) : (X + Z) g = X g + Z g := rfl

def evalHom (g : (MA.DQ P).R) : (MA.DQ P).Op →+ (MA.DQ P).R where
  toFun X := X g
  map_zero' := rfl
  map_add' _ _ := rfl

theorem op_sum_apply {ι : Type} (s : Finset ι) (X : ι → (MA.DQ P).Op) (g : (MA.DQ P).R) :
    (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g :=
  map_sum (evalHom P g) X s

theorem actA_zero (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 f = 0 := by
  funext π
  simp only [MA.actA, Matrix.zero_apply, fst_zero, Pi.zero_apply]
  exact Finset.sum_eq_zero fun π' _ => op_zero_apply P (f π')

theorem actA_add (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x + y) f = MA.actA P x f + MA.actA P y f := by
  funext π
  simp only [MA.actA, Matrix.add_apply, fst_add, Pi.add_apply]
  exact (Finset.sum_congr rfl fun π' _ => op_add_apply P _ _ (f π')).trans Finset.sum_add_distrib

theorem actA_sum {ι : Type} (s : Finset ι) (x : ι → MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (∑ i ∈ s, x i) f = ∑ i ∈ s, MA.actA P (x i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, actA_add, ih]

theorem actA_mul (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x * y) f = MA.actA P x (MA.actA P y f) := by
  funext π
  simp only [MA.actA, Matrix.mul_apply, fst_sum, fst_mul]
  have h1 : ∀ π'' : M.Ty P, (∑ j, (x π j).1 * (y j π'').1) (f π'') =
      ∑ j, (x π j).1 ((y j π'').1 (f π'')) := fun π'' =>
    op_sum_apply P Finset.univ (fun j => (x π j).1 * (y j π'').1) (f π'')
  have h2 : ∀ π' : M.Ty P, (x π π').1 (∑ π'', (y π' π'').1 (f π'')) =
      ∑ π'', (x π π').1 ((y π' π'').1 (f π'')) := fun π' => map_sum (x π π').1 _ _
  exact (Finset.sum_congr rfl fun π'' _ => h1 π'').trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun π' _ => (h2 π').symm))

theorem toSm_of_mem {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) : MA.toSm P u = ⟨u, h⟩ := by
  simp [MA.toSm, h]

theorem toSm_add {u v : MA.Qp P.r P.TT → ℂ} (hu : u ∈ MA.smSub P.r P.TT) (hv : v ∈ MA.smSub P.r P.TT) :
    MA.toSm P (u + v) = MA.toSm P u + MA.toSm P v := by
  rw [toSm_of_mem P hu, toSm_of_mem P hv, toSm_of_mem P (add_mem hu hv)]
  rfl

end act

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

