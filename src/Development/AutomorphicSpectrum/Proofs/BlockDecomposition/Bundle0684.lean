module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMaximalCompactIffIntegralImage
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.SplitK

open Formalism.UG (GLint)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_stabLoc_std_iff (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E m) v ↔
      splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring ∧
        splitHom σ J (τ.comp σ) g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring := by
  have key : ∀ y : Fin m → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E m) v ↔
      (∀ i, splitVec τ y i ∈ v.adicCompletionIntegers F) ∧
        ∀ i, splitVec (τ.comp σ) y i ∈ v.adicCompletionIntegers F := fun y => by
    rw [mem_latLoc_iff_split τ h, mem_splitLat_stdLattice h, mem_splitLat_stdLattice h]
  rw [mem_stabLoc]
  simp only [key, splitVec_matHom_mulVec, mem_GLint_iff_mulVec]
  constructor
  · intro H
    refine ⟨fun u => ?_, fun u => ?_⟩
    · simpa using H (splitIncl h τ u)
    · simpa using H (splitIncl h (τ.comp σ) u)
  · rintro ⟨H1, H2⟩ y
    exact and_congr (H1 _) (H2 _)


omit [NumberField E] in
theorem transpose_splitHom_comp (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1) (g : GLoc σ J v) :
    (splitHom σ J (τ.comp σ) g).1ᵀ = -(J.map τ * (splitHom σ J τ g⁻¹).1 * J.map τ) := by
  have e := splitHom_unitary τ g
  have i1 : (splitHom σ J τ g).1 * (splitHom σ J τ g⁻¹).1 = 1 := by
    rw [map_inv, Units.mul_inv]
  calc (splitHom σ J (τ.comp σ) g).1ᵀ
      = -((splitHom σ J (τ.comp σ) g).1ᵀ * (J.map τ * J.map τ)) := by rw [hJ]; simp
    _ = -(((splitHom σ J (τ.comp σ) g).1ᵀ * J.map τ * (splitHom σ J τ g).1) *
          (splitHom σ J τ g⁻¹).1 * J.map τ) := by
        congr 1
        rw [Matrix.mul_assoc _ (splitHom σ J τ g).1, i1]
        simp [Matrix.mul_assoc]
    _ = _ := by rw [e]

theorem mul_entry_mem {ι : Type} [Fintype ι] {X Y : Matrix ι ι (Fv F v)}
    (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers F) (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers F) (i j : ι) :
    (X * Y) i j ∈ v.adicCompletionIntegers F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hX i l) (hY l j)


omit [NumberField E] in
theorem comp_mem_GLint (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1)
    (hint : ∀ i j, J.map τ i j ∈ v.adicCompletionIntegers F) {g : GLoc σ J v}
    (hg : splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring) :
    splitHom σ J (τ.comp σ) g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  have h2' : ∀ i j, (splitHom σ J τ g⁻¹).1 i j ∈ v.adicCompletionIntegers F := by
    rw [map_inv]; exact h2
  have h1' : ∀ i j, (splitHom σ J τ g⁻¹⁻¹).1 i j ∈ v.adicCompletionIntegers F := by
    rw [inv_inv]; exact h1
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun₂ (transpose_splitHom_comp τ hJ g) j i
    rw [Matrix.transpose_apply] at e
    rw [e, Matrix.neg_apply]
    exact neg_mem (mul_entry_mem (mul_entry_mem hint h2') hint j i)
  · have e := congrFun₂ (transpose_splitHom_comp τ hJ g⁻¹) j i
    rw [Matrix.transpose_apply, map_inv] at e
    rw [e, Matrix.neg_apply]
    exact neg_mem (mul_entry_mem (mul_entry_mem hint h1') hint j i)

theorem mem_stabLoc_std_iff_GLint (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1)
    (hint : ∀ i j, J.map τ i j ∈ v.adicCompletionIntegers F) {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E m) v ↔
      splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring :=
  (mem_stabLoc_std_iff h τ).trans ⟨fun H => H.1, fun H => ⟨H, comp_mem_GLint τ hJ hint H⟩⟩

end Gen

section Blocks

variable {D : D7} {n : ℕ} {v : Pl D}

theorem blkGL_val {R : Type} [CommRing R] (x : GL (Fin (n + n)) R) (i j : Ix n) :
    (blkGL n x).1 i j = x.1 (finSumFinEquiv i) (finSumFinEquiv j) := rfl

theorem mem_GLint_iff_blkGL {x : GL (Fin (n + n)) (Lv D v)} :
    x ∈ GLint (Fin (n + n)) (v.adicCompletionIntegers D.host.F).toSubring ↔
      blkGL n x ∈ GLint (Ix n) (v.adicCompletionIntegers D.host.F).toSubring := by
  rw [mem_GLint_iff, mem_GLint_iff, ← map_inv]
  simp only [blkGL_val]
  constructor
  · exact fun H => ⟨fun i j => H.1 _ _, fun i j => H.2 _ _⟩
  · refine fun H => ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using H.1 (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
    · simpa using H.2 (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem Jst_map_sq (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    (Jst D n).map τ * (Jst D n).map τ = -1 := by
  have e : (Jst D n).map τ = blk4 0 1 (-1) 0 := by
    ext i j
    simp only [Matrix.map_apply, Jst, blk4, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
      simp [Matrix.one_apply]
  have e2 : (Matrix.fromBlocks (-1) 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (Fv D.host.F v)) = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  rw [e, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero]
  rw [e2]
  ext i j
  simp [Matrix.one_apply]

theorem Jst_map_int (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Fin (n + n)) :
    (Jst D n).map τ i j ∈ v.adicCompletionIntegers D.host.F := by
  simp only [Matrix.map_apply, Jst, blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

end Blocks

theorem mem_KUpFin_iff (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    g ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v ↔
      thU D n v τ g ∈ (inL (O := Ov D v) (L := Lv D v) (n := n)).range :=
  (mem_stabLoc_std_iff_GLint (isCMExt_host D) τ (Jst_map_sq τ) (Jst_map_int τ)).trans
    mem_GLint_iff_blkGL

end GlobalTheory.CompanionTheory.Jp.SplitK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.UpTri

theorem transpose_block_matrix {A : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A) :
    (GlobalTheory.StdUnn.blk4 a b c d)ᵀ = GlobalTheory.StdUnn.blk4 aᵀ cᵀ bᵀ dᵀ := by
  ext i j
  simp only [GlobalTheory.StdUnn.blk4, Matrix.transpose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blocks_of_unitary {K : Type} [CommRing K] {n : ℕ} (a : GL (Fin n) K) (b d a' b' c' d' : Matrix (Fin n) (Fin n) K)
    (h : (GlobalTheory.StdUnn.blk4 a' b' c' d')ᵀ * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * GlobalTheory.StdUnn.blk4 a.1 b 0 d =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0) : c' = 0 ∧ a'ᵀ * d = 1 := by
  rw [transpose_block_matrix, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  have e1 : c'ᵀ * a.1 = 0 := by simpa using h1
  have e2 : c'ᵀ = 0 := by
    have := congrArg (· * (a⁻¹).1) e1
    simpa [Matrix.mul_assoc, -Matrix.coe_units_inv] using this
  have e3 : c' = 0 := by simpa using congrArg Matrix.transpose e2
  subst e3
  exact ⟨rfl, by simpa using h2⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem upperParabolic_height_of_split (h : IsCMExt F E σ) (hQ : Q = GlobalTheory.StdUnn.blk4 0 1 (-1) 0) (τ : E →ₐ[F] Fv F v)
    (y : GLoc σ Q v) (a d : GL (Fin n) (Fv F v)) (b : Matrix (Fin n) (Fin n) (Fv F v))
    (hy : (splitHom σ Q τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1) :
    ∃ hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q,
      absEv F E v (GlobalTheory.LocIntw.aUp (Fv F v) σ Q ⟨y, hm⟩) = ‖a.1.det‖₊ / ‖d.1.det‖₊ := by
  obtain ⟨A, B, C, D', e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR (Fv F v) σ y)
  have key : ∀ ρ : E →ₐ[F] Fv F v, (splitHom σ Q ρ y).1 =
      GlobalTheory.StdUnn.blk4 (A.map (splitProj ρ)) (B.map (splitProj ρ)) (C.map (splitProj ρ)) (D'.map (splitProj ρ)) := by
    intro ρ
    rw [splitHom_val]
    change (GlobalTheory.LocIntw.matR (Fv F v) σ y).map (splitProj ρ : Fv F v ⊗[F] E →+* Fv F v) = _
    rw [e]
    exact GlobalTheory.LocIntw.blockMatrix_map _ _ _ _ _
  obtain ⟨ha, -, hc, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective ((key τ).symm.trans hy)
  have hQτ : Q.map τ = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    subst hQ
    have := GlobalTheory.LocIntw.blockMatrix_map (τ : E →+* Fv F v) (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0
    rw [Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have u := splitHom_unitary τ y
  rw [key (τ.comp σ), hQτ, hy] at u
  obtain ⟨hc', hd'⟩ := blocks_of_unitary a b d.1 _ _ _ _ u
  have hC : C = 0 := splitMat_ext h τ
    (by rw [hc]; exact (Matrix.map_zero _ (map_zero _)).symm)
    (by rw [hc']; exact (Matrix.map_zero _ (map_zero _)).symm)
  have hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q := (GlobalTheory.LocIntw.mem_siegelParabolic_iff_lowerLeft_eq_zero hQ).2 fun i j => by
    rw [e, hC, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp
  refine ⟨hm, ?_⟩
  have hA : GlobalTheory.StdUnn.blkA (GlobalTheory.LocIntw.matR (Fv F v) σ y) = A := by rw [e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  have d1 : splitProj τ A.det = a.1.det := by
    rw [← ha]
    exact RingHom.map_det (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) A
  have d2 : splitProj (τ.comp σ) A.det * d.1.det = 1 := by
    have : splitProj (τ.comp σ) A.det = (A.map (splitProj (τ.comp σ))).det :=
      RingHom.map_det (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v) A
    rw [this, ← Matrix.det_transpose, ← Matrix.det_mul, hd', Matrix.det_one]
  rw [absEv_apply, GlobalTheory.LocIntw.coe_aUp, hA, GlobalTheory.SplitInterDet.norm_eq_split h τ, nnnorm_mul, d1,
    eq_inv_of_mul_eq_one_left d2, nnnorm_inv, div_eq_mul_inv]

end General

theorem upperParabolic_height (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v))
    (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (H : thU D n v τ y = pM a d b) :
    ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n),
      absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) =
        nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  have hy : (splitHom D.sp.cm.sig (Jst D n) τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1 := by
    have e : ((splitHom D.sp.cm.sig (Jst D n) τ y).1).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks a.1 b 0 d.1 := congrArg Units.val H
    rw [GlobalTheory.StdUnn.blk4, ← e]
    ext i j
    simp
  exact upperParabolic_height_of_split (isCMExt_host D) (GlobalTheory.LocIntw.Jst_eq D n) τ y a d b hy

end GlobalTheory.CompanionTheory.Jp.UpTri

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGeneric
section
namespace GlobalTheory.CompanionTheory.Jp

theorem rank_residue_map_le_rank_fraction_map :
    ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L]
      [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O),
      (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  intro O L _ _ _ _ _ _ n T
  obtain ⟨S, τ, hdet⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O)
    (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl
  have hres : IsLocalRing.residue O (T.submatrix S τ).det =
      ((T.map (IsLocalRing.residue O)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hfrac : algebraMap O L (T.submatrix S τ).det =
      ((T.map (algebraMap O L)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hO : (T.submatrix S τ).det ≠ 0 := by
    intro h
    apply hdet
    rw [← hres, h, map_zero]
  have hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0 := by
    rw [← hfrac]
    intro h
    exact hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))
  calc (T.map (IsLocalRing.residue O)).rank
      = ((T.map (algebraMap O L)).submatrix S τ).rank := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)),
          Fintype.card_fin]
    _ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem hecke_one : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩

theorem hecke_mul_inv {χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ') : IsHeckeChar D (1 * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have e : (⇑((1 : (AE D)ˣ →* Circle) * χ'⁻¹)) = fun x => (χ' x)⁻¹ := by
      funext x; simp
    rw [e]
    exact h.1.inv
  · simpa using h.2 x

theorem fj_smul {n ρ p' : ℕ} {hn : ρ + p' = n} (M : Maps D hn) (m : Meas D ρ p') (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (c : ℂ) (F : G D n → ℂ) (g : G D n) (φ : Mx D ρ p' → ℂ) :
    FJ M m ψ b₀ (c • F) g φ = c * FJ M m ψ b₀ F g φ := by
  simp only [FJ, PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem eis_pole_free (hRS : RSec) (hEH : EisHol) (hp : 2 ≤ p) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn) (m : Meas D 1 p')
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D 1) (hdet : b₀.1.det ≠ 0)
    {χ' : (AE D)ˣ →* Circle} (hχ' : IsHeckeChar D χ') {θ : InfFam D} (hθ : IsInfFam θ) {Ω : G D p' → Mx D 1 p' → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (g : G D p) :
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) (σ : ℂ)) g Ω) 1)
      (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
  obtain ⟨c1, c2, c3⟩ := hRS D p 1 p' hn M m ψ hψ b₀ hdet 1 χ' hecke_one hχ' θ hθ Ω hΩ H hH ((p : ℂ) / 2) f hf.1 hf.2 g
  have hd := hEH D p' (1 * χ'⁻¹) (hecke_mul_inv hχ') _ (fun z => Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) z) g Ω) c1 c2 c3 1
  have hopen : IsOpen {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_re)
  have hpp : (p : ℝ) = 1 + p' := by rw [← hn]; push_cast; ring
  have hp' : (1 : ℝ) ≤ p' := by
    have : 1 ≤ p' := by omega
    exact_mod_cast this
  have hmem : ((((p : ℝ) / 2 : ℝ)) : ℂ) ∈ {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} := by
    simp only [mem_setOf_eq, Complex.ofReal_re, hpp, Nat.cast_one]
    constructor <;> linarith
  have hcont := (hd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have h1 := (hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt (x := (p : ℝ) / 2))).mono_left
    (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
  have h2 : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ)) (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
    have : Continuous fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) := by fun_prop
    have h3 := (this.tendsto ((p : ℝ) / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
    simpa using h3
  simpa using h2.mul h1

theorem pc_vanish (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal) (hS : SphBound)
    (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn)
    (m : Meas D 1 p') (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (b₀ : HermE D 1) (hb : IsDiagInv b₀) (g : G D p) : pc M m ψ b₀ (resA H f) g = 0 := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨χ', hχ', hres⟩ := hHE D 1
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  have hU := ufil_le p
  have key : ∀ g₀ : G D p, (fun y => pc M m ψ b₀ (resA H f) (M.sh y * g₀)) = 0 := fun g₀ => by
    refine hTT D 1 p' m ψ hψ b₀ hb χ' hχ' hres (fun h => absurd h one_ne_zero) θ hθ _ ?_ ?_ ?_
    · exact ((hPB D p 1 p' hn M m ψ hψ b₀).1 _ hAc hAl).comp (M.sh_cont.mul continuous_const)
    · obtain ⟨C₁, hC₁, -, hb₁⟩ := (hPB D p 1 p' hn M m ψ hψ b₀).2 g₀
      obtain ⟨B, hB⟩ := hC₁.exists_bound_of_continuousOn hAc.continuousOn
      exact ⟨B, hb₁ _ hAc hAl B hB⟩
    · intro Ω hΩ
      have hint : Integrable (Ω 1) m.μ := GlobalTheory.SchwartzAInt.integrable_of_mem D θ hθ 1 p' m.μ m.𝓕 m.hμ (Ω 1) (hΩ.mem 1)
      have hFl : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), Continuous (res H f σ) ∧ LeftInv (GF D p) (res H f σ) := by
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ using ⟨res_cont hS hp1 hH hC hcov hf hσ, res_leftInv hH hf σ⟩
      have hlim := _root_.GlobalTheory.CompanionTheory.FJLim.fj_tendsto hPB D p 1 p' hn M m ψ hψ b₀ ((ufil p : Ultrafilter ℝ) : Filter ℝ) (fun σ => res H f σ) (resA H f)
        hAc hAl hFl (fun C' hC' ε hε => resA_unif hS hp1 hH hC hcov hf hC' hε)
        (hFl.mono fun σ hσ y g' => _root_.GlobalTheory.CompanionTheory.PcAdd.pc_sub hPB D p 1 p' hn M m ψ hψ b₀ _ _ hσ.1 hσ.2 hAc hAl y g') g₀ (Ω 1) hint
      have hzero : Tendsto (fun σ => FJ M m ψ b₀ (res H f σ) g₀ (Ω 1)) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 0) := by
        refine ((eis_pole_free hRS hEH hp hn M m ψ hψ b₀ hb.2 hχ' hθ hΩ hH hf g₀).mono_left hU).congr' ?_
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ
        have e : res H f σ = ((σ - p / 2 : ℝ) : ℂ) • eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) := rfl
        rw [e, fj_smul, hFJ D p 1 p' hn M m ψ hψ b₀ hb.2 1 χ' hecke_one hχ' θ hθ Ω hΩ (σ : ℂ) _
          (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) (by simpa using hσ.1) g₀]
      exact tendsto_nhds_unique hlim hzero
  have := congrFun (key ((M.sh 0)⁻¹ * g)) 0
  simpa [← mul_assoc] using this

theorem resA_n_inv (hME : MapsExist) (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal)
    (hPF : PcFc) (hS : SphBound) (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {nb : hermA D p → G D p}
    {lam : Measure (hermA D p)} {𝓖 : Set (hermA D p)} (hCd : CoefData (D := D) (n := p) nb lam 𝓖) (b : hermA D p) (g : G D p) :
    resA H f (nb b * g) = resA H f g := by
  have hp1 : 1 ≤ p := by omega
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.AdelicChar.exists_isCharAF D.host.F D.sp.cm.totReal
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hn : 1 + (p - 1) = p := by omega
  obtain ⟨⟨M⟩, ⟨m⟩⟩ := hME D p 1 (p - 1) hn
  obtain ⟨⟨M0⟩, ⟨m0⟩⟩ := hME D p 0 p (zero_add p)
  have hr : RankLT ψ (resA H f) 1 := (hPF D p 1 (p - 1) hn M m ψ hψ _ hAc hAl).1 fun b₀ hb g =>
    pc_vanish hHE hFJ hPB hRS hEH hTT hS hp hH hC hcov hf hn M m ψ hψ hθ b₀ hb g
  let b0 : HermE D 0 := ⟨0, by ext i; exact i.elim0⟩
  let β : HermE D p := ⟨0, by simp⟩
  have hdet : b0.1.det ≠ 0 := by simp [b0]
  have hβ : IsExt (zero_add p) b0 β := by
    ext i j
    simp only [bl, Matrix.submatrix_apply, β]
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm i = a
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm j = c
    rcases a with a | a
    · exact a.elim0
    · rcases c with c | c
      · exact c.elim0
      · simp
  have h2 := (hPF D p 0 p (zero_add p) M0 m0 ψ hψ _ hAc hAl).2 hr b0 hdet β hβ nb lam 𝓖 hCd
  exact GlobalTheory.T.invariance_of_constant_fourier_coefficient D p ψ nb lam 𝓖 hCd _ hAc hAl β rfl (fun g => by
    rw [← h2 g]; exact _root_.GlobalTheory.CompanionTheory.PcZero.pc_eq D p (zero_add p) M0 m0 ψ b0 _ g) b g

theorem resMu_main : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound →
    PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  intro hME hHt hHE hFJ hPB hRS hEH hTT hPF hS _ hCE D p hp
  have hp1 : 1 ≤ p := by omega
  obtain ⟨⟨H, hH⟩, C, hC, hcov⟩ := hHt D p
  refine ⟨fun f => resA H f 1, ?_⟩
  exact
    { add := fun f f' hf hf' => resA_add hS hp1 hH hC hcov hf hf' 1
      smul := fun c f hf => resA_smul hS hp1 hH hC hcov hf c 1
      pos := fun f hf h => resA_pos hS hp1 hH hC hcov hf h 1
      bound := fun H' hH' => resA_bound hS hp1 hH hC hcov H' hH'
      inv_n := fun x b hx f hf => by
        have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨x, hx⟩
        obtain ⟨nb, lam, 𝓖, hCd⟩ := hCE D p
        have e : x = nb ⟨b, hb⟩ * 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by rw [mul_one, hx, hCd.1])
        have h1 := resA_translate hS hp1 hH hC hcov hf x
        have h2 := resA_n_inv hME hHE hFJ hPB hRS hEH hTT hPF hS hp hH hC hcov hf hCd ⟨b, hb⟩ 1
        rw [← e] at h2
        exact h1.symm.trans h2
      inv_rat := fun γ hγ f hf => by
        have h1 := resA_translate hS hp1 hH hC hcov hf γ
        have h2 := resA_leftInv hS hp1 hH hC hcov hf γ hγ 1
        rw [mul_one] at h2
        exact h1.symm.trans h2
      lim := fun f hc hl a ha => (resA_lim hS hp1 hH hC hcov f hc hl a ha).2 }

end GlobalTheory.CompanionTheory.ResMu
end
end

