module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Formalism.LocalToGlobal.Columns.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_symVec_sub_ite_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg a j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.epsW X w i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 a).2.1
    · exact ((X.weightVectorsIntegral _).2.2 a).2.2.2
  refine wInt_of_zmod X k hg ?_
  have ha := a.2
  have hpos : (GlobalTheory.Mem.SymChar.Resid.posE D a).1 = a.1 := rfl
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1]
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.gramIntegral ⟨j.1, h1⟩ a).2.2
    rw [map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm] at h
    by_cases e : j = GlobalTheory.Mem.SymChar.Resid.posE D a
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by have := congrArg Fin.val e; simp only at this ⊢; omega)), map_one] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (Fin.ext (by have := congrArg Fin.val h'; simp only at this; omega))),
        map_zero] at h
  rw [dite_eq_right h1]
  have hne : ¬ j = GlobalTheory.Mem.SymChar.Resid.posE D a := fun e => by
    have := congrArg Fin.val e; rw [hpos] at this; omega
  rw [if_neg hne, sub_zero]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4]; exact (X.formsAtZero.2 a).2
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]; exact (X.gramIntegral a _).2.1
  · rw [dite_eq_right h3, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem inv_mul_mem_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) (a b : ∀ i, G i)
    (h : ∀ i, (a i)⁻¹ * b i ∈ H i) : a⁻¹ * b ∈ Subgroup.pi Set.univ H := fun i _ => h i

theorem reindex_finCongr_rfl {κ : Type} [CommRing κ] {a : ℕ} (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ (finCongr (rfl : a = a))).toMonoidHom y = y := by
  apply Units.ext
  ext i j
  rfl

theorem coarse_eq_blkOf {a r t m : ℕ} (hn : a = r + m * t) (i : Fin a) :
    Formalism.L2.Col.coarse r (List.replicate m t) i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp at hn
        omega
      · exact h0
    rw [Formalism.L2.Col.blkIdx_replicate ht m _ (by omega)]

theorem coarseBlockIndex_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem reindex_inv_mul_diag_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ *
        Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HK n κ r (List.replicate m t) := by
  subst h
  rw [reindex_finCongr_rfl]
  have hy' : y ∈ Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := by
    intro i j hij
    apply hy
    have hij' : Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val := hij
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn] at hij'
    exact hij'
  have hy2 : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := Formalism.L2.DIV.blockTri_blkOf_le r t hy
  refine Formalism.L2.Col.mem_HK.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy')
    (Formalism.L2.Col.diagEmb_mem_blockUT hrn _ _), fun i j hi hj => ?_⟩
  let Y : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn (List.replicate m t) (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hD : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Dd = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val]
    ext i' j'
    exact Formalism.L2.Col.diagMat_of_lt _ (show (Fin.castLE hrn i').val < r from i'.2) (show (Fin.castLE hrn j').val < r from j'.2)
  have hY : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Y = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val, Formalism.L2.DIV.upper_block_val_submatrix hra hy2]
    rfl
  have h1 : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) (Y⁻¹ * Dd) = 1 := by
    rw [map_mul, map_inv, hD, hY, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin r) κ => (g : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩) h1
  simp only [Formalism.L2.Col.blockZero_val, Units.val_one] at h2
  have h3 : ((y⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) : GL _ κ) : Matrix _ _ κ) i j =
      (1 : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := h2
  rw [h3]
  simp only [Matrix.one_apply, Fin.ext_iff]

theorem reindex_inv_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ * 1 ∈ Formalism.L2.Col.blockUT n κ r [b] := by
  subst h
  rw [reindex_finCongr_rfl, mul_one]
  refine Subgroup.inv_mem _ ?_
  intro i j hij
  apply hy
  have hij' : Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val := hij
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn] at hij'
  exact hij'

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd


set_option maxHeartbeats 1000000 in
theorem inv_redG_mul_g0Hat_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  intro X px I U L eG hI hL hG t q hz
  apply inv_mul_mem_pi
  intro w
  show _ ∈ (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H
  rw [redG_ptE X I L hL t q hz w]
  have hQ := RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q
  by_cases hw : w.1 ∈ (X.B.primes px).vGs
  · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw]
    have hPg : w.1 ∈ L.Pg := by rw [hL.Pg]; exact hw
    have hPg' : w.1 ∈ (L.datXt t).Pg := hPg
    have hy := Formalism.L2.DIV.parLev_g hQ hPg'
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w =
        Formalism.L2.Col.diagEmb (𝓞 X.B.fields.E ⧸ w.1.asIdeal) (Formalism.L2.Col.r_le_X' X.B.R) (g ⟨w.1, hw⟩) := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_mem _ w hw]
      rfl
    rw [hg0]
    have hgg : ∀ z, (eG.symm z) ⟨w.1, hw⟩ = z ⟨w.1, hPg⟩ := fun z => by
      rw [← hG (eG.symm z) w.1 hw hPg, MulEquiv.apply_symm_apply]
    have key := reindex_inv_mul_diag_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr
      (Formalism.L2.Col.r_le_X' X.B.R) _ hy
    convert key using 3 <;> first | rfl | exact heq_of_eq (hgg _) | exact hgg _
  · have hwQ : w.1 ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      classical
      exact (Finset.mem_union.1 w.2).resolve_left hw
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      simp only [ColIn.Q, tup_ixOf]
    have hQt : w.1 ∈ L.Q t := by
      rw [hL.Q t, e]
      exact hwQ
    have hQt' : w.1 ∈ (L.datXt t).Q := hQt
    have hy := Formalism.L2.DIV.parLev_q hQ hQt'
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw]
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w = 1 := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_not _ w hw]
    rw [hg0]
    exact reindex_inv_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hy

end GlobalTheory.Mem.R3.RowDeco
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelAtTwistPrimesIsOpen
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
set_option maxHeartbeats 4000000 in
theorem thetaOpen_levQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  intro X Pr R Ch sel S mu cst L G m2 hL hQg j b P
  have hc : cst.Ok := hL.cst_ok
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := L.h j b P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b', hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b' + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hinv {E : Type} [Field E] [NumberField E] [StarRing E]
      (P : HeightOneSpectrum (𝓞 E)) {n N : ℕ} (g : ↥(GLint E n P))
      (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
      lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
    unfold lqPrinc at hg ⊢
    intro i j
    set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
    set B := LinearMap.toMatrix'
      ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
    have hBA : B * A = 1 := by
      rw [hA, hB, ← LinearMap.toMatrix'_comp]
      have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
          ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
        refine LinearMap.ext fun x => ?_
        have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
          rw [inv_mul_cancel]
          rfl
        exact hx
      rw [hc, LinearMap.toMatrix'_id]
    have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
      intro a k
      rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
      have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
        show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
        rw [mem_localization_standardLattice]
        intro t
        rw [qth_intAt_iff]
        by_cases h : t = k
        · subst h
          simp
        · simp [Pi.single_apply, h]
      have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
        (g⁻¹ : GLint E n P).2
      have h2 := (hmem _).2 hs
      have h3 := (mem_localization_standardLattice P _).1 h2 a
      rw [qth_intAt_iff] at h3
      exact h3
    have hBm : B - 1 = -(B * (A - 1)) := by
      rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
    rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le _ (fun k _ => ?_)
    rw [map_mul]
    calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
      _ ≤ _ := by rw [one_mul]; exact hg k j
  
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (hinv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  have hH : g ∈ (L.levQ j b P).H := by
    rw [hL.grpQ j b P]
    exact Subgroup.mem_subgroupOf.2 hmem
  refine ⟨hH, ?_⟩
  apply Units.ext
  rw [hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]
  have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
    twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P' _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hPg]
  have hlam {P : HeightOneSpectrum (𝓞 X.E)} (hq : ((qOf P : ℕ) : 𝓞 X.E) ∈ P.asIdeal) (hq0 : ((qOf P : ℕ) : X.E) ≠ 0) {j : ℕ}
      (ξ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ) (y : AutY X R j) (hy : QClose P (qOf P) y) :
      LocE.lamQB ξ (R.k + j) (R.N j) (y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) = 1 := by
    classical
    unfold LocE.lamQB
    set D : Matrix (Fin (R.N j - (R.k + j))) (Fin (R.N j - (R.k + j))) X.E := Matrix.of fun s t : Fin (R.N j - (R.k + j)) =>
      Loc.atN ((y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1) with hD
    have hent : ∀ s t : Fin (R.N j - (R.k + j)), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 X.E ⧸ P.asIdeal)) s t := by
      intro s t
      have hs : R.k + j + s.1 < R.N j + cOf R j := by have := s.2; omega
      have ht : R.k + j + t.1 < R.N j + cOf R j := by have := t.2; omega
      have e1 : Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1) = Pi.single ⟨R.k + j + t.1, ht⟩ 1 := by
        funext l
        unfold Loc.eN
        rw [Pi.single_apply]
        congr 1
        apply propext
        constructor
        · intro h; exact Fin.ext h
        · intro h; rw [h]
      have e2 : D s t = ((toGLm X.E (R.N j + cOf R j) y : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E) ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩ := by
        rw [qsp_toGLm_apply, hD, Matrix.of_apply, e1]
        unfold Loc.atN
        rw [dite_eq_left hs]
        rfl
      obtain ⟨h1, h2⟩ := qth_red_entry P (qOf P) hq0 hq hy ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩
      rw [e2]
      refine ⟨h1, ?_⟩
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      by_cases hst : s = t
      · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst, redP_one]
      · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst, redP_zero]
    have hdet : redP P D.det = 1 := by
      rw [redP_det D fun s t => (hent s t).1]
      have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
      rw [this, Matrix.det_one]
    unfold LocE.unitV
    have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
    rw [dite_eq_left hu]
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [this, map_one, Units.val_one, inv_one]
  exact hlam hq hq0 _ _ hy

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeLevelUni

@[reducible] def unitsDiv : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnit {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDiv
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnit ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add (f := _)] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnit] using e

theorem exists_localAddChar_lifting_residueChar : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → ∀ ψ' : AddChar (kP s.w) ℂ, ψ' ≠ 1 → ∃ ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ, NG.IsPsi0 s ψ₀ ∧ ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ' (φ x) := by
  intro D s φ hφs hφ0 ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring
    (ψ'.compAddMonoidHom φ.toAddMonoidHom)
  refine ⟨ψ₀, ⟨fun x hx => ?_, ?_⟩, fun x => h x⟩
  · have hx1 : x ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : φ ⟨x, hx1⟩ = 0 := (hφ0 ⟨x, hx1⟩).2 hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
      s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    show ψ' (φ ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    obtain ⟨x, rfl⟩ := hφs y
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
      ψ₀ ((x : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
        s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    exact hy

theorem levelUni_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  intro D T L μ0 hL hPg i t hr ψ hψ s hs
  obtain ⟨-, -, -, h4⟩ := _root_.GlobalTheory.MtRed.km_reduction D D.R.nV
  obtain ⟨φ, hφs, hφ0, hφa, hφk⟩ := h4 s
  obtain ⟨hoffG, hoffQ, -, hunr⟩ := _root_.GlobalTheory.LevelTypePlace.offPlace D T L μ0 hL hPg t s hs
  let ψ' : AddChar (kP s.w) ℂ := (ψ s.w).compAddMonoidHom (negAddMonoidHom)
  have hne : ψ' ≠ 1 := by
    intro h1
    apply hψ s.w hs
    ext y
    have := congrArg (fun f : AddChar (kP s.w) ℂ => f (-y)) h1
    simpa [ψ'] using this
  obtain ⟨ψ₀, hP0, hψ₀⟩ := exists_localAddChar_lifting_residueChar D s φ hφs hφ0 ψ' hne
  have hres : IsRes (L.C.mu0 i * L.xiH t) s.w (L.chi ((i : ℕ) + 1) s.w)⁻¹ := by
    intro a k u hk hu
    have h1 := hL.chi i s.w hs a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : (L.xiH t).locK s.w k = 1 := hunr _ hunit
    have e : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k := rfl
    rw [e, h2, mul_one]
    exact h1
  obtain ⟨ξ, hξc, hξr⟩ := _root_.GlobalTheory.XiRes.exists_isCompAt_res D s φ hφs hφ0 hφa _ _ hres
  refine ⟨ψ₀, ξ, hP0, hξc, ⟨_root_.GlobalTheory.MtIn.UniMem.mem_iff D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ, ?_⟩⟩
  intro κ h hκ u hu
  refine _root_.GlobalTheory.MtChr.levChar_std_uni D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ ψ₀ ξ ?_ hξr κ h hκ u hu
  intro x
  rw [hψ₀ x]
  rfl

end GlobalTheory.TypeLevelUni

end
end

