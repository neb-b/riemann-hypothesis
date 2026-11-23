module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLevel

theorem finE_cast_mem {D : D7} (X Y : LSp D) (e : X = Y) (K : Subgroup (GL (Fin X.sp.rank) (Lev.EAf D)))
    (K' : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))) (h : HEq K K') (g : GA D X.sp) (hg : Lev.finE X.sp g ∈ K) :
    Lev.finE Y.sp (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g) ∈ K' := by
  subst e
  cases h
  exact hg

theorem toXf_mem_of_is {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J := by

  have hU : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hX := finE_cast_mem (columnBlock L D.R.m) ⟨D.sp.X', L.ΛX⟩ (colY_m L) _ _
    (_root_.GlobalTheory.FunObj.levRow_zero_eq_lev W S hL t (Nat.zero_le _)) k.1 hU
  exact hX

theorem levRow_zero_le : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _
  exact fun t k hk => toXf_mem_of_is ch.W ch.S.toGridChoice hS.core.lev t k hk

end GlobalTheory.FirstRowLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowInt

variable {D : D7}

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem smul_mem_latO_at : All fun {D} _ _ _ {G} _ _ =>
    ∀ i, i < D.R.m → ∀ v, ∀ e ∈ intAt D (· = v), ∀ u ∈ latRow G i,
      e • u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ v e he u hu
  have h0 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := hu.1
  have h1 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := latO_negSp_le _ _ _ _ _ h0
  have h2 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e he.2 u h1
  have h3 : MxAt (· = v) (e • u) := fun a b => Ideal.mul_mem_right _ _ he.1
  exact (GlobalTheory.AscFinWit.mem_latO_at h3).1 h2

end GlobalTheory.RowInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InversePartialFourierSumCompFromBlocks
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section
namespace GlobalTheory.BlockSubstFourier

theorem invFourierSum_comp_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) (hΦ : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ)
    (M₁ : GL D₁ k) (hM₁ : M₁ ∈ KO k D₁) (M₂ : GL D₂ k) (hM₂ : M₂ ∈ KO k D₂) (X : Matrix A (D₁ ⊕ D₂) k) :
    invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [compl_block_one] at hΦ ⊢
  set P := Assignment.two.block D₁ D₂ with hP
  have inr_mem : ∀ j : D₂, (Sum.inr j : D₁ ⊕ D₂) ∈ P := fun j => by simp [hP, Assignment.block]
  have inl_nmem : ∀ j : D₁, (Sum.inl j : D₁ ⊕ D₂) ∉ P := fun j => by simp [hP, Assignment.block]
  let eP : D₂ ≃ P := Equiv.ofBijective (fun j => ⟨Sum.inr j, inr_mem j⟩) ⟨fun a b h => by simpa using h, by
    rintro ⟨(j | j), h⟩
    · exact absurd h (inl_nmem j)
    · exact ⟨j, rfl⟩⟩
  have eP_apply : ∀ j, (eP j : D₁ ⊕ D₂) = Sum.inr j := fun j => rfl
  set M := fromBlocks M₁.val 0 0 M₂.val with hM
  set M' := fromBlocks M₁.val 0 0 (invT M₂).val with hM'
  set Nk : Matrix P P k := (invT M₂).val.submatrix eP.symm eP.symm with hNk
  have hNk_apply : ∀ a b, Nk (eP a) (eP b) = (invT M₂).val a b := fun a b => by simp [hNk]
  obtain ⟨u, hu⟩ := invT_mem_KO hM₂
  let N : Matrix P P 𝒪[k] := u.val.submatrix eP.symm eP.symm
  let N' : Matrix P P 𝒪[k] := (u⁻¹).val.submatrix eP.symm eP.symm
  have hNN : N * N' = 1 := by
    simp only [N, N', Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hNmap : N.map (fun x => (x : k)) = Nk := by
    rw [hNk, ← hu]; ext i j; rfl
  have hM₂i := (mem_KO_iff M₂).1 hM₂

  set X₂ : Matrix A D₂ k := X.submatrix id Sum.inr with hX₂
  have hXM₂ : (X * M).submatrix id Sum.inr = X₂ * M₂.val := by
    ext i j; simp [hM, hX₂, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
  have condP : ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ P, Z i j ∈ 𝒪[k]) ↔ ∀ i (j : D₂), Z i (Sum.inr j) ∈ 𝒪[k] := by
    intro Z
    refine forall_congr' fun i => ⟨fun h j => h _ (inr_mem j), fun h j hj => ?_⟩
    rcases j with j | j
    · exact absurd hj (inl_nmem j)
    · exact h j
  have hsum : ∀ (T : Matrix A P k) (Y : Matrix A (D₁ ⊕ D₂) k),
      pairCols P Y T = trace (T.submatrix id eP * (Y.submatrix id Sum.inr)ᵀ) := by
    intro T Y
    simp only [pairCols, trace, Matrix.mul_apply, diag_apply, transpose_apply, submatrix_apply, id]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Equiv.sum_comp eP (fun j => T i j * Y i j)).symm
  have hTN : ∀ T : Matrix A P k, (T * Nk).submatrix id eP = T.submatrix id eP * (invT M₂).val := by
    intro T; ext i j
    simp only [submatrix_apply, id, Matrix.mul_apply]
    rw [← Equiv.sum_comp eP]
    simp [hNk_apply]
  have hset : ∀ T : Matrix A P k, setCols P X T * M' = setCols P (X * M) (T * Nk) := by
    intro T; ext i (j | j)
    · simp [hM, hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
    · have h1 : setCols P (X * M) (T * Nk) i (Sum.inr j) = (T.submatrix id eP * (invT M₂).val) i j := by
        rw [← hTN]; simp only [setCols, Matrix.of_apply, dif_pos (inr_mem j), submatrix_apply, id]; rfl
      rw [h1]
      simp [hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
      rfl
  have hpair : ∀ T : Matrix A P k, pairCols P (X * M) (T * Nk) = pairCols P X T := by
    intro T
    rw [hsum, hsum, hTN, hXM₂, transpose_mul, invT_val]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ M₂.valᵀ, ← transpose_mul, Units.mul_inv, transpose_one,
      Matrix.one_mul]
  have setCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      setCols P Y (T + T') = setCols P Y T + setCols P 0 T' := by
    intro Y T T'; ext i j
    by_cases h : j ∈ P <;> simp [setCols, h]
  have pairCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      pairCols P Y (T + T') = pairCols P Y T + pairCols P Y T' := by
    intro Y T T'; simp [pairCols, add_mul, Finset.sum_add_distrib]
  have hcZ : ∀ z : k, valuation k z ≤ valuation k ((ϖ ^ e : kˣ) : k) → (((ϖ ^ e)⁻¹ : kˣ) : k) * z ∈ 𝒪[k] := by
    intro z hz
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
    exact hz
  rw [invFourierSum_apply, invFourierSum_apply]
  by_cases hX : ∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]
  · have hXM : ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      rw [condP] at hX ⊢
      intro i j
      have := congrFun (congrFun hXM₂ i) j
      simp only [submatrix_apply, id] at this
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (hX i l) (hM₂i.1 l j)
    rw [if_pos hX, if_pos hXM]
    let F : Matrix A P k → ℂ := fun T =>
      Φ (setCols P (X * M) ((ϖ ^ e)⁻¹ • T)) * (ψ (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • T)) : ℂ)
    have step : ∀ S : A → P → Res k e,
        Φ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S) * M') * (ψ (-pairCols P X ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) =
          F (liftRes S * N.map (fun x => (x : k))) := by
      intro S
      rw [hNmap]
      simp only [F]
      rw [← Matrix.smul_mul, ← hset, hpair]
    have hF : ∀ T Z : Matrix A P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        F (T + Z) = F T := by
      intro T Z hZ
      simp only [F, smul_add, setCols_add', pairCols_add', neg_add, AddChar.map_add_eq_mul]
      have hcZ' : ∀ i j, ((ϖ ^ e)⁻¹ • Z) i j ∈ 𝒪[k] := fun i j => by
        simpa [Units.smul_def] using hcZ _ (hZ i j)
      rw [hΦ.2, triv (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • Z)), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        exact mul_mem (hcZ' i j) (hXM i j j.2)
      · refine FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simpa [setCols, hj] using hcZ' i ⟨j, hj⟩
        · simp [setCols, hj]
    simp only [step]
    exact GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hNN F hF
  · have hXM : ¬ ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      intro h'
      apply hX
      rw [condP] at h' ⊢
      intro i j
      have hX₂ : X₂ = (X * M).submatrix id Sum.inr * (M₂⁻¹).val := by
        rw [hXM₂, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      have : X i (Sum.inr j) = ((X * M).submatrix id Sum.inr * (M₂⁻¹).val) i j := congrFun (congrFun hX₂ i) j
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (h' i l) (hM₂i.2 l j)
    rw [if_neg hX, if_neg hXM]

end GlobalTheory.BlockSubstFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.DepLat

variable {D : D7}

theorem finLat_of_nsmul {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : FinLat Λ) (hle : A ≤ Λ)
    {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a := continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

theorem finLat_depLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (p : Pair T), IsSelfDualC (G.pS p) (G.latS p) → IsSelfDualC (G.pT p) (G.latT p) → FinLat (depLat G p) := by
  intro D T L sc G p hS hT
  obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT p) (ΛT := G.latT p) hS (G.pl.modul_ne_bot sc)
  refine finLat_of_nsmul (GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)) (fun u hu => hu.1) hK
    fun u hu => ⟨nsmul_mem hu K, fun e he => ?_⟩
  rw [smul_comm]
  exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])) _ hu)

end GlobalTheory.AscFin.DepLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeLatOSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem finLat_latO_selfDual : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → FinLat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun S T ΛS ΛT hS hT => GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumFirstBlockBlockDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.BlockSubst

def firstCols (D₁ D₂ : Type) [Fintype D₁] [Fintype D₂] : D₁ ≃ ↥(Assignment.one.block D₁ D₂) where
  toFun j := ⟨Sum.inl j, by simp [Assignment.block]⟩
  invFun x := Sum.getLeft x.1 (by simpa [Assignment.block] using x.2)
  left_inv j := rfl
  right_inv x := by
    obtain ⟨x | x, hx⟩ := x
    · rfl
    · simp [Assignment.block] at hx

theorem forall_mem_block_one {D₁ D₂ : Type} [Fintype D₁] [Fintype D₂] (p : D₁ ⊕ D₂ → Prop) :
    (∀ j ∈ Assignment.one.block D₁ D₂, p j) ↔ ∀ j : D₁, p (Sum.inl j) := by
  constructor
  · intro h j; exact h _ (by simp [Assignment.block])
  · rintro h (j | j) hj
    · exact h j
    · simp [Assignment.block] at hj

theorem sum_mul_eq_trace {A D : Type} [Fintype A] [Fintype D] {k : Type} [Field k] (X Z : Matrix A D k) :
    ∑ i, ∑ j, X i j * Z i j = trace (X * Zᵀ) := by
  simp [trace, Matrix.mul_apply]

end GlobalTheory.BlockSubst

open GlobalTheory.BlockSubst in
theorem GlobalTheory.BlockSubst.fourierSum_blockDiag_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ Y : Matrix A (D₁ ⊕ D₂) k,
      fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) Y =
        fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂ Y
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  set P := Assignment.one.block D₁ D₂ with hP
  set E := firstCols D₁ D₂ with hE
  set c : k := ((ϖ ^ e : kˣ) : k) with hc
  obtain ⟨hM1, hM1'⟩ := (mem_KO_iff M₁).1 hM₁
  obtain ⟨hT1, hT1'⟩ := (mem_KO_iff _).1 (invT_mem_KO hM₁)
  have hsumP : ∀ f : ↥P → k, ∑ j : ↥P, f j = ∑ j : D₁, f (E j) := fun f =>
    (Fintype.sum_equiv E _ _ fun _ => rfl).symm
  have hX1 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inl j) = ∑ l, X i (Sum.inl l) * a l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  have hX2 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inr j) = ∑ l, X i (Sum.inr l) * b l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  set Y₁ : Matrix A D₁ k := Matrix.of fun i j => Y i (Sum.inl j) with hY₁
  have hYH : ∀ i j, (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i (Sum.inl j) = (Y₁ * (invT M₁).val) i j := by
    intro i j; rw [hX1]; simp [Y₁, Matrix.mul_apply]
  have hinv : (invT M₁).val * M₁.valᵀ = 1 := by
    rw [invT_val, ← transpose_mul, Units.mul_inv, transpose_one]
  have hinv' : M₁.val * ((invT M₁).val)ᵀ = 1 := by
    rw [invT_val, transpose_transpose, Units.mul_inv]
  have hint : ∀ (X : Matrix A D₁ k) (B : Matrix D₁ D₁ k), (∀ i j, B i j ∈ 𝒪[k]) →
      (∀ i j, c * X i j ∈ 𝒪[k]) → ∀ i j, c * (X * B) i j ∈ 𝒪[k] := by
    intro X B hB hX i j
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Subring.sum_mem _ fun l _ => by rw [← mul_assoc]; exact mul_mem (hX i l) (hB l j)
  have hcond : (∀ i, ∀ j ∈ P, c * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ P, c * (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i j ∈ 𝒪[k]) := by
    simp only [hP, forall_mem_block_one, hYH]
    constructor
    · intro h; exact hint Y₁ _ hT1 h
    · intro h i j
      have := hint _ M₁.valᵀ (fun i j => by simpa using hM1 j i) h i j
      rwa [Matrix.mul_assoc, hinv, Matrix.mul_one] at this
  set YH := Y * fromBlocks (invT M₁).val 0 0 M₂.val with hYHdef
  have hset : ∀ T' : Matrix A ↥P k, setCols P YH (T' * M₁.val.submatrix E.symm E.symm) =
      setCols P Y T' * fromBlocks M₁.val 0 0 M₂.val := by
    intro T'
    ext i (j | j)
    · rw [hX1]
      simp only [setCols, Matrix.of_apply]
      rw [dite_eq_left (by simp [hP, Assignment.block]), Matrix.mul_apply, hsumP]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dite_eq_left (by simp [hP, Assignment.block])]
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      rfl
    · rw [hX2]
      simp only [setCols, Matrix.of_apply]
      rw [dite_eq_right (by simp [hP, Assignment.block]), hYHdef, hX2]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dite_eq_right (by simp [hP, Assignment.block])]
  have hpc : ∀ (Z : Matrix A (D₁ ⊕ D₂) k) (S : Matrix A ↥P k),
      pairCols P Z S = ∑ i, ∑ j : D₁, S i (E j) * Z i (Sum.inl j) := by
    intro Z S; simp only [pairCols]; exact Finset.sum_congr rfl fun i _ => hsumP _
  have hpair : ∀ T' : Matrix A ↥P k, pairCols P YH (T' * M₁.val.submatrix E.symm E.symm) = pairCols P Y T' := by
    intro T'
    set T₁ : Matrix A D₁ k := Matrix.of fun i j => T' i (E j) with hT₁
    have hTN : ∀ i j, (T' * M₁.val.submatrix E.symm E.symm) i (E j) = (T₁ * M₁.val) i j := by
      intro i j; rw [Matrix.mul_apply, hsumP]; simp [T₁, Matrix.mul_apply]
    rw [hpc, hpc]
    simp only [hTN, hYH]
    calc ∑ i, ∑ j, (T₁ * M₁.val) i j * (Y₁ * (invT M₁).val) i j
        = trace ((T₁ * M₁.val) * (Y₁ * (invT M₁).val)ᵀ) := sum_mul_eq_trace _ _
      _ = trace (T₁ * Y₁ᵀ) := by
          rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc M₁.val, hinv', Matrix.one_mul]
      _ = ∑ i, ∑ j, T' i (E j) * Y i (Sum.inl j) := (sum_mul_eq_trace T₁ Y₁).symm
  rw [fourierSum_apply, fourierSum_apply]
  beta_reduce
  split_ifs with h1 h2 h2
  · congr 1
    obtain ⟨u, hu⟩ := hM₁
    let N : Matrix ↥P ↥P 𝒪[k] := u.val.submatrix E.symm E.symm
    let N' : Matrix ↥P ↥P 𝒪[k] := (u⁻¹).val.submatrix E.symm E.symm
    have hN : N * N' = 1 := by
      simp only [N, N', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
    have hNk : N.map (fun x => (x : k)) = M₁.val.submatrix E.symm E.symm := by
      rw [← hu]; rfl
    have hF : ∀ T Z : Matrix A ↥P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        Φ (setCols P YH (T + Z)) * (ψ (pairCols P YH (T + Z)) : ℂ) =
          Φ (setCols P YH T) * (ψ (pairCols P YH T) : ℂ) := by
      intro T Z hZ
      have e1 : setCols P YH (T + Z) = setCols P YH T + setCols P 0 Z := by
        ext i j; by_cases hj : j ∈ P <;> simp [setCols, hj]
      have e2 : pairCols P YH (T + Z) = pairCols P YH T + pairCols P YH Z := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      rw [e1, e2, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P YH Z), mul_one]
      · refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        have h3 := (Valuation.mem_integer_iff _ _).1 (h2 i j j.2)
        rw [map_mul] at h3
        rw [Valuation.mem_integer_iff, map_mul]
        exact (show valuation k (Z i j) * valuation k (YH i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) * valuation k (YH i j) by
          gcongr; exact hZ i j).trans h3
      · rw [GlobalTheory.SplitFlip.stdLat, smul_diagLat]
        simp only [Pi.one_apply, mul_one]
        change ∀ i j, valuation k (setCols P 0 Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)
        intro i j
        by_cases hj : j ∈ P
        · simpa [setCols, hj] using hZ i ⟨j, hj⟩
        · simp [setCols, hj]
    have key : ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T * N.map (fun x => (x : k)))) *
          (ψ (pairCols P YH (liftRes T * N.map (fun x => (x : k)))) : ℂ) =
        ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T)) * (ψ (pairCols P YH (liftRes T)) : ℂ) :=
      GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hN (fun T' => Φ (setCols P YH T') * (ψ (pairCols P YH T') : ℂ)) hF
    rw [← key, hNk]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hset, hpair]
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

theorem GlobalTheory.RowTest.rowTest_realisation : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.RowClaim.HidaSetting large₂ R.toRealDat F.lv2 → (∃ ch : GlobalTheory.RowTest.Choice R.toRealDat, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro hC hL hI hCo hS hF hSR hR
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.T.rowTest_hilbertModels_of_choiceClaims hC hL hI hCo hS hF hSR hR
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hCF0 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hSet hch => ?_⟩
  exact _root_.GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 D G Pl0 I0 T0 A3 Ks R F (hx₀ D large₂ hε hx G Pl0 T0 _ Ks R.toRealDat F.lv2 hSet hch)
end

