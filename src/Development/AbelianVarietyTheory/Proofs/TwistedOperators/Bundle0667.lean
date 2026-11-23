module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArrowLocalModelMovedFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.ArrowModel

section Moves
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z']
  [DecidableEq Z']

def moveHomeo (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun x := ((εT⁻¹).val * x * εS.val).submatrix σT σS
  invFun z := εT.val * z.reindex σT σS * (εS⁻¹).val
  left_inv x := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv z := by
    simp only [Matrix.reindex_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one,
      Matrix.submatrix_submatrix, Equiv.symm_comp_self, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  continuous_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_submatrix _ _
  continuous_invFun := (continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul continuous_const


omit [IsNonarchimedeanLocalField k] in
theorem comp_homeo_mem_SB {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (e : X ≃ₜ X') {Φ : X' → ℂ}
    (h : Φ ∈ SB X') : Φ ∘ e ∈ SB X :=
  ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_back {K : Type} [Field K] {n N n' N' : ℕ} (h : N = n) (h' : N' = n') (L₁ : GL (Fin n) K) (L₀ : GL (Fin n') K)
    (x : Matrix (Fin N) (Fin N') K) :
    (((L₁⁻¹).val * (L₁.val.submatrix id (Fin.cast h) * x * ((L₀⁻¹).val).submatrix (Fin.cast h') id) * L₀.val).submatrix
      (Fin.cast h) (Fin.cast h')) = x := by
  subst h h'
  simp only [Fin.cast_refl, Matrix.submatrix_id_id]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end Moves

theorem indicator_move : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' Z Z' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (εS : GL Y' k) (εT : GL Y k), εS ∈ KO k Y' → εT ∈ KO k Y → ∀ (σS : Z' ≃ Y') (σT : Z ≃ Y) (O : SB (Matrix Z Z' k)), IsOne O → ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ ∀ x, Φ.1 x = O.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS) := by
  intro k _ _ _ _ Y Y' Z Z' _ _ _ _ _ _ _ _ εS εT hS hT σS σT O hO
  let e := moveHomeo εS εT σS σT
  refine ⟨⟨O.1 ∘ e, comp_homeo_mem_SB e O.2⟩, ?_, fun x => rfl⟩
  unfold IsOne at hO ⊢
  funext x
  change O.1 (e x) = _
  rw [hO]
  have key : (∀ r q, e x r q ∈ (ValuativeRel.valuation k).integer) ↔ ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer := by
    have h1 := GlobalTheory.SplitFlip.mul_mul_mem_matLat_iff (inv_mem hT) hS x
    rw [GlobalTheory.SplitFlip.mem_matLat_stdLat, GlobalTheory.SplitFlip.mem_matLat_stdLat] at h1
    rw [← h1]
    exact ⟨fun h r q => by simpa [e, moveHomeo] using h (σT.symm r) (σS.symm q), fun h r q => h _ _⟩
  by_cases h : ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer
  · rw [Set.indicator_of_mem (show e x ∈ {x : Matrix Z Z' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from key.2 h),
      Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from h)]
  · rw [Set.indicator_of_notMem (show e x ∉ {x : Matrix Z Z' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from fun H => h (key.1 H)),
      Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from h)]

theorem exists_moved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' Z Z' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (Φ₁ : SB (Matrix Y Y' k)), ∃ Φ' : SB (Matrix Z Z' k), ∀ z, Φ'.1 z = Φ₁.1 (εT.val * z.reindex σT σS * (εS⁻¹).val) := by
  intro k _ _ _ _ Y Y' Z Z' _ _ _ _ _ _ _ _ εS εT σS σT Φ₁
  exact ⟨⟨Φ₁.1 ∘ (moveHomeo εS εT σS σT).symm, comp_homeo_mem_SB _ Φ₁.2⟩, fun z => rfl⟩

theorem coord_up : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (p : Place D (Kw w)), IsPlc w p → ∀ (j : ℕ) (hj : j < D.R.m) (x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))) (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)), ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, hj⟩ ⟨le_rfl, hj.le⟩ ((p.up (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) x).map fun a => cpt w (toEAf D a)) = xᵀ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t w p hp j hj x
  have hm : ∀ M : Matrix (Fin (ch.G.V (.grid D.R.m (j + 1))).rank) (Fin (ch.G.V (.grid D.R.m j)).rank) (Kw w),
    (M.map p.ι).map (fun a => cpt w (toEAf D a)) = M := fun M => Matrix.ext fun a b => by simp [← hp.2.1, p.π_ι]
  simp only [Place.up, GlobalTheory.FunObj.Frames.coord, frRow, frOf, hm]
  exact congrArg Matrix.transpose (frame_back _ _ _ _ x)


open Classical in
theorem model_of_vec : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {μ0 : T}, R.toLevCh.Is μ0 → LatP ch → ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ (φ : EdgeDat ch t w) j (hj : j < D.R.m) v f, IsArrVec ch t w p.e φ j hj v f → ∃ Tm₀, p.IsModel ch.W.ψ (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) Tm₀ ∧ (∀ O, IsOne O → Tm₀ O = v) ∧ ∃ Φ₀ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))) (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)), (∀ x, Φ₀.1 x = φ (.theta D.R.m j) xᵀ) ∧ Tm₀ Φ₀ = f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch μ0 hL hLat t w hw p hp φ j hj v f hv
  obtain ⟨hθ, hSB, hTA⟩ := hv
  obtain ⟨Tm, hM, hO, Φ, hΦ, hf⟩ := _root_.GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt D (Kw w) p ch.W.ψ ch.W.ψ_std _ _ _ _
    (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩).sd (node_isV ch.G hL (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩).sd
    _ _ (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) (hLat t w hw p hp j hj).1 v _ f hθ hSB hTA
  refine ⟨Tm, hM, hO, Φ, fun x => ?_, hf⟩
  rw [hΦ, if_pos (GlobalTheory.LocMod.Witness.up_half p _ _ x), coord_up ch t w p hp j hj x]

theorem weil_move : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Γ : GlobalTheory.SplitFlip.Grid k) (i j : ℕ), p.IsComp χS (Γ.kappa (.theta i j) (i, j + 1)) → p.IsComp χT (Γ.kappa (.theta i j) (i, j)) → ∀ (FS : Frame k S.rank (Fin (Γ.rank (i, j)))) (FT : Frame k T.rank (Fin (Γ.rank (i, j + 1)))) (Tm : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : Γ.VertexGroup) (ρ : GA D S) (ρ' : GA D T), p.IsLoc FS ρ (g (i, j)) → p.IsLoc FT ρ' (g (i, j + 1)) → ∀ Φ₀ : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k), ∃ Φ₁ : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k), (∀ x, Φ₁.1 x = Γ.edgeFactor .one g (.theta i j) * Φ₀.1 (((g (i, j + 1))⁻¹).val * x * (g (i, j)).val)) ∧ ω (ρ, ρ') (Tm Φ₀) = Tm Φ₁ := by
  intro D k _ _ _ _ p ψ S T χS χT ω hω Γ i j hS hT FS FT Tm hM g ρ ρ' hρ hρ' Φ₀
  refine ⟨⟨_, (SB _).smul_mem (((Γ.kappa (.theta i j) (i, j + 1) * (Γ.kappa (.theta i j) (i, j))⁻¹) (Matrix.GeneralLinearGroup.det (g (i, j))) : ℂˣ) : ℂ)
    (om_mem_SB (Γ.kappa (.theta i j) (i, j + 1))⁻¹ (g (i, j)) (g (i, j + 1)) Φ₀.2)⟩, fun x => ?_,
    GlobalTheory.LocOm.omLoc D k p ψ S T χS χT ω hω _ _ hS hT _ _ FS FT Tm hM ρ (g (i, j)) ρ' (g (i, j + 1)) hρ hρ' Φ₀ _ rfl⟩
  have e1 : ∀ (a : kˣ) (r : ℕ), ((nabs k a ^ ((r : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow a ((r : ℂ) / 2) := fun a r => by
    rw [GlobalTheory.SplitFlip.apow, Complex.ofReal_cpow (nabs_pos k a).le]; push_cast; rfl
  have e2 : ∀ (a : kˣ) (r : ℕ), ((nabs k a ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow a (-((r : ℂ) / 2)) := fun a r => by
    rw [GlobalTheory.SplitFlip.apow, Complex.ofReal_cpow (nabs_pos k a).le]; push_cast; rfl
  simp only [om, GlobalTheory.SplitFlip.Grid.edgeFactor, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, e1, e2, GlobalTheory.SplitFlip.Assignment.read,
    GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg]
  have hA := Units.ne_zero ((Γ.kappa (.theta i j) (i, j + 1)) (Matrix.GeneralLinearGroup.det (g (i, j))))
  generalize ((Γ.kappa (.theta i j) (i, j + 1)) (Matrix.GeneralLinearGroup.det (g (i, j))) : ℂ) = A at hA ⊢
  simp only [GlobalTheory.SplitFlip.Edge.src, GlobalTheory.SplitFlip.Edge.tgt, inv_inv]
  field_simp

theorem arrow_model : Big fun ch => LatP ch → ChrP ch → ArrP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  intro hLat hChr t w hw p hp φ j hj v f hv ε g hε a ρ a' ρ' hρ hρ' Z Z' _ _ _ _ σ σ'
  obtain ⟨Tm₀, hM, hO, Φ₀, hΦ₀, hf⟩ := model_of_vec ch hL hLat t w hw p hp φ j hj v f hv
  have hC := (hChr t w hw p hp).2.2 j hj
  have hωis := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  obtain ⟨Φ₁, hΦ₁, hω⟩ := weil_move D (Kw w) p ch.W.ψ _ _ _ _ (ch.W.om (.mu t D.R.m j)) hωis (locGrid ch.G t w) D.R.m j hC.1 hC.2
    _ _ Tm₀ hM (ε * g) ρ ρ' hρ hρ' Φ₀
  obtain ⟨Tm', hM', hT'⟩ := _root_.GlobalTheory.FlatPlace.exists_isModel_mvFr D (Kw w) p ch.W.ψ _ _ _ _ (ch.W.om (.mu t D.R.m j)) hωis _ _ Z' Z _ _ Tm₀ hM a a'
    (ε (D.R.m, j)) (ε (D.R.m, j + 1)) σ σ'
  refine ⟨Tm', hM', fun O hO' => ?_, ?_⟩
  · obtain ⟨Φ, hΦ, hΦO⟩ := indicator_move (Kw w) _ _ _ _ (ε (D.R.m, j)) (ε (D.R.m, j + 1)) (hε _) (hε _) σ σ' O hO'
    rw [hT' Φ O hΦO, hO Φ hΦ]
  · obtain ⟨Φ', hΦ'⟩ := exists_moved (Kw w) _ _ _ _ (ε (D.R.m, j)) (ε (D.R.m, j + 1)) σ σ' Φ₁
    refine ⟨Φ', fun z => ?_, ?_⟩
    · rw [hΦ', hΦ₁, hΦ₀, phiM]
      congr 2
      simp only [Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
    · rw [hT' Φ₁ Φ' ?_, ← hω, ← hf, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
      intro x
      rw [hΦ']
      congr 1
      rw [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.ArrowModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RowShape.LastBF

open GlobalTheory.GoodPos GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mem_completedHomLattice_iff_selfDual_source {S T : HSp D} {LS : Lat S} (LT : Lat T) (hS : IsSelfDualC S LS) (P : Pl D → Prop) (u : WO S T) :
    u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

theorem last_of_line {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} (LW : Lat W)
    (hM : IsSelfDualC V₀ M) {x : Pl D} {m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hW : ∀ t ∈ idAt D (· = x), colMul d.jY r t ∈ latA W LW (· = x) ↔
      incA D D.host.xi0 * cA D (m : AE D) * t ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [mem_completedHomLattice_iff_selfDual_source LW hM, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hW _ (Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.LocSD.hermAt_mem_idAt (hsd.1 y hy) _)),
    ← herm_conj V₀ y (((m : AE D) * a) • ratV z), int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1]
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D m * GlobalTheory.IwaPlace.hermAt V₀ y (a • ratV z)) * e3

theorem const_mem_latPi {S : HSp D} (i₀ : Fin S.rank) (I : FI D) (v : Pl D) (s : AE D) :
    (fun _ => s) ∈ latV S (latPi S I) (· = v) ↔ s ∈ idV I v := by
  constructor
  · intro hy
    have key : ∀ y ∈ latV S (latPi S I) (· = v), y i₀ ∈ idV I v := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, mem_latPi.1 hz i₀, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    exact key _ hy
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, fun _ => z, mem_latPi.2 fun _ => hz,
        funext fun i => by rw [one_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

theorem AA_mul_rowId (j τ : ℕ) (hj : j + 2 * (τ + 1) + 2 = D.R.m) (p : Fin (D.R.m - 1 - (j + 1))) (hp : p.1 = τ + 1) :
    D.host.AA * rowId D (j + 1) p = FractionalIdeal.spanSingleton _ (star (D.host.xi0 ^ τ)) * lineId D j := by
  have hodd : Odd (j + 1) := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - τ - 2, by omega⟩
  unfold rowId tiltSc lineId stairId
  rw [if_pos hodd, if_neg (by omega), show D.R.m - 1 - (j + 1) - 1 - p.1 = τ by omega,
    show D.R.m - 1 - (j + 1) - p.1 = τ + 1 by omega, show (D.R.m - 2 - j) / 2 = τ + 1 by omega, hp,
    pow_succ D.host.AA (τ + 1)]
  ring

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem last_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) (hσ : 0 < σ) :
    ∀ a ∈ idAt D (· = v),
    (rowJac G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (G.V (.grid D.R.m (j + 1)))
        (coreL G j : Set _) (rowN G (j + 1) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = τ + 1 := ⟨σ - 1, by omega⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hL : IsSelfDualC _ (lineL D j) :=
    isSelfDualC_latPi (GlobalTheory.RowShape.nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (G.Λ (.top j)) :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  have hM : IsSelfDualC _ (coreL G j) := GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL
  have ho : OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (coreL G j) (G.Λ (.top j)) (lineL D j) v := GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v (lineId D j) (lineId_ne_zero D j)
  have hx : D.host.xi0 ^ (τ + 1) ≠ 0 := pow_ne_zero _ hξ
  have hm0 : g * (D.host.xi0 ^ (τ + 1))⁻¹ ≠ 0 := mul_ne_zero hg (inv_ne_zero hx)
  have hline : ∀ a ∈ idAt D (· = v),
      a • ratV (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ∈
        latV (GlobalTheory.SeeSaw.Model.nLine D) (lineL D j) (· = v) ↔
      (((inU _ hm0)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = v) := fun a ha => by
    refine (const_mem_latPi (S := GlobalTheory.SeeSaw.Model.nLine D) (0 : Fin 1) (lineId D j) v
      (a * incA D (D.host.xi0 ^ (τ + 1)))).trans ?_
    rw [hgen, and_iff_left (Ideal.mul_mem_right _ _ ha), inU_inv, mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]
  have hU := line_norm (GlobalTheory.SeeSaw.Model.isLineVec_nLine hx) hL hline
  have hN : star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ⬝ᵥ
      (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => D.host.xi0 ^ (τ + 1)) =
      -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) := by
    rw [GlobalTheory.RowShape.nLine_gram, neg_mulVec, one_mulVec, dotProduct_neg]
    exact congrArg Neg.neg (Fin.sum_univ_one (fun _ : Fin 1 => star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)))
  rw [hN] at hU
  refine last_of_line _ _ _ hM (m := inU _ hm0) (Fin.last τ) rfl (fun t ht => ?_)
    (fun a ha => (orth_line _ ho _ a).symm.trans (hline a ha))
  have hc : colMul (rowJac G (j + 1) (by omega) (τ + 1) (by omega)).jY (Fin.last τ) t =
      fun k => t * incA D ((G.rowDec (j + 1) (by omega)).a k
        (Fin.castLE (by omega : τ + 1 ≤ D.R.m - 1 - (j + 1)) (Fin.last τ)).rev) := by
    funext k
    rfl
  have hs : star (D.host.xi0 ^ τ) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ hξ)
  rw [hc, rowN, dite_eq_left (by omega), (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2,
    AA_mul_rowId j τ hj _ (by simp only [Fin.val_rev, Fin.val_castLE, Fin.val_last]; omega),
    idV_spanSingleton_mul_iff D v _ _ hs t, and_iff_left ht, hgen, and_iff_left (Ideal.mul_mem_left _ _ ht),
    hU _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)), inU_val]
  have e : g * (D.host.xi0 ^ (τ + 1))⁻¹ * -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) *
      (g⁻¹ * (star (D.host.xi0 ^ τ))⁻¹) = D.host.xi0 := by
    rw [pow_succ D.host.xi0 τ, star_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    have := pow_ne_zero τ hξ
    field_simp
  have e' := congrArg (incA D) e
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul (incA D) g⁻¹] at e'
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D (incA D (g * (D.host.xi0 ^ (τ + 1))⁻¹)) * t) * e'

end GlobalTheory.RowShape.LastBF

theorem GlobalTheory.RowShape.big_last_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj v hσ =>
    GlobalTheory.RowShape.LastBF.last_rowN ch.G j σ hj v hσ⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000

namespace GlobalTheory.LineZero

variable {D : D7}

noncomputable def mulL {k m n : ℕ} (A : Mx D k m) : Mx D m n →+ Mx D k n where
  toFun y := A * y
  map_zero' := Matrix.mul_zero _
  map_add' y y' := Matrix.mul_add _ _ _

theorem rat_mul_mem_latO {S B T : HSp D} (M : Matrix (Fin T.rank) (Fin B.rank) D.host.E)
    {LS : Set (Fin S.rank → D.host.E)} {LB : Set (Fin B.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hM : ∀ t ∈ LB, M *ᵥ t ∈ LT) {y : WO S B} (hy : y ∈ latO S B LS LB P) :
    (rat M : Mx D T.rank B.rank) * y ∈ latO S T LS LT P := by
  suffices h : latO S B LS LB P ≤ (latO S T LS LT P).comap (mulL (rat M : Mx D T.rank B.rank)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring)

end GlobalTheory.LineZero

namespace GlobalTheory.LineZero

variable {D : D7}

theorem latO_le_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib,
      TensorProduct.tmul_neg, neg_neg]
  rw [e]
  exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩)

theorem rat_mul_mem_hatMx {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E)
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} {N' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)}
    (hA : ∀ x ∈ N, A * x ∈ N') {y : Mx D m n} (hy : y ∈ hatMx N) : (rat A : Mx D k m) * y ∈ hatMx N' := by
  suffices h : hatMx N ≤ (hatMx N').comap (mulL (rat A : Mx D k m)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, x, hx, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, A * x, hA x hx, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  rw [← TensorProduct.tmul_sum]

theorem mul_mem_smul_homLat {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') (I : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ I • homLat Λ Λ') : A * x ∈ I • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun _ _ hy hy' => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hy z hz)
  · rw [Matrix.mul_add]
    exact add_mem hy hy'

end GlobalTheory.LineZero


open GlobalTheory.LineZero in
theorem GlobalTheory.LineZero.adj_mem_lineLat : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF h u hu
  have h1 := _root_.GlobalTheory.LineAdjZero.adj_lineComp_mem_latO D hq T L μ0 hL sc G W M hM F hF h u hu
  have h2 := _root_.GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep D hq T L μ0 hL sc G W M hM F hF h u hu
  have hz : ∀ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0}, F.oz.iB *ᵥ t ∈ G.Λ (.core 0) := by
    intro t ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
    rw [Matrix.mulVec_smul, hF.zB]
    refine Submodule.smul_mem _ c ?_
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, zero_mem _, fun _ => 1, fun _ => FractionalIdeal.one_mem_one _, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct]
  show _ ∈ (latCore G 0).comap _
  rw [AddSubgroup.mem_comap]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    AddMonoidHom.inr_apply]
  rw [GlobalTheory.MixModel.OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB * _)]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_le_negSp (rat_mul_mem_latO F.oz.iB hz h1)
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx F.oz.iB (fun x hx => mul_mem_smul_homLat F.oz.iB hz _ hx) (h2 e he)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth : Big fun ch => LocP ch := by
  first | exact @GlobalTheory.FlatPlaceLoc.localization₂ | exact GlobalTheory.FlatPlaceLoc.localization₂ | (intros; apply GlobalTheory.FlatPlaceLoc.localization₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPointPrescribedLocalMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLocBig

theorem exists_hasLoc_big : Big fun ch => ∀ t (j : ℕ) (hj : j ≤ _)
    (g : ∀ w : GlobalTheory.FunObj.locPl ch.G t, GL (Fin ((GlobalTheory.FunObj.locGrid ch.G t w.1).rank (_, j))) (GlobalTheory.FunObj.Kw w.1)),
    ∃ r, HasLoc t ch.S.B hj r g :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t _ hj g =>
    GlobalTheory.RowRep.exists_hasLoc s.core.lev ch.S.B t hj g⟩⟩

end GlobalTheory.RowLocBig
end
end

