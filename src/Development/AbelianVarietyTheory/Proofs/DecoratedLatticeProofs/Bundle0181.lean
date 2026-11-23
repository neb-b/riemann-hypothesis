module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CayleyRuleOfBiInvariantVacuumCoefficient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CayleyVac

theorem exists_cartanU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {n : ℕ} (g : GU σ n) :
    ∃ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧
      ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_good_div L ϖ σ q n hU g
  obtain ⟨t, ht, -⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i : Fin n => ϖ ^ d.getD i.1 0) (fun i => by
      have hϖ : ϖ ≠ 0 := by
        intro h
        have hv := hU.2.2.2.1
        rw [h, Valuation.map_zero] at hv
        exact absurd hv WithZero.zero_ne_coe
      rw [map_zpow₀, hU.2.2.1, GlobalTheory.InertThetaCompare.Good.rev hd,
        ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero])
  refine ⟨fun i => d.getD i.1 0, t, ht, ?_⟩
  refine GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL L ϖ σ q n hU t g a b ha hb ?_
  apply Units.ext
  simp only [Units.val_mul]
  rw [e, ht]

end GlobalTheory.ChainOnto.CayleyVac

namespace GlobalTheory.ChainOnto.CayleyVac

theorem cayley_of_coeff {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {M : Type} [AddCommGroup M] [Module ℂ M]
    {α β : Type} (ρ : Matrix α β L → Module.End ℂ M) {r N : ℕ} (π : GU σ r →* Module.End ℂ M) (s : M)
    (l : M →ₗ[ℂ] ℂ) (hls : l s ≠ 0)
    (hco : ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L α β, ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s)
    (φ : GU σ r → ℂ) (hφ : KerU ϖ q N ((-1) ^ N) φ) (hl : ∀ g, l (π g s) = φ g * l s) :
    CayleyRule q N ρ π s := by
  intro e he g hdet hint
  have h1 := hco e he (π g⁻¹ s)
  rw [hl] at h1
  have h2 : e (π g⁻¹ s) = φ g⁻¹ * e s := mul_right_cancel₀ hls (by rw [h1]; ring)
  rw [h2]
  congr 1
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, hg⟩ := exists_cartanU hU g⁻¹
  have hord := _root_.GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int L ϖ σ q hU r g t d ht k₁ hk₁ k₂ hk₂ hg hdet hint
  rw [hg, hφ d t ht k₁ hk₁ k₂ hk₂, hord, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  push_cast
  rw [_root_.mul_inv, ← _root_.inv_pow, ← _root_.inv_pow, _root_.inv_neg_one]

end GlobalTheory.ChainOnto.CayleyVac


open GlobalTheory.ChainOnto.CayleyVac in
theorem GlobalTheory.ChainOnto.cayleyRule_of_vacCoeff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l : M →ₗ[ℂ] ℂ, l s ≠ 0 → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ φ : GU σ n → ℂ, KerU ϖ q n' ((-1) ^ n') φ → (∀ g, l (ω (g, 1) s) = φ g * l s) → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s) ∧ ∀ φ : GU σ n' → ℂ, KerU ϖ q n ((-1) ^ n) φ → (∀ g, l (ω (1, g) s) = φ g * l s) → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hs l hls hl
  have hU : IsUnramInv ϖ σ q := hs.1.unr
  have hco : ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s :=
    fun e he => _root_.GlobalTheory.ChainOnto.heisInv_forms_proportional L ϖ σ q δ ψ n n' M ρ ω s hs l e hl he
  refine ⟨fun φ hφ hc => cayley_of_coeff hU ρ _ s l hls hco φ hφ ?_, fun φ hφ hc => cayley_of_coeff hU ρ _ s l hls hco φ hφ ?_⟩
  · intro g; simpa using hc g
  · intro g; simpa using hc g

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem prod_diagonal_block_dets_eq_lower_block_det {κ : Type} [CommRing κ] {r t j n : ℕ} (hn : n = r + j * t) {g : GL (Fin n) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    ∏ c ∈ Finset.range j, dBlk (blkOf r t) (c + 1) g = dBlk (blk2 r) 1 g := by
  classical
  have hg2 : g ∈ blockTri (blk2 r) := blockTri_blkOf_le r t hg
  set M : Matrix (Fin n) (Fin n) κ := (g : Matrix (Fin n) (Fin n) κ) with hM
  have sq : ∀ (b : Fin n → ℕ) (c : ℕ), g ∈ blockTri b → ((dBlk b c g : κˣ) : κ) = (M.toSquareBlock b c).det := by
    intro b c h; rw [diag_block_det_val c h]; rfl
  have emp : ∀ (b : Fin n → ℕ) (c : ℕ), c ∉ Finset.univ.image b → (M.toSquareBlock b c).det = 1 := by
    intro b c hc
    haveI : IsEmpty {a : Fin n // b a = c} := ⟨fun a => hc (Finset.mem_image.2 ⟨a.1, Finset.mem_univ _, a.2⟩)⟩
    exact Matrix.det_isEmpty
  have hdet : ∀ (b : Fin n → ℕ) (N : ℕ), (∀ a, b a < N) → M.BlockTriangular b →
      M.det = ∏ c ∈ Finset.range N, (M.toSquareBlock b c).det := by
    intro b N hb hB
    rw [hB.det]
    refine Finset.prod_subset (fun c hc => ?_) (fun c _ hc => emp b c hc)
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2 (hb a)
  have h1 := hdet (blkOf r t) (j + 1) (fun a => by
      unfold blkOf
      split_ifs with h
      · omega
      · have ha : a.val - r < j * t := by have := a.2; omega
        have ht : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · simp [h0] at ha
          · exact h0
        have : (a.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ha)
        omega) hg
  have h2 := hdet (blk2 r) 2 (fun a => by unfold blk2; split_ifs <;> omega) hg2
  rw [Finset.prod_range_succ'] at h1
  rw [Finset.prod_range_succ', Finset.prod_range_one] at h2
  have h0 : (M.toSquareBlock (blkOf r t) 0).det = (M.toSquareBlock (blk2 r) 0).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (p := fun a : Fin n => blk2 r a = 0)
      (q := fun a : Fin n => blkOf r t a = 0) (fun a => by unfold blk2 blkOf; split_ifs <;> simp_all))]
    rfl
  have hu : IsUnit (M.toSquareBlock (blk2 r) 0).det := by rw [← sq _ 0 hg2]; exact Units.isUnit _
  apply Units.ext
  rw [Units.coe_prod, sq _ 1 hg2]
  rw [Finset.prod_congr rfl (fun c _ => sq _ (c + 1) hg)]
  rw [h0] at h1
  exact hu.mul_right_cancel (h1.symm.trans h2)

end GlobalTheory.FlatLevel

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem multT_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : MultT θ M J χ ≤ MultT θ M J' χ' :=
  Submodule.map_mono (Submodule.span_mono fun X hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩)


open Classical in
theorem lev_flat_le (c : Com D) (w : Twist D) (hw : w.Is c) (j : ℕ) {n : ℕ} (hn : n = D.R.r + j * D.R.t)
    (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D)) (hr hr' : D.R.r ≤ n)
    (x : GL (Fin n) (Lev.EAf D))
    (hx : x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B)) :
    x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) ∧
      levFn β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x =
        levFn β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x := by
  obtain ⟨hp, hP⟩ := mem_lev.1 hx
  obtain ⟨hUA, hSt, h3, -⟩ := mem_parLev.1 hp
  have h3' : ∀ PP ∈ c.Pg, redFn β PP x ∈ blockTri (blkOf D.R.r D.R.t) := h3
  have hP' : (fun PP : c.Pg => upperLeftBlock hr (redFn β PP.1 x)) ∈ c.P.H := hP
  have hone := (hw.grp _).1 hP'
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  refine ⟨mem_lev.2 ⟨mem_parLev.2 ⟨hUA, hSt, fun PP h => h3' PP (hPg PP h),
    fun PP h => blockTri_blkOf_le _ _ (h3' PP (hQ PP h))⟩, ?_⟩, ?_⟩
  · show _ ∈ (⊥ : Subgroup (G0 w.Pg D.R.r))
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    exact hone ⟨PP.1, hPg PP.1 PP.2⟩ PP.2
  · unfold levFn
    have e1 : ext1 (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 c.P.H c.P.chi _ = 1
      unfold ext1
      split_ifs
      · rw [hw.chr]; rfl
      · rfl
    have e2 : ext1 (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 (LevelP.triv w.Pg D.R.r ℂ).H (LevelP.triv w.Pg D.R.r ℂ).chi _ = 1
      unfold ext1
      split_ifs
      · rfl
      · rfl
    rw [e1, e2]
    show 1 * (∏ PP ∈ c.Pg, ∏ c' ∈ Finset.range j, c.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ (∅ : Finset (Pl D.host.E)), (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x)) =
      1 * (∏ PP ∈ w.Pg, ∏ c' ∈ Finset.range j, w.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ w.Q, (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x))
    rw [Finset.prod_empty, mul_one, one_mul, one_mul, hw.union, Finset.prod_union hw.disj]
    congr 1
    · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c' _ => ?_
      rw [hw.chiPg (c' + 1) PP hP]
    · refine Finset.prod_congr rfl fun PP hP => ?_
      simp_rw [hw.chiQ _ PP hP]
      rw [← map_prod, prod_diagonal_block_dets_eq_lower_block_det hn (h3' PP (hQ PP hP))]


open Classical in
theorem flatLe : ∀ D : D7, FlatLe D := by
  intro D c w hw j _ s hs hr
  obtain ⟨hr', hL, hflat⟩ := hs
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  show MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) ≤
    MultT c.θ s.M (levS s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
      (Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
  rw [hL]
  refine multT_le c.θ s.M fun k hk => ?_
  obtain ⟨h1, h2⟩ := lev_flat_le c w hw j hn s.V.gram s.β hr hr' _ hk.2
  exact ⟨⟨hk.1, h1⟩, (congrArg (fun u : ℂˣ => (u : ℂ)) h2).symm⟩

end GlobalTheory.FlatLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem upVal_of_span_adj : ∀ D : D7, SoftQ D → UpSpanQ D → UpAdjQ D → UpVal D := by
  intro D hSoft hSpan hAdj
  intro hgap c tw htw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ v hv
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := (hSoft c tw htw (k + 1) hk' s' hs').1
  have hl : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → ∀ (y : s'.CC c), ∀ w ∈ s'.KF,
      s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = ip' y x * ipD (p.It φ w) v := by
    intro u x hx y w hw
    rw [hx y]
    exact (hAdj hgap c tw htw k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)
  have key : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → p.up φ (PiLocalization₂.val u v) ≠ 0 →
      x ≠ 0 ∧ ∃ w₁, IsAdjVec p ipD ipD' φ v w₁ ∧ p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := by
    intro u x hx hF
    obtain ⟨hx0, w₁, hw₁, hFx⟩ := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c)
      (s'.CC c).subtype s'.KF ipD' ip' s'.pet hM'.hermD hM'.posD hM'.herm hM'.pos
      (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v)
      (hSpan hgap c tw htw k hk s s' hs hs' p hp u φ v hv) (hl u x hx) hF
    have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := hFx
    refine ⟨hx0, w₁, ⟨hw₁, fun w hw => ?_⟩, hFx'⟩
    have h1 := hl u x hx x w hw
    rw [hFx'] at h1
    have h2 := (hM'.schur x x w w₁).symm.trans h1
    have hxx : ip' x x ≠ 0 := fun h => by
      have := hM'.pos x hx0
      rw [h] at this
      simp at this
    exact mul_left_cancel₀ hxx h2
  refine ⟨fun ⟨u, hF⟩ => ?_, fun w₀ hw₀ u x hx => ?_⟩
  · obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
    obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
    refine ⟨w₁, fun h => hF ?_, hw₁⟩
    rw [hFx, h]
    simp
  · by_cases hF : p.up φ (PiLocalization₂.val u v) = 0
    · have h1 := hl u x hx x w₀ hw₀.1
      rw [hF, ← hw₀.2 w₀ hw₀.1] at h1
      have h0 : s'.pet (PiLocalization₂.val x w₀) (0 : GA D s'.V → ℂ) = 0 := by
        simp [PiLocalization₂.pet, Lift.pet]
      rw [h0] at h1
      rw [hF]
      rcases mul_eq_zero.mp h1.symm with h | h
      · have hx0 : x = 0 := by
          by_contra hne
          have := hM'.pos x hne
          rw [h] at this
          simp at this
        subst hx0
        first | rfl | simp [PiLocalization₂.val]
      · have hw0 : w₀ = 0 := by
          by_contra hne
          have := hM'.posD w₀ hne
          rw [h] at this
          simp at this
        subst hw0
        simp
    · obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
      have hd : w₁ = w₀ := by
        by_contra hne
        have hdK : w₁ - w₀ ∈ s'.KF := s'.KF.sub_mem hw₁.1 hw₀.1
        have hz : ipD' (w₁ - w₀) (w₁ - w₀) = 0 := by
          rw [map_sub, hw₁.2 _ hdK, hw₀.2 _ hdK, sub_self]
        have := hM'.posD _ (sub_ne_zero.mpr hne)
        rw [hz] at this
        simp at this
      rw [hFx, hd]

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem upAdjQ_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdjQ D := by
  intro hP D _ c w hw k _ s s' hs hs' p hp u y φ v _ w' _
  obtain ⟨hr, -, hfl⟩ := hs
  obtain ⟨hr', -, hfl'⟩ := hs'
  have hc : c.Is := hw.com
  have hF := _root_.GlobalTheory.ChainOnto.ThetaSwap.integral_swap D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hc.inf hp.weil (p.pt φ) (hp.theta φ)
    s.ν s.fd s'.ν s'.fd hfl.haar hfl.fund hfl'.haar hfl'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w')
    (rapidDec_val hP hc u v) (rapidDec_val hP hc y w')
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w' h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w' h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w' h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w') g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w' g

end GlobalTheory.ChainTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Inhab

variable {D : D7}

theorem nonempty_vol (V : HSp D) : Nonempty (Vol V) :=
  let ⟨μ, 𝓕, h1, h2⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  ⟨⟨μ, 𝓕, h1, h2⟩⟩

theorem nonempty_volN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem coCpt_of_mul {V : HSp D} (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso {V : HSp D} (h : IsAniso V) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h)

theorem coCpt_of_posDef {V : HSp D} (h : ∀ τ, (gramAt D V τ).PosDef) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)

theorem exists_weil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {χS χT : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χT) (h3 : ResEta D χS S.rank) (h4 : ResEta D χT T.rank) :
    ∃ om, IsWeilDatumO ψ S T χS χT om :=
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) h1 h2 h3 h4

theorem nonempty_step {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) : Nonempty (Step ψ V V₀ W W₀ ρ σ) := by
  obtain ⟨χV, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D V.rank
  obtain ⟨χW, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D W.rank
  obtain ⟨om, h⟩ := exists_weil hψ V W a1 b1 a2 b2
  obtain ⟨om₀, h₀⟩ := exists_weil hψ V₀ W₀ a1 b1 (resEta_parity a2 hV) (resEta_parity b2 hW)
  obtain ⟨vW⟩ := nonempty_vol W
  obtain ⟨vS⟩ := nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩⟩

theorem even_im_hermitian_sub {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : S.rank % 2 = S₀.rank % 2 := by
  have := d.rank_add
  omega

theorem nonempty_stepBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) :
    Nonempty (StepBF ψ B J) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub B.d) (even_im_hermitian_sub J.d)

theorem nonempty_stepFB {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (J : JacLev D (σ + 1))
    (B : BesLev D σ) : Nonempty (StepFB ψ J B) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub J.d) (even_im_hermitian_sub B.d)

theorem cmHost_imaginaryGenerator_ne_zero (D : D7) : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

end GlobalTheory.Unf.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_agrees_row_subgroup_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.VolBridge.vol_agree | exact GlobalTheory.VolBridge.vol_agree | (intros; apply GlobalTheory.VolBridge.vol_agree <;> assumption)
end

