module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0017
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
theorem twisted_section_flat_valuation (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hL : Laws U x) (hFE : FlatExists U x) (Z : Comp Xo c)
    (w : Psi H → ℤ) : ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), ∀ (T : CDVR) (io : c.F →+* T.Fr)
      (y : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → evI y (idem Z) ≠ 0 → vV T.V (evI y t.sig) = 0 := by
  have hp : HasPts U Z := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
  let sF : ∀ τ, FlatSec U x Z τ := fun τ => (hFE.nonempty Z τ).some
  have hK := nonempty_keySec hL
  let s := FlatSec.shift hp sF w
  have hδ := GlobalTheory.FlatTwisting.finite_sum_flDefect (Dw := Dw) (c := c) w
  refine ⟨TwSec.ofConst s (by convert hδ) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos s) fun G hG f hf => ?_,
    fun T io y hio hZ => ?_⟩
  · have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos (w := -w) (s.symm.copy rfl rfl)
      (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
    rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
    exact h
  letI := io.toAlgebra
  have hLies : LiesOn Z y.1 := by
    by_contra hn
    exact hZ ((idem_mem_suppOn Z) T.Fr y.1 ((liesOff_iff Z y.1).2 hn))
  have hid : evI y (idem Z) = 1 := by
    have e := evI_mul y (idem Z) (idem Z)
    rw [idem_mul_idem] at e
    exact mul_left_cancel₀ hZ (by rw [mul_one]; exact e.symm)
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hsig : ∀ τ, ev (sF τ).sig ∈ unitsV T := fun τ => by
    have hn := _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt hP hP.q2 E H Dw l Xo c r U x hL Z τ
      (ArchSec.ofConst (sF τ)) T io y hio hLies
    have hev0 : evI y (sF τ).sig ≠ 0 := by
      intro h0
      rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, h0, nval_zero] at hn
      exact EReal.top_ne_zero hn
    refine ⟨hev0, ?_⟩
    rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, nval_of_ne hev0] at hn
    have : ((vV T.V (evI y (sF τ).sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    show vV T.V (evI y (sF τ).sig) = 0
    simpa using this
  have hinv : ∀ τ, ev (sF τ).inv ∈ unitsV T := fun τ => by
    have e : ev (sF τ).sig * ev (sF τ).inv = 1 := by
      rw [← map_mul, (sF τ).mul_inv]; exact hid
    have h2 : ev (sF τ).inv ≠ 0 := right_ne_zero_of_mul_eq_one e
    refine ⟨h2, ?_⟩
    have h3 := vV_mul (V := T.V) (hsig τ).1 h2
    rw [e, (hsig τ).2, zero_add, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    exact h3.symm
  have hprod : ev s.sig ∈ unitsV T := by
    rw [(FlatSec.shift_spec hp sF w).1, map_mul, map_prod]
    refine (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).prod_mem fun τ _ => ?_)
    rw [(ConstSec.zpow_spec (sF τ) (-w τ)).1, map_mul, map_mul, map_pow, map_pow]
    exact (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).mul_mem ((unitsV T).pow_mem (hsig τ) _) ((unitsV T).pow_mem (hinv τ) _))
  exact hprod.2
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityOfLocalCharts
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open Filter
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompProport
section Flag
open GlobalTheory.VarFlag
open GlobalTheory.ShFam (EigFrame FlagCpt FlagTor)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal HasToricChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end Flag
section Good
open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegCmp
open GlobalTheory.Toroidal (genBd HasToricChart)
theorem growth_eq_top_self_intersection (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    [IsIntegral (Y₀ TF.X Z)] (hd : topologicalKrullDim (Y₀ TF.X Z) = CompHt.dimFlag (T.Q.Dw j))
    {la : AllWt.Weight (T.Q.Dw j)} (hla : ∀ τ, StrictAnti (la τ)) :
    CompHt.growthOn Y.U Z (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
      ((letI := algebraΓOfHom (str₀ TF.X Z); topSelfIntersection Y.d.c₂.F (L₀ TF.X Z la) (CompHt.dimFlag (T.Q.Dw j)) : ℤ) : ℝ) := by
  have hg : genericPoint (Y₀ TF.X Z) ∉ bd₀ TF.X Z := fun h => by
    obtain ⟨y, hy⟩ := (dense_U₀ TF.X Z).nonempty
    exact h ((genericPoint_specializes y).mem_open (U₀ TF.X Z).isOpen hy)
  have hc : ∀ m : ℕ, cls (L₀ TF.X Z (m • la)) (isLB_L₀ _ _ _) = m • cls (L₀ TF.X Z la) (isLB_L₀ _ _ _) := fun m => by
    have a := cls_common_add (common₀ TF.X Z)
    induction m with
    | zero =>
      have := a 0 0
      simp only [add_zero] at this
      rw [zero_nsmul, zero_nsmul]
      exact left_eq_add.1 this
    | succ m ih => rw [succ_nsmul, succ_nsmul, ← ih]; exact a _ _
  rw [← growth_vanishing hN _ _ (str₀ TF.X Z) _ (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo).2.1 hd _ hg _
    (isLB_L₀ _ _ la) (_root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL _ _ _ _ _ _ TF Z hY.geo la (gapGe_of_strictAnti hla)) _ _ hc
    (fun m => vanBd TF.X Z (m • la)) fun _ _ => Iff.rfl, CompHt.growthOn]
  congr 1
  funext m
  have h1 := _root_.GlobalTheory.CompHS.cusp_extends_comp D T j Y e o hY hf Z TF (m • la)
  have h2 := le_antisymm h1.space_le (vanBd_le_space D T j Y e o hY hf Z TF (m • la))
  rw [CompHt.nsmul_wtOf, smul_zero, ← h2]
  exact congrArg _ h1.equiv.rank_eq
theorem growth_eq_covolume (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k (la : AllWt.Weight (T.Q.Dw j)), (∀ τ, StrictAnti (la τ)) →
        CompHt.growthOn Y.U (q k) (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
          (GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
            (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) * (CompHt.vdm la : ℤ)) := by
  obtain ⟨q, hq, h⟩ := topSelf_eq_covol hP.p16 TF hc hY.geo (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) hσ (hY.unf σ hσ)
  refine ⟨q, hq, fun k la hla => ?_⟩
  obtain ⟨_, hd, h⟩ := h k
  refine (_root_.GlobalTheory.CompProport.growth_eq_top_self_intersection hP hN hL hY hf _ TF hd hla).trans ?_
  rw [h, GlobalTheory.FlagPoly.flagDegFormula, CompHt.weylProd_eq,
    show ((CompHt.vdm la : ℤ) : ℝ) = _ from CompHt.map_vdm (Int.castRingHom ℝ) la]
  congr 1
  simp only [CompHt.dimFlag, eq_intCast]
  change GlobalTheory.TrueCx.covol ((Y.U σ).X k) * _ = _
  ring
theorem invariant_volume_eq_covolume (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    Proport Y.U ∧ ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
        (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := by
  obtain ⟨q, hq, h⟩ := _root_.GlobalTheory.CompProport.growth_eq_covolume hP hN hL hY hf TF hc hσ
  have hs : (0 : ℝ) < (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) :=
    Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt)
  have hv : ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
      (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := fun k => by
    have := GlobalTheory.TrueCx.covol_pos ((Y.U σ).X k)
    rw [CompHt.vZero, h k _ CompHt.strictAnti_stdWt, ENNReal.toReal_ofReal (by positivity), mul_div_cancel_right₀ _ hs.ne']
  refine ⟨fun Z la hla => ?_, q, hq, hv⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [h k la hla, CompHt.topDeg, hv]
theorem proportionality_of_local_charts (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) : Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  obtain ⟨h, q, -, hv⟩ := _root_.GlobalTheory.CompProport.invariant_volume_eq_covolume hP hN hL hY hf TF hc (σ := Y.d.c₂.F.val.toRingHom) rfl
  refine ⟨h, fun Z => ?_⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [hv]
  exact div_pos (mul_pos (GlobalTheory.TrueCx.covol_pos _) (by positivity)) (Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt))
end Good
end GlobalTheory.CompProport
end
end
end

