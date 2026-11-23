module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishing
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.AtReal

open Formalism.IndefR.Links

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

theorem cols_heq {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    {m : Dc.Mem} {m' : Dc'.Mem} (hm : HEq m m') :
    Dc.a m = Dc'.a m' ∧ (∀ v, HEq (Dc.Xc m v) (Dc'.Xc m' v)) ∧
      ∀ t (x : Fin (Dc.a m) → K) (x' : Fin (Dc'.a m') → K) (F : Fin (Df.nV t) → K) (F' : Fin (Df'.nV t) → K),
        HEq x x' → HEq F F' → Dc.Pt m t x F = Dc'.Pt m' t x' F' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hm
  refine ⟨rfl, fun v => HEq.rfl, fun t x x' F F' hx hF => ?_⟩
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hF
  rfl

theorem cols_mem {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    (m : Dc.Mem) : ∃ m' : Dc'.Mem, HEq m m' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  exact ⟨m, HEq.rfl⟩

end Gen

theorem heq_fin {α : Type} {n n' : ℕ} (h : n = n') (x : Fin n → α) : ∃ x' : Fin n' → α, HEq x x' := by
  subst h; exact ⟨x, HEq.rfl⟩

theorem heq_fin' {α : Type} {n n' : ℕ} (h : n = n') (x' : Fin n' → α) : ∃ x : Fin n → α, HEq x x' := by
  subst h; exact ⟨x', HEq.rfl⟩

theorem heq_mat {n n' : ℕ} (h : n = n') (M' : Matrix (Fin n') (Fin n') ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, HEq M M' := by
  subst h; exact ⟨M', HEq.rfl⟩

theorem heq_mulVec {n n' : ℕ} (h : n = n') {M : Matrix (Fin n) (Fin n) ℂ} {M' : Matrix (Fin n') (Fin n') ℂ}
    (hM : HEq M M') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : HEq (M.mulVec x) (M'.mulVec x') := by
  subst h; obtain rfl := eq_of_heq hM; obtain rfl := eq_of_heq hx; rfl

theorem heq_fnorm {n n' : ℕ} (h : n = n') {Y : Matrix (Fin n) (Fin n) ℂ} {Y' : Matrix (Fin n') (Fin n') ℂ}
    (hY : HEq Y Y') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : fnorm Y x = fnorm Y' x' := by
  subst h; obtain rfl := eq_of_heq hY; obtain rfl := eq_of_heq hx; rfl

theorem heq_cpt {K : Type} [Field K] (σ : K →+* ℂ) {n n' : ℕ} (h : n = n') {x : Fin n → K} {x' : Fin n' → K}
    (hx : HEq x x') : HEq (cpt σ x) (cpt σ x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem heq_cjv (s : Bool) {n n' : ℕ} (h : n = n') {x : Fin n → ℂ} {x' : Fin n' → ℂ}
    (hx : HEq x x') : HEq (Formalism.L2.SG.JoinSI.cjv s x) (Formalism.L2.SG.JoinSI.cjv s x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop.AtReal

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop

open Formalism.IndefR.Links GlobalTheory.MiTop.AtReal


end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaValueEdgeSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.ChainChar

theorem char_of_red {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+ k) {s κ r : ℕ} (hr : r = κ + (s + 1))
    (S : GlobalTheory.SymChain.SymData k s κ) (x : S.P.J) (g : GL (Fin r) (O ⧸ I))
    (hx : ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1)
    (z : O) (hz : Ideal.Quotient.mk I z = edgeSum (GlobalTheory.chainEdge κ) g) :
    ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * π z) : ℂ) := by
  subst hr
  set X := (x : GL (Fin κ ⊕ Fin (s + 1)) k).val with hX
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have h1 : ∀ a b, valuation k (X a b - π (l a b)) < 1 := fun a b => hx a b _ _ (he a) (he b) _ (hl a b)
  have hI : ∀ p ∈ I, valuation k (π p) < 1 := by
    intro p hp
    have h2 := hx (.inr 0) (.inr 0) _ _ (he _) (he _) (l (.inr 0) (.inr 0) + p)
      (by rw [map_add (f := _), hl, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero])
    have h3 := (valuation k).map_sub_lt (h1 (.inr 0) (.inr 0)) h2
    rwa [map_add, sub_sub_sub_cancel_left, add_sub_cancel_left] at h3
  let w : O := ∑ a, ∑ b, if GlobalTheory.chainEdge κ (e a) (e b) then l a b else 0
  let t : k := ∑ a, ∑ b, if GlobalTheory.chainEdge κ (e a) (e b) then X a b else 0
  have hw : w - z ∈ I := by
    rw [← Ideal.Quotient.eq, hz, edgeSum, ← e.sum_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact hl a b
    · exact map_zero _
  have htw : valuation k (t - π w) < 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t, w, map_sum, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun a _ => (valuation k).map_sum_lt one_ne_zero fun b _ => ?_
    split_ifs
    · exact h1 a b
    · simp
  have htz : valuation k (t - π z) < 1 := by
    have h4 := (valuation k).map_add_lt htw (hI _ hw)
    rwa [map_sub, sub_add_sub_cancel] at h4
  have ht : t = GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k) + GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val X.toBlocks₁₁ := by
    simp only [t, Fintype.sum_sum_type, Finset.sum_add_distrib, GlobalTheory.RootEx.simpleSum, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum,
      GlobalTheory.chainEdge, he, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr]
    have e1 : ∀ (a : Fin κ) (b : Fin (s + 1)), ¬ (κ + b.val = a.val + 1 ∧ a.val + 1 ≠ κ) := fun a b => by
      have := a.2; omega
    have e2 : ∀ (a : Fin (s + 1)) (b : Fin κ), ¬ (b.val = κ + a.val + 1 ∧ κ + a.val + 1 ≠ κ) := fun a b => by
      have := b.2; omega
    have e3 : ∀ (a b : Fin κ), (b.val = a.val + 1 ∧ a.val + 1 ≠ κ) ↔ b.val = a.val + 1 := fun a b => by
      have := b.2; omega
    have e4 : ∀ (a b : Fin (s + 1)), (κ + b.val = κ + a.val + 1 ∧ κ + a.val + 1 ≠ κ) ↔ b.val = a.val + 1 := fun a b => by
      omega
    simp only [e1, e2, e3, e4, if_false, Finset.sum_const_zero, add_zero, zero_add]
    rw [add_comm]
    rfl
  have hone : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * (t - π z)) = 1 := by
    refine (S.cond _).2 ?_ _ le_rfl
    have h5 := (S.unif _).1 htz
    have h6 : valuation k (((S.ϖ⁻¹ : kˣ) : k) * (S.ϖ : k)) = valuation k ((1 : kˣ) : k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  rw [S.sym.2 x, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add, ← ht]
  congr 1
  rw [← mul_one (S.ψ (_ * π z)), ← hone, ← AddChar.map_add_eq_mul, ← mul_add, add_sub_cancel]

end GlobalTheory.ChainChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastBiTheta

variable {D : D7}

theorem sOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem sOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem sOH_resS_symm {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) (a a' : WO A S) (b b' : WO L S) :
    symplOH V₀ S ((o.resS S).symm (a, b)) ((o.resS S).symm (a', b')) = symplOH A S a a' + symplOH L S b b' := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem quasi_of_mem {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    {x : WO S T} (hx : x ∈ ratMx D T.rank S.rank) (w : WO S T) : f (x + w) = ψ (-(symplOH S T x w)) * f w := by
  obtain ⟨γ, rfl⟩ := hx
  exact h.quasi γ w

theorem resS_symm_mem {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : a ∈ ratMx D S.rank A.rank) (hb : b ∈ ratMx D S.rank L.rank) :
    (o.resS S).symm (a, b) ∈ ratMx D S.rank V₀.rank := by
  rw [OrthDec.resS_symm_apply]
  exact add_mem (ratMx_mul ha (rat_mem _)) (ratMx_mul hb (rat_mem _))

theorem resS_symm_map {B : Type} [CommRing B] (φ : AE D →+* B) {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D)
    {a : WO A S} {b : WO L S} (ha : a.map φ = 0) (hb : b.map φ = 0) : ((o.resS S).symm (a, b)).map φ = 0 := by
  rw [OrthDec.resS_symm_apply, Matrix.map_add φ (map_add φ), map_mul_eq_zero_left φ ha, map_mul_eq_zero_left φ hb,
    add_zero]


set_option maxHeartbeats 1000000 in
theorem isBiTheta_lastBi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  intro D ψ _ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ hΦ
  obtain ⟨kadd, kcont, krat, -, ksympl, kpart⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  have hC : ∀ u v, lastBi o o'' τ Ξ Φ₂ u v =
      Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := fun _ _ => rfl
  let K : WO S L'' →+ WO L S := AddMonoidHom.mk' (kap τ S) kadd
  let P1 : WO S X →+ WO S T := (AddMonoidHom.fst _ _).comp (o''.resT S).toAddMonoidHom
  let P2 : WO S X →+ WO S L'' := (AddMonoidHom.snd _ _).comp (o''.resT S).toAddMonoidHom
  have cP1 : Continuous fun b : WO S X => (o''.resT S b).1 := continuous_fst.comp (o''.continuous_resT S)
  have cP2 : Continuous fun b : WO S X => (o''.resT S b).2 := continuous_snd.comp (o''.continuous_resT S)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show Continuous fun p : WO A S × WO S X =>
      Φ₂ (o''.resT S p.2).1 * Ξ ((o.resS S).symm (p.1, kap τ S (o''.resT S p.2).2))
    exact (hΦ.cont.comp (cP1.comp continuous_snd)).mul
      (hΞ.cont.comp ((o.continuous_resS_symm S).comp (continuous_fst.prodMk (kcont.comp (cP2.comp continuous_snd)))))
  ·
    intro n L₁ L₂ hL₁ hL₂ hf₁ hf₂ u v
    let M₁ : (Fin n → ℝ) →+ WO S T := P1.comp L₂
    let M₂ : (Fin n → ℝ) →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.prod L₁ (K.comp (P2.comp L₂)))
    have cM₁ : Continuous M₁ := cP1.comp hL₂
    have cM₂ : Continuous M₂ := (o.continuous_resS_symm S).comp (hL₁.prodMk (kcont.comp (cP2.comp hL₂)))
    have fM₁ : ∀ t, (M₁ t).map (finPart D) = 0 := fun t => map_mul_eq_zero_right (finPart D) _ (hf₂ t)
    have fM₂ : ∀ t, (M₂ t).map (finPart D) = 0 := fun t =>
      resS_symm_map (finPart D) o S (hf₁ t) ((kpart _).2 (map_mul_eq_zero_right (finPart D) _ (hf₂ t)))
    have e : (fun t => lastBi o o'' τ Ξ Φ₂ (u + L₁ t) (v + L₂ t)) = fun t =>
        Φ₂ ((o''.resT S v).1 + M₁ t) * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + M₂ t) := by
      funext t
      rw [hC]
      show Φ₂ (o''.resT S (v + L₂ t)).1 * Ξ ((o.resS S).symm (u + L₁ t, kap τ S (o''.resT S (v + L₂ t)).2)) =
        Φ₂ ((o''.resT S v).1 + (o''.resT S (L₂ t)).1) *
          Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (L₁ t, kap τ S (o''.resT S (L₂ t)).2))
      rw [map_add (f := _), Prod.fst_add, Prod.snd_add, kadd, ← map_add (f := _), Prod.mk_add_mk]
    rw [e]
    exact (hΦ.smooth n M₁ cM₁ fM₁ _).mul (hΞ.smooth n M₂ cM₂ fM₂ _)
  ·
    intro γ u v
    rw [hC, hC]
    have e : (o.resS S).symm (ratW S A γ + u, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (ratW S A γ, 0) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, zero_add]
    have hγ : ratW S A γ ∈ ratMx D S.rank A.rank := rat_mem γ
    rw [e, quasi_of_mem hΞ (resS_symm_mem o S hγ (zero_mem _)), sOH_resS_symm, sOH_zero_left, add_zero]
    ring
  ·
    intro γ u v
    rw [hC, hC]
    have h1 : (o''.resT S (ratW X S γ)).1 ∈ ratMx D T.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have h2 : (o''.resT S (ratW X S γ)).2 ∈ ratMx D L''.rank S.rank := ratMx_mul (rat_mem _) (rat_mem γ)
    have e : (o.resS S).symm (u, kap τ S ((o''.resT S (ratW X S γ)).2 + (o''.resT S v).2)) =
        (o.resS S).symm (0, kap τ S (o''.resT S (ratW X S γ)).2) + (o.resS S).symm (u, kap τ S (o''.resT S v).2) := by
      rw [kadd, ← map_add (f := _), Prod.mk_add_mk, zero_add]
    have ph : ψ (-symplOH S X (ratW X S γ) v) = ψ (-symplOH S T (o''.resT S (ratW X S γ)).1 (o''.resT S v).1) *
        ψ (-symplOH S L'' (o''.resT S (ratW X S γ)).2 (o''.resT S v).2) := by
      rw [← AddChar.map_add_eq_mul, o''.symplOH_resT S (ratW X S γ) v]
      exact congrArg ψ (neg_add _ _)
    rw [map_add (f := _), Prod.fst_add, Prod.snd_add, e, quasi_of_mem hΦ h1,
      quasi_of_mem hΞ (resS_symm_mem o S (zero_mem _) (krat _ h2)), sOH_resS_symm, sOH_zero_left, zero_add, kH, ph]
    ring
  ·
    obtain ⟨U, hUo, hU⟩ := hΞ.level
    let iA : WO A S →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
    have ciA : Continuous fun a : WO A S => (o.resS S).symm (a, 0) :=
      (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
    refine ⟨U.comap iA, hUo.preimage ciA, fun a ha hinf v => ?_⟩
    funext u
    have h1 := congrFun (hU (iA a) ha (resS_symm_map (infPart D) o S hinf (by simp)))
      ((o.resS S).symm (u, kap τ S (o''.resT S v).2))
    have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
        (o.resS S).symm (u, kap τ S (o''.resT S v).2) + iA a := by
      show _ = _ + (o.resS S).symm (a, 0)
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) (iA a) = symplOH A S u a := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (a, 0)) = _
      rw [sOH_resS_symm, sOH_zero_right, add_zero]
    simp only [heisO] at h1 ⊢
    rw [ph] at h1
    rw [hC, hC, e, ← h1]
    ring
  ·
    obtain ⟨UΞ, hUΞo, hUΞ⟩ := hΞ.level
    obtain ⟨UΦ, hUΦo, hUΦ⟩ := hΦ.level
    let jL : WO S X →+ WO V₀ S := (o.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (K.comp P2))
    have cjL : Continuous fun b : WO S X => (o.resS S).symm (0, kap τ S (o''.resT S b).2) :=
      (o.continuous_resS_symm S).comp (continuous_const.prodMk (kcont.comp cP2))
    refine ⟨UΦ.comap P1 ⊓ UΞ.comap jL, (hUΦo.preimage cP1).inter (hUΞo.preimage cjL), fun b hb hinf u => ?_⟩
    have hT : (o''.resT S b).1.map (infPart D) = 0 := map_mul_eq_zero_right (infPart D) _ hinf
    have hJ : (jL b).map (infPart D) = 0 :=
      resS_symm_map (infPart D) o S (by simp) ((kpart _).1 (map_mul_eq_zero_right (infPart D) _ hinf))
    show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) =
      o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))
    rw [o''.heisO_boxT, hUΦ (o''.resT S b).1 hb.1 hT]
    congr 1
    funext w
    have h2 := congrFun (hUΞ (jL b) hb.2 hJ) ((o.resS S).symm (u, kap τ S w))
    have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) = (o.resS S).symm (u, kap τ S w) + jL b := by
      show _ = _ + (o.resS S).symm (0, kap τ S (o''.resT S b).2)
      rw [kadd, ← map_add (f := _), Prod.mk_add_mk, add_zero]
    have ph : symplOH V₀ S ((o.resS S).symm (u, kap τ S w)) (jL b) = symplOH S L'' w (o''.resT S b).2 := by
      show symplOH V₀ S ((o.resS S).symm (u, _)) ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) = _
      rw [sOH_resS_symm, sOH_zero_right, zero_add, kH]
    simp only [heisO] at h2 ⊢
    rw [ph] at h2
    rw [e]
    exact h2

end GlobalTheory.LastBiTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_trivial_near_one_of_local_bad_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Vs : Set (HeightOneSpectrum (𝓞 F))), Vs.Finite → (∀ v ∈ bad, v ∈ Vs) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ v ∈ Vs, ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) := by
  first | exact @GlobalTheory.ChiCont.main | exact GlobalTheory.ChiCont.main | (intros; apply GlobalTheory.ChiCont.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixProjEqOneOfSuppAtDistinctFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OtherPlace

theorem pr_placeIdem_other {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (hv : q.v ≠ q'.v) :
    q.pr (q'.e + cA D q'.e) = 0 := by
  obtain ⟨ε, hε, hqe⟩ := q.above
  obtain ⟨ε', hε', hqe'⟩ := q'.above
  have hpr : ∀ x, q.pr x = q.pr (q.e * x) := fun x => by rw [← q.sec_pr, q.pr_sec]
  have he : q.e = q.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hqe, mul_add, q.split.1, q.split.2.1, add_zero]
  have hεε : ε * ε' = 0 := by
    rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε, GlobalTheory.SplitCut.eFin_of_placeIdem hε']
    exact GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ hv
  rw [hqe', hpr, he, mul_assoc, ← map_mul, hεε, map_zero, mul_zero, map_zero]

theorem mt_map_pr_eq_one : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k)
    (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V), q.v ≠ q'.v → SuppAt q'.e V g → (mt V g).map q.pr = 1 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' V g hv hs
  have h0 := pr_placeIdem_other q q' hv
  ext i j
  have h1 := congrArg q.pr (hs i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, ← sub_eq_zero, ← h1.symm]
  have : q.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [this]

end GlobalTheory.OtherPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppGrp

open GlobalTheory.FinPl

theorem placeIdem_mem_idAt {D : D7} {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (P : Pl D → Prop) (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h2⟩ := h
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · exact TensorProduct.zero_tmul _ (1 : D.host.E)
  · have hu : u.1 ≠ v := fun e => u.2 (e ▸ hP)
    show (evalV D.host.F u.1 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h2 u.1 hu, TensorProduct.zero_tmul]

theorem mem_congGrp {D : D7} (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (h : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  rw [congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have h1 := h i j
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
  have : Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this] at h1
  exact h1

theorem mem_grpAt_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  intro D k _ _ _ _ q V g hg P hP
  obtain ⟨ε, h1, h2⟩ := q.above
  refine mem_congGrp V _ g fun i j => ?_
  have h3 := hg i j
  rw [h2] at h3
  rw [← h3]
  exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt h1 P hP)

end GlobalTheory.SuppGrp
end

