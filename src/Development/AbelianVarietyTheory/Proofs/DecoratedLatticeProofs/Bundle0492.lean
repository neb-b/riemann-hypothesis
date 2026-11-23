module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditions
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCores
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.CoreHomothety

variable {D : D7}

theorem mulVec_mem_idAt {P : GlobalTheory.FinPl.Pl D → Prop} {m l : ℕ} (X : Matrix (Fin m) (Fin l) (AE D))
    {y : Fin l → AE D} (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (X *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have h1 := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  have h2 : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel, mt_one,
      Matrix.one_mulVec]
  rw [h2] at h1
  exact h1.symm

theorem moves_trans {S : HSp D} {g h : GA D S} {L M N : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h1 : Moves S g L M P)
    (h2 : Moves S h M N P) : Moves S (h * g) L N P := by
  intro y hy
  rw [h1 y hy, h2 _ (mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec]
  rfl

theorem moves_conj {S : HSp D} {h : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (hM : Moves S h L M P)
    (a : GA D S) : Moves S (h * a * h⁻¹) M M P ↔ Moves S a L L P := by
  constructor
  · intro H
    have e : h⁻¹ * (h * a * h⁻¹ * h) = a := by group
    have := moves_trans (moves_trans hM H) (moves_inv hM)
    rwa [e] at this
  · intro H
    have := moves_trans (moves_trans (moves_inv hM) H) hM
    rwa [← mul_assoc] at this

theorem sMoves_trans {S : HSp D} {c : AE D} {g h : GA D S} {L M N : Lat S} {v : GlobalTheory.FinPl.Pl D}
    (hS : SMoves S c g L M v) (hM : Moves S h M N (· = v)) : SMoves S c (h * g) L N v := by
  intro y hy
  rw [hS y hy, hM (c • (mt S g *ᵥ y)) (fun i => Ideal.mul_mem_left _ c (mulVec_mem_idAt _ hy i)),
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_gluedS_smul (q : GlobalTheory.LatPair.Unif k) {P P' : GlobalTheory.LatPair.Pair k n} {g : GL n k} {s : k} (hs : s ≠ 0)
    (hg : g.val = s • (1 : Matrix n n k)) (hP : P' = g • P) (u : n → k) (t : Fin 1 → k) :
    Sum.elim u t ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec ↔ Sum.elim (s • u) t ∈ GlobalTheory.LatPair.gluedS q 1 P'.ker P'.vec := by
  have hgx : ∀ x : n → k, g • x = s • x := fun x => by
    show g.val *ᵥ x = s • x
    rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hgi : ∀ x : n → k, g⁻¹ • x = s⁻¹ • x := fun x => by
    have : x = g • (s⁻¹ • x) := by rw [hgx, smul_smul, mul_inv_cancel₀ hs, one_smul]
    conv_lhs => rw [this]
    rw [inv_smul_smul]
  have hker : ∀ x : n → k, x ∈ P'.ker ↔ s⁻¹ • x ∈ P.ker := fun x => by
    rw [hP, GlobalTheory.LatPair.Pair.smul_ker, GlobalTheory.LatPair.mem_smul_iff, hgi]
  have hvec : P'.vec - s • P.vec ∈ P'.ker := by
    have h1 := P.hasVal_vec.gl_smul g
    rw [← hP, hgx] at h1
    have := GlobalTheory.LatPair.Pair.sub_vec_mem h1
    rw [← neg_sub]
    exact neg_mem this
  rw [GlobalTheory.LevelUnfold.mem_gluedS, GlobalTheory.LevelUnfold.mem_gluedS]
  refine exists_congr fun σ => and_congr_left' ?_
  have e1 : (Sum.elim u t : n ⊕ Fin 1 → k) ∘ Sum.inl = u := rfl
  have e2 : (Sum.elim (s • u) t : n ⊕ Fin 1 → k) ∘ Sum.inl = s • u := rfl
  rw [e1, e2]
  have e3 : s • u - σ • P'.vec = s • (u - σ • P.vec) - σ • (P'.vec - s • P.vec) := by
    simp only [smul_sub]
    rw [smul_comm σ s P.vec]
    abel
  rw [e3, Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ σ hvec), hker, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem emb_central_frame {p : SplitPt D k} {S A L : HSp D} {o : OrthDec S A L} {ζ : Fin L.rank → D.host.E}
    {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hsum : IsSumFrame o ζ β β₀) {a : GA D A}
    {c' : AE D} (ha : mt A a = c' • (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))) (y : n ⊕ Fin 1 → k) :
    (mt S (o.emb (a, 1))).map p.pr *ᵥ (β₀.b *ᵥ y) =
      β₀.b *ᵥ Sum.elim (fun i => p.pr c' * y (Sum.inl i)) (fun j => y (Sum.inr j)) := by
  have h3 : (mt A a).map p.pr = β.b * (p.pr c' • (1 : Matrix n n k)) * β.b' := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, β.bb', ha]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have e := GlobalTheory.FinPl.Comm.block_calc p.pr _ _ _ _ _ _ _ (o.emb_jA a 1) (GlobalTheory.FinPl.Comm.emb_vecB o ζ a) h3 β.b'b
  rw [← hsum] at e
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  congr 1
  ext (i | j) <;> simp [Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

end Split

theorem exists_central_sMoves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M M' μ T q P a₀ hn hsum hM hM' hlat hμ hline hnorm hval hconj
  obtain ⟨M'', hsd'', hmv⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D S M' hM').1 (o.emb (a₀, 1))⁻¹
  have hmv' : Moves S (o.emb (a₀, 1)) M'' M' (· = p.v) := by
    have := moves_inv (hmv (· = p.v))
    rwa [inv_inv] at this
  have hline'' : LineAt (vecB o ζ) μ M'' p.v := by
    intro b hb
    rw [← hline b hb, hmv' (b • ratV (vecB o ζ)) (fun i => Ideal.mul_mem_right _ _ hb), Matrix.mulVec_smul,
      GlobalTheory.FinPl.Comm.emb_vecB]
  obtain ⟨P', hP'⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.exists_gluedW D k p S A L o ζ n β β₀ M'' μ T q hsum hsd'' hμ hline'' hnorm hval
  have hm : p.pr (incA D μ) ≠ 0 := by
    intro h0
    have h1 : p.pr (incA D μ * incA D μ⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hW : GluedW β₀ M q 1 P := fun x => by
    have e : (Sum.elim (fun a => x (Sum.inl a)) (fun j => 1 * x (Sum.inr j)) : n ⊕ Fin 1 → k) = x := by
      ext (i | i) <;> simp
    rw [e]
    exact (hlat x).symm
  have hstab : ∀ g : GL n k, g • P = P ↔ g • P' = P' := fun g => by
    rw [← _root_.GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq D k p S A L o ζ n β β₀ M q 1 P hsum hM one_ne_zero hW g,
      ← _root_.GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq D k p S A L o ζ n β β₀ M'' q _ P' hsum hsd'' hm hP' g,
      hconj _ (GlobalTheory.FinPl.FrameLat.gl_mem_grpAt β g)]
    have e : o.emb (a₀ * β.gl g * a₀⁻¹, 1) = o.emb (a₀, 1) * o.emb (β.gl g, 1) * (o.emb (a₀, 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, inv_one, mul_one, mul_one]
    rw [e, moves_conj hmv']
  obtain ⟨g, s, hs, hg, hPP⟩ := _root_.GlobalTheory.LatPair.StabScal.eq_scalar_smul_of_stab k n P P' hn hstab
  obtain ⟨c, hc, hcpr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (p.pr (incA D μ))⁻¹ (inv_ne_zero hm)
  obtain ⟨c', hc', hc'pr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (s * p.pr (incA D μ)) (mul_ne_zero hs hm)
  obtain ⟨a, hcen, hamt⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar D A p.v c' hc'
  refine ⟨a, c, hcen, hc, ?_⟩
  have key : SMoves S c (o.emb (a, 1)) M M'' p.v := by
    refine _root_.GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp D k p S M M'' c (o.emb (a, 1)) hM hsd'' hc fun x => ?_
    have hx : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    rw [hx, emb_central_frame hsum hamt, ← Matrix.mulVec_smul, hW, hP']
    refine (mem_gluedS_smul q hs hg hPP _ _).trans (iff_of_eq ?_)
    congr 1
    ext (i | j)
    · simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, hcpr, hc'pr]
      field_simp
    · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, hcpr]
      field_simp
  have e : o.emb (a₀ * a, 1) = o.emb (a₀, 1) * o.emb (a, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e]
  exact sMoves_trans key hmv'

end GlobalTheory.Core.Mi.LatMatch.CoreHomothety
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevZeroInd in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LevZero.gen : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  intro D c v cm st b G h0 hB Q hmul hN hU hred
  classical
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (c.V 0).rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero (c.V 0) st.β st.L D.R.r D.R.t hr hn cm.Pg cm.P cm.chi ξ hL
    (Lev.finE (c.V 0) x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ levS (c.V 0) st.β st.L, Lev.finE (c.V 0) x ∈ St st.β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ PP : cm.Pg, ∃ z, GlobalTheory.LevZero.Red (G PP) PP.1 z (upperLeftBlock hr (redFn st.β PP.1 (Lev.finE (c.V 0) x))) :=
    fun x hx PP => (hB.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ y ∈ levS (c.V 0) st.β st.L, x * y ∈ levS (c.V 0) st.β st.L :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ levS (c.V 0) st.β st.L, x⁻¹ ∈ levS (c.V 0) st.β st.L := fun x hx => Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ levS (c.V 0) st.β st.L,
      (∀ PP ∈ cm.Pg, PP ∉ s → redFn st.β PP (Lev.finE (c.V 0) k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ cm.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := _root_.GlobalTheory.LevZeroPlace.one_place cm st b G h0 hB Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn st.β a (Lev.finE (c.V 0) m) = redFn st.β a (Lev.finE (c.V 0) k) :=
          reductionBlock_injective_of_eq hr hn ((GlobalTheory.LevZeroUniq.main (G ⟨a, haP⟩) a (hB.loc ⟨a, haP⟩).idem).2 z z _ _ (hmr hr) hz
            (by rw [inv_mul_cancel]; exact one_mem _))
        have hk1 : m⁻¹ * k ∈ levS (c.V 0) st.β st.L := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn st.β PP (Lev.finE (c.V 0) (m⁻¹ * k)) =
            (redFn st.β PP (Lev.finE (c.V 0) m))⁻¹ * redFn st.β PP (Lev.finE (c.V 0) k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim cm.Pg k hk fun PP hPP h => absurd hPP h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIffCharacterTrivialSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIntChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_of_le_one {ψk : AddChar k Circle} (hc : HasConductor ψk 1) {y : k} (hy : valuation k y ≤ 1) : ψk y = 1 :=
  (hc 1).2 (by simp) y (by simpa using hy)

theorem trivial_iff_mem {ψk : AddChar k Circle} (hc : HasConductor ψk 1) {ξ : k} (hξ : valuation k ξ = 1) (t : k) :
    (∀ c ∈ 𝒪[k], ψk (t * c / ξ) = 1) ↔ t ∈ 𝒪[k] := by
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hξ
  constructor
  · intro h
    by_cases ht : t = 0
    · rw [ht]; exact zero_mem _
    have h1 := (hc (t / ξ)).1 (fun y hy => by
      have hc' : y * ξ / t ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_div₀, map_mul, hξ, mul_one]
        rw [map_div₀, hξ, div_one] at hy
        exact div_le_one_of_le₀ hy zero_le'
      have := h _ hc'
      rwa [show t * (y * ξ / t) / ξ = y by field_simp] at this)
    rw [Valuation.mem_integer_iff]
    simpa [map_div₀, hξ] using h1
  · intro ht c hc'
    apply triv_of_le_one hc
    rw [map_div₀, hξ, div_one]
    exact (Valuation.mem_integer_iff _ _).1 (mul_mem ht hc')

theorem int_iff_psiE : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), valuation k ((ofSplit q).xi) = 1 → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ s ∈ GlobalTheory.FinPl.idAt D (· = q.v), (s ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ ∀ o ∈ GlobalTheory.FinPl.intAt D (· = q.v), psiE ψ (s * o) = 1) := by
  intro D k _ _ _ _ q ψ ψk hξ hχ hc s hs
  have hι : ∀ y, psiE ψ (q.sec y) = ψk (y / (ofSplit q).xi) := fun y => GlobalTheory.LocBesChar.psiE_ι (ofSplit q) hχ y
  have hone : ∀ y, valuation k y ≤ 1 → psiE ψ (q.sec y) = 1 := fun y hy => by
    rw [hι, triv_of_le_one hc (by rw [map_div₀, hξ, div_one]; exact hy)]; rfl
  constructor
  · intro hsI o ho
    have hso : s * o ∈ GlobalTheory.FinPl.idAt D (· = q.v) := Ideal.mul_mem_right _ _ hs
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitIntComp.mem_intAt_iff q hs).1 hsI
    obtain ⟨h3, h4⟩ := (GlobalTheory.SplitIntComp.mem_intAt_iff q ho.1).1 ho
    rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q hso, psiE_add, GlobalTheory.LocBesChar.psiE_cA, hone, hone, one_mul]
    · rw [map_mul, map_mul]; exact (Valuation.mem_integer_iff _ _).1 (mul_mem h2 h4)
    · rw [map_mul]; exact (Valuation.mem_integer_iff _ _).1 (mul_mem h1 h3)
  · intro h
    rw [GlobalTheory.SplitIntComp.mem_intAt_iff q hs]
    constructor
    · rw [← trivial_iff_mem hc hξ]
      intro c hc'
      have hm : q.sec c ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
        simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff q 1 c).2 (by simpa using hc')
      have := h _ hm
      rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right, hι, mul_comm c] at this
      exact Circle.coe_inj.1 (this.trans Circle.coe_one.symm)
    · rw [← trivial_iff_mem hc hξ]
      intro c hc'
      have hm : cA D (q.sec c) ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
        simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff q 1 c).2 (by simpa using hc')
      have := h _ hm
      rw [mul_comm, GlobalTheory.Core.Mi.LatMatch.cA_sec_mul, GlobalTheory.LocBesChar.psiE_cA, hι, mul_comm c] at this
      exact Circle.coe_inj.1 (this.trans Circle.coe_one.symm)

end GlobalTheory.SplitIntChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal

theorem quotient_integral_of_subsingleton {G : Type} [Group G] [MeasurableSpace G] [Subsingleton G] {R : Subgroup G}
    (μR : Measure R) (μG : Measure G) (hR : μR Set.univ = 1) (hG : μG Set.univ = 1) (f : G → ℂ) :
    IsQuotIntL1 μR μG f (f 1) := by
  haveI : IsProbabilityMeasure μR := ⟨hR⟩
  haveI : IsProbabilityMeasure μG := ⟨hG⟩
  have hc : ∀ x, f x = f 1 := fun x => by rw [Subsingleton.elim x 1]
  have hf : f = fun _ => f 1 := funext hc
  refine ⟨fun _ => f 1, integrable_const _, fun _ => integrable_const _, fun h => ?_, ?_⟩
  · simp [hc h]
  · simp

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem conv_nil' {G : Type} [Monoid G] : conv ([] : List (G →₀ ℂ)) = Finsupp.single 1 1 := rfl

theorem aconv_singleton' {G : Type} [AddMonoid G] (c : G →₀ ℂ) : aconv [c] = c := by
  simp only [aconv, List.foldr_cons, List.foldr_nil]
  conv_rhs => rw [← Finsupp.sum_single c]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem aconv_nil' {G : Type} [AddMonoid G] : aconv ([] : List (G →₀ ℂ)) = Finsupp.single 0 1 := rfl

theorem comb_single_zero' (S' T : HSp D) (u : WO S' T → ℂ) :
    comb ψ S' T (Finsupp.single 0 1) u = u := by
  simp [comb, Finsupp.support_single_ne_zero _ one_ne_zero, heisO_zero_eq]

theorem trc_single_one' {V : HSp D} (u : GA D V → ℂ) : trc (Finsupp.single 1 1) u = u := by
  simp only [trc, Finsupp.support_single_ne_zero (1 : GA D V) (one_ne_zero (α := ℂ)), Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext x
  show u (x * 1) = u x
  rw [mul_one]

theorem value_zero_eq (Q : Fin 0 → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ 1 1 := by
  simp only [value, integrand, List.ofFn_zero, conv_nil', aconv_singleton', trc_single_one']
  rw [GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]
  simp [aconv_nil', comb_single_zero']
end

end GlobalTheory.QVal

namespace GlobalTheory.QVal

theorem valQr_zero : ∀ D : D7, ValQr D 0 := by
  intro D ψ _ σ S Q _ μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ _
  obtain ⟨-, -, -, -, e1, e2, e3, e4⟩ := hN
  have hP : ¬ ∃ v, places Q v := fun ⟨_, i, _⟩ => i.elim0
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.J.W (places Q)) := by
    rw [grpAt_eq_bot S.J.W hP]; infer_instance
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) := by
    rw [grpAt_eq_bot S.B'.V hP]; infer_instance
  simp only [IsEmpty.forall_iff, Set.setOf_true] at e1 e2 e3 e4
  refine ⟨fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1, ?_, fun q => ?_⟩
  · have := quotient_integral_of_subsingleton ρ₁ μ₁ e2 e1 (fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1)
    simpa [value_zero_eq] using this
  · have := quotient_integral_of_subsingleton ρ₂ μ₂ e4 e3 (fun y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ q.1 y.1)
    simpa using this

end GlobalTheory.QVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_finite_of_tuple_conditions : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → OffLaw v w → GSupp (t := t) v → QFin v w → t.LocFin := by
  first | exact @GlobalTheory.FirstCells.locFin | exact GlobalTheory.FirstCells.locFin | (intros; apply GlobalTheory.FirstCells.locFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBesselStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∀ q₂ ∈ GfC (c.V (j + 1 + 1)), integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1 + 1), q₂ = r * y * (κ * k) := by
  first | exact @GlobalTheory.DStepSuppSecond.integ_support | exact GlobalTheory.DStepSuppSecond.integ_support | (intros; apply GlobalTheory.DStepSuppSecond.integ_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacobStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ GfC (c.V (j + 1)), ∀ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1), q₁ = r * y * (κ * k) := by
  first | exact @GlobalTheory.DStepSupp.main | exact GlobalTheory.DStepSupp.main | (intros; apply GlobalTheory.DStepSupp.main <;> assumption)
end

