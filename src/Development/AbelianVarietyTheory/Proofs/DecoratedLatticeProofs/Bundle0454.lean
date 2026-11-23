module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinIntBridge

theorem comm_symm_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm a ∈ GlobalTheory.AdelicU.intLoc F E v := by
  have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ≤
      (GlobalTheory.AdelicU.intLoc F E v).comap
      ((Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F ⊗[F] E) := by
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
    · obtain ⟨x, rfl⟩ := RingHom.mem_range.1 (show e ∈ (algebraMap (𝓞 E) E).range from he)
      simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (one_mem _) x
    · simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (a := b) hb 1
  exact hle ha

theorem prV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (y : AF F ⊗[F] E) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm (Formalism.UG.prV (E := E) v
      (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y))) =
      Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_intLoc_of_finM : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D V n hn κ x hx v h i j
  have h1 := comm_symm_mem v (h (finCongr hn i) (finCongr hn j))
  have h2 : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 (finCongr hn i) (finCongr hn j) =
      Formalism.UG.prV (E := D.host.E) v (toEAf D (Formalism.L2.Theta.mt V κ i j)) := by
    change Formalism.UG.prV (E := D.host.E) v (x.1 (finCongr hn i) (finCongr hn j)) = _
    rw [← hx]
    simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  rw [h2] at h1
  have h3 := prV_gen (F := D.host.F) (E := D.host.E) v (Formalism.L2.Theta.mt V κ i j)
  exact (congrArg (· ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) h3).mp h1

end GlobalTheory.FinIntBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryIntegralityCongruence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceBwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colGroup_of_embX {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J) : g ∈ colGroup k κ (Fin τ) := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  rw [← h1]
  refine ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩
  · rw [one_mul]
    exact (le_sup_left : (embX (s + 1)).range ≤ R k _ (s + 1) 1) ⟨g, rfl⟩
  · rw [inv_one, one_mul, mul_one, one_mul]
    exact hg

theorem entries_of_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : g ∈ colGroup k κ (Fin τ)) (a b : XIx (Fin κ) (Fin τ) 0) :
    g.val a b ∈ 𝒪[k] ∧ (e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  obtain ⟨_, ⟨g₀, rfl, rfl⟩, hu⟩ := hg
  refine ⟨(g₀.val a b).2, fun hab => ?_⟩
  have h1 : residue 𝒪[k] (g₀.val a b) = (1 : Matrix _ _ 𝓀[k]) a b := hu a b (by rw [hp, hp]; exact hab)
  have h2 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
    simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
  rw [h2, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h1
  have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h1
  convert h3 using 2
  simp only [Matrix.one_apply]
  split_ifs <;> rfl

theorem exists_mat {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k V.rank Y) (e : Y ≃ Fin V.rank) (hβ : F.β = (1 : Matrix (Fin V.rank) (Fin V.rank) k).submatrix id e) (x : GA D V) :
    ∃ g : GL Y k, (mt V x).map q.pr = F.β * g.val * F.γ ∧ ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := by
  have hmul : ∀ y z : GA D V, y * z = 1 → (F.γ * (mt V y).map q.pr * F.β) * (F.γ * (mt V z).map q.pr * F.β) = 1 := fun y z h => by
    have h1 : mt V y * mt V z = 1 := by
      have h2 : mt V y * mt V z = mt V (y * z) := rfl
      rw [h2, h]
      rfl
    have h3 : (mt V y).map q.pr * (mt V z).map q.pr = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = F.γ * ((mt V y).map q.pr * (F.β * F.γ) * (mt V z).map q.pr) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h3, Matrix.mul_one, F.γβ]
  let g : GL Y k := ⟨_, _, hmul x x⁻¹ (mul_inv_cancel x), hmul x⁻¹ x (inv_mul_cancel x)⟩
  have hg : (mt V x).map q.pr = F.β * g.val * F.γ := by
    calc _ = (F.β * F.γ) * (mt V x).map q.pr * (F.β * F.γ) := by rw [F.βγ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [g, Matrix.mul_assoc]
  refine ⟨g, hg, fun a b => ?_⟩
  have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [hβ] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm

end Loc


end GlobalTheory.FamTrace.TraceBwd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionIntegralAdelicReduction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FunObj.Comparison₂ (IsRed Compat IsIx)

namespace GlobalTheory.QTw.LocFn

section Red

variable {S F K : Type} [CommRing S] [CommRing F] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* F} {ψ : S →+* K}

theorem parPhi_eq_of_equiv (h : IsRed φ ψ) {R : Type} [Fintype R] [DecidableEq R] {r t j j' a b : ℕ} (f : Fin r ≃ R)
    {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) j' ≃ Fin b}
    (ha : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j × Fin t))).trans ea))
    (hb : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j' × Fin t))).trans eb))
    {c : Fˣ →* ℂˣ} {δ : Kˣ →* ℂˣ} (hc : Compat φ ψ c δ⁻¹) (N : Matrix (Fin b) (Fin a) S) :
    parPhi δ ((N.map ψ).submatrix eb ea) =
      if H : LowZero r (N.map φ) ∧ IsUnit (topL r (N.map φ)).det then (c H.2.unit : ℂ) else 0 := by
  have e1 : (topL r (N.map φ)).det = ((N.submatrix eb ea).toBlocks₁₁.map φ).det := by
    rw [GlobalTheory.FunObj.Comparison₂.topL_r ha hb, ← det_submatrix_equiv_self f]
    rfl
  have e2 : LowZero r (N.map φ) ↔ MaxM ((N.map ψ).submatrix eb ea).toBlocks₂₁ :=
    (GlobalTheory.FunObj.Comparison₂.lowZero_r h ha hb N).trans
      ⟨fun H i l => by
        obtain ⟨l, rfl⟩ := f.surjective l
        exact H i l, fun H i l => H i (f l)⟩
  split_ifs with H
  · obtain ⟨g, hg, e⟩ := (h.isUnit_det_iff _).1 (e1 ▸ H.2)
    rw [parPhi_of_mem (x := (N.map ψ).submatrix eb ea) _ hg e (e2.1 H.1) (fun _ _ => h.int _) (fun _ _ => h.int _),
      hc.det (k := Matrix.GeneralLinearGroup.det g) _ (H.2.unit_spec.trans e1) (congrArg Matrix.det e),
      MonoidHom.inv_apply]
  · by_contra h0
    obtain ⟨h1, h2, -⟩ := (parPhi_ne_zero_iff _).1 h0
    exact H ⟨e2.2 h2, e1 ▸ (h.isUnit_det_iff _).2 h1⟩

theorem tame_congr {δ : Kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Kˣ} (hx : valuation K (x : K) = 1)
    (h : valuation K ((x : K) - y) < 1) : δ y = δ x := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  refine hδ _ ?_
  rwa [Units.val_mul, Units.val_inv_eq_inv_val, ← mul_inv_cancel₀ x.ne_zero, ← sub_mul, map_mul, map_inv₀, hx, inv_one,
    mul_one, Valuation.map_sub_swap]

end Red

theorem isIx_of_isOrd {κ l r t j a : ℕ} (h : κ + l = r) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) :
    IsIx ((Equiv.sumCongr (finSumFinEquiv.trans (finCongr h)).symm (Equiv.refl (Fin j × Fin t))).trans e) := by
  refine ⟨?_, fun i => ?_, fun c s => ?_⟩
  · simpa [h] using (Fintype.card_congr e).symm
  · obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective i
    rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, he]
    rcases i with i | i <;> rfl
  · refine (he (.inr (c, s))).trans ?_
    change κ + l + c.val * t + s.val = _
    rw [h, mul_comm]; omega

theorem parPhi_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : EAf D →+* k), (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (δ : kˣ →* ℂˣ), IsTame δ → ∀ (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), (∀ (z : 𝓞 D.host.E) (x : kˣ) (u : (Formalism.L2.DIV.kP PP)ˣ), (x : k) = (ofSplit q).pr (z : D.host.E) → (u : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ u)⁻¹) → ∀ (κ l r t j j' a b : ℕ), r = κ + l → ∀ (ea : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) (eb : Ix (Fin κ ⊕ Fin l) (Fin t) j' ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), parPhi δ ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = if H : LowZero r (N.map (Formalism.L2.DIV.resS D.host.F PP)) ∧ IsUnit (topL r (N.map (Formalism.L2.DIV.resS D.host.F PP))).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0 := by
  intro D k _ _ _ _ q PP π' hπ hred δ hδ ξ hξ κ l r t j j' a b hr ea eb ha hb N
  refine parPhi_eq_of_equiv hred _ (isIx_of_isOrd hr.symm ha) (isIx_of_isOrd hr.symm hb) (fun s u x hu hx => ?_) N
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
      (ofSplit q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have h2 : valuation k ((x : k) - (ofSplit q).pr (z : D.host.E)) < 1 := by
    rw [hx, ← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
    exact (hz.trans hu).symm
  have h3 : valuation k (x : k) = 1 := by
    rw [hx]; exact (hred.isUnit_iff s).1 (hu ▸ u.isUnit)
  have h4 : (ofSplit q).pr (z : D.host.E) ≠ 0 := fun h => by
    rw [h, sub_zero, h3] at h2
    exact lt_irrefl _ h2
  rw [MonoidHom.inv_apply, ← tame_congr hδ (y := Units.mk0 _ h4) h3 h2, hξ z (Units.mk0 _ h4) u rfl hz.symm, inv_inv]

end GlobalTheory.QTw.LocFn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrHOUpIncAdj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastPrimSplit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q, q.pr_sec]

theorem incAdj_yZero_apply {ρ : ℕ} (hρ : 0 < ρ) {S T T₀ : HSp D} (d : HypDec T T₀ ρ) (z : Fin S.rank → D.host.E)
    (a : AE D) (i : Fin T.rank) (l : Fin S.rank) :
    d.incAdj S (a • yZero S ρ z) i l =
      cA D a * incA D (D.host.xi0⁻¹ * d.e' i ⟨ρ - 1, by omega⟩ * (star z ᵥ* S.gram) l) := by
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell, map_sum]
  rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_true, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change incA D (d.e' i _) * (-incA D _ * (cA D a * -incA D (star (z m)) * incA D (S.gram m l))) =
    cA D a * (incA D _ * incA D (d.e' i _) * (incA D (star (z m)) * incA D (S.gram m l)))
  ring

theorem map_row {E : Type} [Field E] (f : E →+* k) {m n : Type} [Fintype m] (w : m → E) (M : Matrix m n E) (j : n) :
    ∑ l, f (w l) * f (M l j) = f ((w ᵥ* M) j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, RingHom.map_mul]

theorem row_core (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    (fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β =
      Pi.single (Sum.inr ()) (sc * (ofSplit q).hz B) := by
  set f := q.pr.comp (incA D) with hf
  funext t
  rcases t with t | ⟨⟨⟩⟩
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have h0 : (fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* B.o.iA.map f = 0 := by
      funext j
      refine (map_row f _ B.o.iA j).trans ?_
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
        Matrix.vecMul_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
    have h1 : ((fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* (B.o.iA.map f * FA.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * F₀.β l (Sum.inl t) =
      ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * (B.o.iA.map f * FA.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.1 l t]
    rfl
  · rw [Pi.single_eq_same]
    have h0 : (star (vecB B.o B.ζ) ᵥ* B.V₀.gram) ⬝ᵥ vecB B.o B.ζ = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, B.o.isoB]
    change ∑ l, f _ * F₀.β l (Sum.inr ()) = sc * f (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.2 l, RingHom.map_mul, mul_left_comm]
    rfl

theorem row_jac (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (hρ : 0 < ρ) (J : JacLev D ρ) {n' : Type} [Fintype n'] [DecidableEq n']
    (sc hh : k) (FW₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (2 * ρ)))
    (hFW : (ofSplit q).IsJacFrame J sc hh FW₀ FW) :
    (fun l => q.pr (incA D ((J.d.e'ᴴ * J.W.gram) ⟨ρ - 1, by omega⟩ l))) ᵥ* FW.β =
      Pi.single (Sum.inr ⟨ρ - 1, by omega⟩) (sc * (ofSplit q).xi) := by
  set f := q.pr.comp (incA D) with hf
  set i₀ : Fin ρ := ⟨ρ - 1, by omega⟩ with hi₀
  have hcol : ∀ {m : ℕ} (M : Matrix (Fin J.W.rank) (Fin m) D.host.E) (j : Fin m),
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * f (M l j) = f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun M j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply (M := J.d.e'ᴴ * J.W.gram), map_sum]
    simp only [RingHom.map_mul]
  funext t
  rcases t with t | t
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have hz : J.d.e'ᴴ * J.W.gram * J.d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose J.d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have h0 : (fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* J.d.i₀.map f = 0 := by
      funext j
      refine (hcol J.d.i₀ j).trans ?_
      rw [hz, Matrix.zero_apply, map_zero, Pi.zero_apply]
    have h1 : ((fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* (J.d.i₀.map f * FW₀.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inl t) =
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * (J.d.i₀.map f * FW₀.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hFW.2.1 l t]
    rfl
  · change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = _
    have hmul : ∀ (c : k) (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ),
        (∀ r, FW.β r (Sum.inr t) = c * f (M r j)) →
        ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = c * f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun c M j h => by
      rw [← hcol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [h, mul_left_comm]
    by_cases ht : t.val < ρ
    · rw [hmul _ _ _ (hFW.2.2.1 ⟨t.val, ht⟩ t rfl), J.d.e'e]
      by_cases h2 : t.val = ρ - 1
      · have h3 : t = ⟨ρ - 1, by omega⟩ := Fin.ext h2
        have h4 : (⟨t.val, ht⟩ : Fin ρ) = i₀ := Fin.ext h2
        have h5 : ρ - (i₀ : ℕ) = 1 := by change ρ - (ρ - 1) = 1; omega
        rw [h4, Matrix.one_apply_eq, map_one, mul_one, h5, pow_one, h3, Pi.single_eq_same]
      · rw [Matrix.one_apply_ne fun h => h2 (congrArg Fin.val h).symm, map_zero, mul_zero,
          Pi.single_eq_of_ne fun h => h2 (congrArg Fin.val (Sum.inr_injective h))]
    · have h6 := t.2
      rw [hmul _ _ _ (hFW.2.2.2 ⟨2 * ρ - 1 - t.val, by omega⟩ t (by change t.val + (2 * ρ - 1 - t.val) + 1 = _; omega)),
        J.d.e'e', Matrix.zero_apply, map_zero, mul_zero, Pi.single_eq_of_ne fun h => ht (by
          have h7 : t.val = ρ - 1 := congrArg Fin.val (Sum.inr_injective h)
          omega)]

end GlobalTheory.LastPrimSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalTransferWeilPairingInertPlacesStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalTransfer_weilPairing_inertPlaces : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun v => ¬ IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.transferOn_inert | exact GlobalTheory.ChainOnto.transferOn_inert | (intros; apply GlobalTheory.ChainOnto.transferOn_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPlace

theorem under_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (h : Formalism.L2.NTheta.IsIdemAt q.e PP) :
    HeightOneSpectrum.under (𝓞 D.host.F) PP = q.v := by
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
  obtain ⟨ε, hε, h3⟩ := q.above
  have h2 := q.split.2.1
  have h4 := GlobalTheory.IdemSupport.ev_mul (Φ := (GlobalTheory.StdFrames.toAd D).comp (toEAf D)) q.e (cA D q.e) PP
  rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul, eq_comm] at h4
  by_contra hv
  have := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 PP hv
  rw [← h3, GlobalTheory.IdemSupport.ev_add, h4, hd.2.1, add_zero] at this
  exact one_ne_zero this

theorem v_eq_of_isIdemAt : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (PP : Formalism.L2.DIV.Pl D.host.E),
    Formalism.L2.NTheta.IsIdemAt q.e PP → Formalism.L2.NTheta.IsIdemAt q'.e PP → q.v = q'.v :=
  fun _ _ _ _ _ _ _ _ _ _ _ q q' PP h h' => (under_eq q PP h).symm.trans (under_eq q' PP h')

end GlobalTheory.FinPl.SplitPlace
end

