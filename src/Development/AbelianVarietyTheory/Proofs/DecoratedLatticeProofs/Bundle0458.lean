module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0441
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.SymChain.SymData.RowLam

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sum_sum_lt {ι κ' : Type} [Fintype ι] [Fintype κ'] (f : ι → κ' → k)
    (hf : ∀ i j, valuation k (f i j) < 1) : valuation k (∑ i, ∑ j, f i j) < 1 := by
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  exact Valuation.map_sum_lt _ one_ne_zero (fun j _ => hf i j)

theorem psi_inv_mul_eq_one (ψ : AddChar k Circle) (ϖ : kˣ) (hψ : GlobalTheory.SplitWeil.HasConductor ψ 1)
    (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {t : k} (ht : valuation k t < 1) :
    ψ (((ϖ⁻¹ : kˣ) : k) * t) = 1 := by
  have h1 := (hψ 1).2 (by simp)
  apply h1
  have hle : valuation k t ≤ valuation k (ϖ : k) := (hϖ t).1 ht
  rw [map_mul, map_one]
  calc valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k t
      ≤ valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k (ϖ : k) := by gcongr
    _ = 1 := by rw [← map_mul]; simp

end GlobalTheory.SymChain.SymData.RowLam

open GlobalTheory.SymChain.SymData.RowLam in
theorem GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  intro k _ _ _ _ s κ S x M hM hsup
  have hS := S.sym.2 x
  have hsimple : valuation k (GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k)) < 1 := by
    unfold GlobalTheory.RootEx.simpleSum
    apply val_sum_sum_lt
    intro i j
    split_ifs with h
    · exact hsup i j h
    · simp
  have hdiff : valuation k (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ -
      ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) < 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply val_sum_sum_lt
    intro a b
    split_ifs with h
    · simpa [Matrix.toBlocks₁₁] using hM a b
    · simp
  have e1 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hsimple
  have e2 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hdiff
  have e3 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁) =
      S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) := by
    rw [mul_sub, AddChar.map_sub_eq_div] at e2
    exact div_eq_one.mp e2
  rw [hS, e1, e3]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensColPhiOneCharIndSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

section Translate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_phiOne_charInd_smul (χ : AddChar 𝓀[k] ℂ) (P₁ : Pair k n') (Q : Pair k n) (g : GL n k)
    (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol (phiOne P₁ Q) (charInd χ Q) ((g⁻¹ : GL n k).val * x) =
      tensCol (phiOne P₁ (g • Q)) (charInd χ (g • Q)) x := by
  have hcol : (fun i => ((g⁻¹ : GL n k).val * x) i (Sum.inr 0)) = (g⁻¹ : GL n k) • (fun i => x i (Sum.inr 0)) := rfl
  have hsub : ((g⁻¹ : GL n k).val * x).submatrix id Sum.inl = (g⁻¹ : GL n k).val * x.submatrix id Sum.inl := rfl
  have hphi : ∀ z : Matrix n n' k, phiOne P₁ (g • Q) z = phiOne P₁ Q ((g⁻¹ : GL n k).val * z) := by
    intro z
    have h := phiOne_smul (P := P₁) (Q := Q) (x := z) (1 : GL n' k) g
    rw [one_smul] at h
    rw [h, Units.val_one, Matrix.mul_one]
  have hchi : ∀ y : n → k, charInd χ (g • Q) y = charInd χ Q ((g⁻¹ : GL n k) • y) := by
    intro y
    unfold charInd vecInd
    rw [Pair.smul_lat, mem_smul_iff]
    split_ifs with hy
    · have hv := Pair.hasVal_ev (P := g • Q) (x := y) (by rw [Pair.smul_lat, mem_smul_iff]; exact hy)
      rw [Pair.smul_hasVal] at hv
      rw [hv.ev_eq]
    · simp
  unfold tensCol
  rw [hsub, hcol, hphi, hchi]

end Translate

end GlobalTheory.FinPl

namespace GlobalTheory.FinPl

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyVacuumData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mem_latV_iff (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) (w : Fin S.rank → k) :
    (fun i => q.sec (w i)) ∈ latV S L (· = q.v) ↔ ∀ i, w i ∈ 𝒪[k] := by
  classical
  have hmem : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hsingle : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ L := fun i =>
    (hmem _).2 fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
  let G : Finset (Fin S.rank → D.host.E) := Finset.univ.image fun i => Pi.single i 1
  have hGL : ∀ x ∈ (G : Set (Fin S.rank → D.host.E)), x ∈ L := by
    intro x hx
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hsingle i
  have hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L := by
    apply le_antisymm
    · rw [Submodule.span_le]; exact hGL
    · intro x hx
      have hi := (hmem x).1 hx
      have e : x = ∑ i, (⟨x i, hi i⟩ : 𝓞 D.host.E) • (Pi.single i 1 : Fin S.rank → D.host.E) := by
        funext j
        rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
        simp [Algebra.smul_def]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G]))
  constructor
  · intro h
    have h1 := FullLatFrame.pr_mem_span q G hG h
    simp only [q.pr_sec] at h1
    have h2 : ∀ z ∈ Submodule.span 𝒪[k] (FullLatFrame.aux₃ q '' (G : Set (Fin S.rank → D.host.E))), ∀ i, z i ∈ 𝒪[k] := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        intro i
        exact FullLatFrame.pr_int_mem q ⟨x i, (hmem x).1 (hGL x hx) i⟩
      | zero => intro i; exact zero_mem _
      | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
      | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
    exact h2 _ h1
  · intro h
    have e : w = ∑ i, (⟨w i, h i⟩ : 𝒪[k]) • FullLatFrame.aux₃ q (S := S) (Pi.single i 1) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [FullLatFrame.aux₃, Pi.single_apply, Ne.symm hb]) (by simp)]
      simp [FullLatFrame.aux₃]
      change _ = w j * 1
      rw [mul_one]
    rw [← FullLatFrame.mem_latW, e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [FullLatFrame.mem_latW]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (hsingle i)

theorem intIn_stdFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) : IntIn q S (stdFr k e) L := by
  intro y
  rw [sec_mem_latV_iff q S L hL]
  have h : (stdFr k e).β *ᵥ y = y ∘ e.symm := by
    change (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e *ᵥ y = _
    have := Matrix.submatrix_mulVec_equiv (1 : Matrix (Fin S.rank) (Fin S.rank) k) y id e
    simpa [Function.comp_def] using this
  rw [h]
  exact ⟨fun h i => h _, fun h a => by simpa using h (e a)⟩

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFr {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (e : Y ≃ Fin N) (d : Y → k) (hd : ∀ y, d y ≠ 0) :
    GlobalTheory.LocMod.Frame k N Y where
  β := (stdFr k e).β * Matrix.diagonal d
  γ := Matrix.diagonal (fun y => (d y)⁻¹) * (stdFr k e).γ
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      show (fun y => d y * (d y)⁻¹) = fun _ => (1 : k) from funext fun y => mul_inv_cancel₀ (hd y),
      Matrix.diagonal_one, Matrix.one_mul, (stdFr k e).βγ]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (stdFr k e).γ, (stdFr k e).γβ, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      show (fun y => (d y)⁻¹ * d y) = fun _ => (1 : k) from funext fun y => inv_mul_cancel₀ (hd y), Matrix.diagonal_one]

theorem intIn_diagFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) (d : Y → k) (hd : ∀ y, d y ≠ 0) (hv : ∀ y, valuation k (d y) = 1) :
    IntIn q S (diagFr e d hd) L := by
  intro y
  have h1 := intIn_stdFr q S L hL e (fun a => d a * y a)
  have h2 : (diagFr e d hd).β *ᵥ y = (stdFr k e).β *ᵥ fun a => d a * y a := by
    change ((stdFr k e).β * Matrix.diagonal d) *ᵥ y = _
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext a
    exact Matrix.mulVec_diagonal _ _ _
  rw [h2, ← h1]
  refine forall_congr' fun a => ?_
  change valuation k (y a) ≤ 1 ↔ valuation k (d a * y a) ≤ 1
  rw [map_mul, hv, one_mul]

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

theorem oTop_iA {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

theorem oTop_iB {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iB b a = if (I.rec7 l Z).sp.X'.rank = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

theorem entry_inl {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ} {Y : Type} [Fintype Y]
    [DecidableEq Y] (eT : Y ≃ Fin n) (iA : Matrix (Fin N) (Fin n) E) (hA : ∀ b a, iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0)
    (r : Fin N) (c : Y) (m : Fin N) (hm : (m : ℕ) = eT c) :
    (1 : Matrix (Fin N) (Fin N) k) r m = (iA.map f * (1 : Matrix (Fin n) (Fin n) k).submatrix id eT) r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (eT c)
    (fun b _ hb => by rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]) (by simp)]
  rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, hA, Matrix.one_apply]
  by_cases h : (eT c : ℕ) = r
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

theorem entry_inr {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ}
    (iB : Matrix (Fin N) (Fin 1) E) (hB : ∀ b a, iB b a = if n = (b : ℕ) then 1 else 0) (z : Fin 1 → E) (x : E)
    (hz : ∀ i, z i = x) (r : Fin N) (m : Fin N) (hm : (m : ℕ) = n) :
    (1 : Matrix (Fin N) (Fin N) k) r m * f x = (iB.map f *ᵥ fun i => f (z i)) r := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, hB, hz, Matrix.one_apply]
  by_cases h : n = (r : ℕ)
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames


end GlobalTheory.XGeoStd.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryClassRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiCol

theorem colLam_ne_zero {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : colLam T v g ≠ 0 := by
  unfold colLam
  split_ifs with h
  · simp only [Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one]
    intro h0
    have e := (T.gl.psi0 h.choose v h.choose_spec).map_add_eq_mul
      (∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0)
      (-(∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at e
    exact one_ne_zero e
  · exact one_ne_zero

theorem mem_type_prod_iff {D : D7} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ↔ ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem, Fin.exists_fin_two]

end GlobalTheory.FamTraceChiCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceAtG

theorem mat_embA_besFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) (h : GA D B.A)
    (g₀ : GL n k) (hh : (mt B.A h).map p.π = FA.β * g₀.val * FA.γ) :
    (mt B.V (embA B.d B.o h)).map p.π = F.β * (GlobalTheory.RootEx.embX c g₀).val * F.γ := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  have hint : (mt B.V (B.d.emb0 (B.o.emb (h, 1)))).map p.π * ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) =
      (rat (B.d.i₀ * B.o.iA)).map p.π * FA.β * g₀.val := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, eA, Matrix.map_mul, hh]
    simp only [Matrix.mul_assoc]
    rw [FA.γβ, Matrix.mul_one]
  refine GlobalTheory.LocGrp.eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 hint fun j => ?_
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.TraceAtG

end

noncomputable section
open GlobalTheory.FamTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedConjugatePlaceInverseUniformizerValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), ResEta D χ 0 → ∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w ≠ w' → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w' ∧ GlobalTheory.LFun.val (F := D.host.F) χ w' = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  first | exact @GlobalTheory.SplitUnr.unrAt_and_val_inv | exact GlobalTheory.SplitUnr.unrAt_and_val_inv | (intros; apply GlobalTheory.SplitUnr.unrAt_and_val_inv <;> assumption)
end

