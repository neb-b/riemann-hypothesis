module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawBetweenBasePointsMovedPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplit

theorem mem_latV_iff_wParts {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = p.v)) :
    y ∈ GlobalTheory.FinPl.latV S L (· = p.v) ↔ (fun i => p.sec (p.pr (y i))) ∈ GlobalTheory.FinPl.latV S L (· = p.v) ∧
      ∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = p.v) →
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * p.pr (cA D (y j)) ∈ 𝒪[k] := by
  have hy' : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    rw [Pi.add_apply, p.sec_pr, p.sec_pr, map_mul, GlobalTheory.LatVac.cA_cA, ← add_mul]
    exact ((GlobalTheory.FinPl.FrameLat.idem_iff p (y i)).1 (hy i)).symm
  conv_lhs => rw [hy']
  rw [GlobalTheory.FinPl.FrameLat.decomp hL, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]

theorem latV_eq_of_wPart : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L L' : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → IsSelfDualC S L' → (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v)) → GlobalTheory.FinPl.latV S L (· = q.v) = GlobalTheory.FinPl.latV S L' (· = q.v) := by
  intro D k _ _ _ _ q S L L' hL hL' h
  have key : ∀ (M M' : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → IsSelfDualC S M' →
      (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M' (· = q.v)) →
      ∀ y, y ∈ GlobalTheory.FinPl.latV S M (· = q.v) → y ∈ GlobalTheory.FinPl.latV S M' (· = q.v) := by
    intro M M' hM hM' hMM' y hy
    have hs : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = q.v) := fun i => GlobalTheory.FinPl.FrameLat.latV_supp hy i
    rw [mem_latV_iff_wParts q hM y hs] at hy
    rw [mem_latV_iff_wParts q hM' y hs]
    exact ⟨(hMM' _).1 hy.1, fun x hx => hy.2 x ((hMM' x).2 hx)⟩
  ext y
  exact ⟨key L L' hL hL' h y, key L' L hL' hL (fun x => (h x).symm) y⟩

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : GlobalTheory.FinPl.SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (b : Fin n → k) :
    ((rat M : Mx D m n) *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map ((ofSplit q).π.comp (incA D)) *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => GlobalTheory.SplitInt.mul_sec q _ _

end

theorem exists_lineLat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  intro D k _ _ _ _ q S A B o MS MA Y _ _ FA FS z hMS hMA ⟨LB₀, hLB₀⟩ hβA hβB hIS hIA
  set f : D.host.E →+* k := (ofSplit q).π.comp (incA D) with hf
  have hpr : (ofSplit q).pr = ⇑f := rfl
  rw [hpr] at hβA hβB
  have hc : Fintype.card (Y ⊕ Unit) = S.rank := FS.card_eq
  have hcA : Fintype.card Y = A.rank := FA.card_eq
  have hB1 : B.rank = 1 := by
    have := o.rank_add
    rw [Fintype.card_sum, hcA, Fintype.card_unit] at hc
    omega
  have hsub : ∀ i j : Fin B.rank, i = j := fun i j => Fin.ext (by omega)
  haveI : Subsingleton (Fin B.rank) := ⟨hsub⟩
  let i₀ : Fin B.rank := ⟨0, by omega⟩

  have hcol : ∀ c : Y ⊕ Unit → k, FS.β *ᵥ c =
      o.iA.map f *ᵥ (FA.β *ᵥ fun a => c (Sum.inl a)) + c (Sum.inr ()) • (o.iB.map f *ᵥ z) := by
    intro c
    funext r
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton, hβA, hβB,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => by ring
    · exact Finset.sum_congr rfl fun s _ => by ring
  have hz : z i₀ ≠ 0 := by
    intro h0
    have hz0 : z = 0 := funext fun i => by rw [hsub i i₀, h0]; rfl
    have h1 := congrFun (congrFun FS.γβ (Sum.inr ())) (Sum.inr ())
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [hβB, hz0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hz' : ∀ i, z i ≠ 0 := fun i => by rw [hsub i i₀]; exact hz
  let FB : Frame k B.rank Unit :=
    { β := Matrix.of fun i _ => z i
      γ := Matrix.of fun _ i => (z i)⁻¹
      βγ := by
        ext i j
        rw [hsub j i]
        simp [Matrix.mul_apply, hz' i]
      γβ := by
        ext u u'
        rw [Subsingleton.elim u' u]
        simp [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, hz] }
  obtain ⟨LB, hLB, -, hLBw⟩ := _root_.GlobalTheory.SplitLat.exists_selfDual_frame D k q B Unit FB LB₀ hLB₀
  obtain ⟨L', hL', hL'o⟩ := GlobalTheory.OrthSumLat.exists_selfDual_orthAt D S A B o MA LB hMA hLB
  have hFBv : ∀ y : k, (FB.β *ᵥ fun _ => y) = fun i => z i * y := fun y => by
    funext i
    simp [FB, Matrix.mulVec, dotProduct]
  refine ⟨LB, hLB, ?_, fun y => ?_⟩
  ·
    have hqA : o.qA.map f * o.iA.map f = 1 := by
      rw [← Matrix.map_mul, o.qA_iA, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqAB : o.qA.map f * o.iB.map f = 0 := by
      rw [← Matrix.map_mul, o.qA_iB, Matrix.map_zero _ (map_zero f)]
    have hqB : o.qB.map f * o.iB.map f = 1 := by
      rw [← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqBA : o.qB.map f * o.iA.map f = 0 := by
      rw [← Matrix.map_mul, o.qB_iA, Matrix.map_zero _ (map_zero f)]
    have hw : ∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S MS (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v) := by
      intro x
      set c := FS.γ *ᵥ x with hcdef
      have hx : x = FS.β *ᵥ c := by rw [hcdef, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      have hqx : o.qA.map f *ᵥ x = FA.β *ᵥ fun a => c (Sum.inl a) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iA.map f), hqA,
          Matrix.one_mulVec, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iB.map f), hqAB, Matrix.zero_mulVec, smul_zero,
          add_zero]
      have hqBx : o.qB.map f *ᵥ x = FB.β *ᵥ fun _ => c (Sum.inr ()) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iA.map f), hqBA,
          Matrix.zero_mulVec, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iB.map f), hqB, Matrix.one_mulVec, zero_add,
          hFBv]
        funext i
        simp [mul_comm]
      have eS := hIS c
      rw [← hx] at eS
      have eA := hIA (fun a => c (Sum.inl a))
      have eB := hLBw (fun _ => c (Sum.inr ()))
      rw [← eS, hL'o q.v, show o.pA = rat o.qA from rfl, show o.pB = rat o.qB from rfl, rat_mulVec_sec,
        rat_mulVec_sec, ← hf, hqx, hqBx, ← eA, ← eB, Sum.forall]
    intro y
    rw [latV_eq_of_wPart D k q S MS L' hMS hL' hw]
    exact hL'o q.v y
  · have := hLBw (fun _ => y)
    rw [hFBv] at this
    exact ⟨fun h => this.1 fun _ => h, fun h => this.2 h ()⟩

end GlobalTheory.LineSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceModelExtensionLineLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModelExtend

theorem isFullLattice_span {D : D7} {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsFullLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  have hζ : ζ ≠ 0 := by
    rintro rfl
    exact h.2 (by simp)
  letI : Submodule.IsLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) :=
    Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span_singleton ζ)
  refine ⟨?_⟩
  rw [Submodule.span_span_of_tower]
  exact (finrank_eq_one_iff_of_ne_zero ζ hζ).1 (by rw [Module.finrank_fin_fun, h.1])


open GlobalTheory.LocMod in
theorem exists_placeModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  intro D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL
  classical
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hLS
  letI := isFullLattice_span hζ
  obtain ⟨hAo, hAc⟩ := GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS
    (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) inferInstance inferInstance Unit n FS FL''
  have hinj : Function.Injective (Witness.ext P FS FL'') := by
    intro Φ Ψ h
    apply Subtype.ext; funext x
    have := congrFun h (P.up FS FL'' x)
    rwa [Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x),
      if_pos (Witness.up_half P FS FL'' x), Witness.down_up] at this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)
  set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d
  have hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ := fun Φ => by
    change TL (G (Witness.ext P FS FL'' Φ)) = TL Φ
    rw [← LinearMap.comp_apply G, hG, LinearMap.id_apply]
  have hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ :=
    _root_.GlobalTheory.SBOfHalf.exists_sb_ext_eq D k P S L'' Unit n FS FL'' Λ hAo hAc
  generalize hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc
  have hcl : IsClopen (A : Set (Matrix Unit n k)) := ⟨A.isClosed_of_isOpen hAo, hAo⟩
  let Φ₀ : SB (Matrix Unit n k) := ⟨(A : Set (Matrix Unit n k)).indicator 1,
    (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
  have e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ := by
    funext t
    rw [Witness.ext_apply, halfInd]
    change (if IsHalf p.e t then _ else _) = _
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      change (A : Set (Matrix Unit n k)).indicator 1 _ = _
      rw [Set.indicator_apply, ← hA]
      refine if_congr ?_ rfl rfl
      change P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _
      rw [Witness.up_down P FS FL'' ht, and_iff_left ht]
    · rw [if_neg ht, if_neg fun h => ht h.2]
  refine ⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => Φ'.1 (s + P.down FS FL'' x),
      Φ'.2.1.comp_continuous (continuous_add_const _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
    have e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply, Witness.down_add]
      exact if_congr (Witness.half_add hx) rfl rfl
    rw [e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s,
      _root_.GlobalTheory.ModSB.mul_char_mem_SB D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩
    have e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply]
      split_ifs with ht
      · change _ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _
        rw [Witness.up_down P FS FL'' ht]
      · rw [mul_zero]
    rw [e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]
  · rw [one_smul, ← e1, hT₃]

end GlobalTheory.ModelExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumBasePointsLawRationalTwistPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.ReadLaw


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem transport_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∀ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 → TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 → cosetIn q = cosetIn (A.p0 i α) → cosetIn q' = cosetIn (A.p0 (i + 1) γ) → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → A.xi i hi α γ z' = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀ κ₀' hκ hκ' q q' hq hq' hc hc' z z' v hv hvh hact
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 α
  have hb' := hA.base (i + 1) hi γ
  obtain ⟨M₀, hM₀, h2⟩ := GlobalTheory.AdForm.TwResid.xiAt_transport_tw I l hok u a i hi (A.b0 i α) (A.b0 (i + 1) γ)
    (A.p0 i α) q (A.p0 (i + 1) γ) q' (A.kb i α) κ₀ (A.kb (i + 1) γ) κ₀'
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 hq hq' hc hc'
  obtain ⟨z₂, t, ht, hth, hv2⟩ := _root_.GlobalTheory.AdForm.DenseHalf.half_eq_rat_add_nsmul ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) A.e _ hA.idem
    (d * M₀) (Nat.mul_pos hd hM₀) v hvh
  have hm : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • z₂.map (fun r => A.e * incA (I.rec7 l Z) r) := by
    have e := map_add (((AddMonoidHom.mulLeft A.e).comp (incA (I.rec7 l Z)).toAddMonoidHom).mapMatrix) z' (k • z₂)
    rw [map_nsmul] at e
    exact e
  have hcong : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + (d * M₀) • (-(k • t)) := by
    rw [hact, hm, hv2, smul_neg, smul_comm (d * M₀) k t, smul_add]
    abel
  have hc2 := h1 κ.1 κ'.1 κ₀ κ₀' hκ hκ' M₀ z (z' + k • z₂) (-(k • t)) (neg_mem (nsmul_mem ht k)) hcong
  have hx := h2 _ _ hc2
  have hw : IsHalf A.e (v - (d * M₀) • t) := fun r s => by
    rw [Matrix.sub_apply, Matrix.smul_apply, mul_sub, mul_smul_comm, hvh r s, hth r s]
  have hz2 : z₂.map (fun r => A.e * incA (I.rec7 l Z) r) = v - (d * M₀) • t := eq_sub_of_add_eq hv2.symm
  have hp := hper (z' + k • z₂) z' (v - (d * M₀) • t) (sub_mem hv (nsmul_mem ht _)) hw (by rw [hm, hz2])
  exact hp.symm.trans (congrArg B.embLL hx)

theorem law_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' hr hr' x y hx hy z z' v hv hvh hact
  obtain ⟨κ₀, hκ₀⟩ := ((hA.U i (Nat.le_of_succ_le hi) α κ.1).1 κ.2).2
  obtain ⟨κ₀', hκ₀'⟩ := ((hA.U (i + 1) hi γ κ'.1).1 κ'.2).2
  obtain ⟨q, q', hq, hq', hc, hc', hlaw⟩ := _root_.GlobalTheory.AdForm.MovedLaw.moved_law I hok hpins l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm
  have h2 := transport_base I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm q q' hq hq' hc hc' z z' v hv hvh hact
  rw [h2]
  exact hlaw _

end GlobalTheory.AdForm.ReadLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.Join

section
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)

theorem xiAt_eq_prod (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (x : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) :
    xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) x =
      Formalism.L2.Col.phiT B.fields.K (A.p0 i α).1.1.deco.1 (A.p0 (i + 1) γ).1.1.deco.1 x *
        ∏ P : BadPr I a, locXi A i α γ P x := by
  rcases lt_trichotomy (i + 2) B.R.m with h | h | h
  · rw [xiAt, dif_pos h]
    unfold Formalism.L2.Col.XiEntry
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locXi, dif_pos h]
  · rw [xiAt, dite_eq_right (by omega), dif_pos h]
    unfold Formalism.L2.Col.XiCpl1
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locXi, dite_eq_right (by omega), dif_pos h]
  · have h1 : i + 1 = B.R.m := by omega
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := B.R.two_le_m; omega⟩
    rw [xiAt, dite_eq_right (by omega), dite_eq_right (by omega), dif_pos h1]
    show xiOver _ _ _ _ n h1 _ _ _ x = _
    unfold xiOver
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locXi, dite_eq_right (by omega), dite_eq_right (by omega), dif_pos h1]
    rfl

theorem xi_eq_xiOff_mul (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) :
    A.xi i hi α γ z = xiOff A i hi α γ z *
      ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∉ (B.primes X).vGs), B.embLL (locXi A i α γ P (homOf I l Z i hi z)) := by
  unfold TwDat.xi xiOff
  refine (congrArg B.embLL (xiAt_eq_prod A i hi α γ (homOf I l Z i hi z))).trans ?_
  rw [map_mul, map_mul, map_prod, map_prod, mul_assoc, Finset.prod_filter_mul_prod_filter_not]

theorem entry_eq_sgn_mul (hI : I.Ok) : ∀ (c : Comm (I.rec7 l Z)) (v : VCom c) (Bs : GlobalTheory.Fam.Base c) PP (G : QGeo v Bs PP) χ (E : QExt G χ) hψ sg π (P : BadPr I a), ReadsAt A P E hψ sg π → ∀ j d (H : j + 1 + d = G.s) (hj : j + 1 ≤ B.R.m) (hj' : j + 1 < B.R.m) α γ (e' : XIx (Fin B.R.k) (Fin B.R.t) j ≃ Fin (B.R.N j)) (e : XIx (Fin B.R.k) (Fin B.R.t) (j + 1) ≃ Fin (B.R.N (j + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ x, (G.T E.δ E.tame E.η).entry G.ψk G.ν j d H (E.rep j (d + 1) (by omega) (π j α)) (E.rep (j + 1) d H (π (j + 1) γ)) (GlobalTheory.SymBridge.toLoc (G.q.pr.comp (incA (I.rec7 l Z))) e e' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)) = GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h j ((A.b0 j α).get hj) P) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) * GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h (j + 1) ((A.b0 (j + 1) γ).get hj') P) (B.R.N j + Formalism.L2.Col.cOf B.R j) * B.embLL (locXi A j α γ P x) := by
  intro c v Bs PP G χ E hψ sg π P hR j d H hj hj' α γ e' e he' he x
  have hAt := hR.tw
  have hs : G.s = B.R.m - 2 := by have := hAt.steps; omega
  have hL : (I.idx a).Ok I.Ch I.sel (I.tup a) (I.cst a) I.glob G.s := by rw [hs]; exact hI.idx_ok a
  have hEA := GlobalTheory.T.twistPrime_parahoricEntries_eq_columnData B.fields (B.primes X) B.R I.Ch I.sel _ (I.tup a) (I.cst a) B.embLL P G.k
    (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg) G.ν G.unitVol (hI.idx_ok a).cst_ok hAt (I.idx a) I.glob hL
  have h2 := hEA j d H ((A.b0 j α).get hj) ((A.b0 (j + 1) γ).get hj') _ _ (hR.rep j (d + 1) (by omega) hj α)
    (hR.rep (j + 1) d H hj' γ) e' e he' he
    (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)
  have hlt : j + 2 < B.R.m := by have := hAt.steps; omega
  simp only [locXi, dif_pos hlt]
  exact h2

end

theorem xi_factor_and_entry : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → (∀ i (hi : i + 1 ≤ B.R.m) α γ z, A.xi i hi α γ z = xiOff A i hi α γ z * ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∉ (B.primes X).vGs), B.embLL (locXi A i α γ P (homOf I l Z i hi z))) ∧ ∀ (c : Comm (I.rec7 l Z)) (hX : c.X = (I.rec7 l Z).sp.X) (v : VCom c) (Bs : GlobalTheory.Fam.Base c) PP (G : QGeo v Bs PP) χ (E : QExt G χ) hψ sg π (P : BadPr I a), ReadsAt A P E hψ sg π → ∀ j d (H : j + 1 + d = G.s) (hj : j + 1 ≤ B.R.m) (hj' : j + 1 < B.R.m) α γ (e' : XIx (Fin B.R.k) (Fin B.R.t) j ≃ Fin (B.R.N j)) (e : XIx (Fin B.R.k) (Fin B.R.t) (j + 1) ≃ Fin (B.R.N (j + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ x, (G.T E.δ E.tame E.η).entry G.ψk G.ν j d H (E.rep j (d + 1) (by omega) (π j α)) (E.rep (j + 1) d H (π (j + 1) γ)) (GlobalTheory.SymBridge.toLoc (G.q.pr.comp (incA (I.rec7 l Z))) e e' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)) = GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h j ((A.b0 j α).get hj) P) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) * GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h (j + 1) ((A.b0 (j + 1) γ).get hj') P) (B.R.N j + Formalism.L2.Col.cOf B.R j) * B.embLL (locXi A j α γ P x) :=
  fun _ hI _ _ _ _ _ _ A _ => ⟨xi_eq_xiOff_mul A, fun c _ => entry_eq_sgn_mul A hI c⟩

end GlobalTheory.QTw.Join
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormTranslateRealPointReadByPeriodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_translate_real_point_read_by_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  first | exact @GlobalTheory.AdForm.TopTranslate.top_translate | exact GlobalTheory.AdForm.TopTranslate.top_translate | (intros; apply GlobalTheory.AdForm.TopTranslate.top_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiIntegralOverNUnfold
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

theorem weilRepresentationOnFunctions_embed_mul {D : D7} {V W : HSp D} (om : Om V W) (e g : GA D V) (h : GA D W) (Φ : WO V W → ℂ) :
    om (g, h) (om (e, 1) Φ) = om (g * e, h) Φ := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem fjN_unfold : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → ∀ h₀, ∫ n in J.vN.𝓝, fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n ∂J.vN.ν = ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑 h₀
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := _root_.GlobalTheory.Unf.FB.basePoint_spec D σ B
  obtain ⟨-, -, hvM, -⟩ := _root_.GlobalTheory.Unf.VolExist.measures_exist D
  obtain ⟨vb⟩ := hvM (σ + 1) J.W₀.rank
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have hq : Quasi ψ J.W₀ B.L (Y h₀) := quasi_of_fam hY h₀
  have hTh := _root_.GlobalTheory.th_isTh D ψ s.weil.std σ J B (Y h₀) hq x₀ hx₀
  have hΦ' : IsThetaFunO ψ J.W B.V (s.om (J.d.emb0 h₀, 1) Φ) := s.weil.om_pres _ _ hΦ
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  have key := (_root_.GlobalTheory.Unf.unfold_over_N_lift D hD ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS J.vN vb s.vU s.vW x₀
    (th J ψ B (Y h₀)) hbase hTh G (s.om (J.d.emb0 h₀, 1) Φ) hG hΦ' 𝓑 h𝓑').2
  have hL : (fun n : flagN J.d => fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n) =
      fun n => th J ψ B (Y h₀) n.1 * liftS s.om s.vW.μ s.vW.𝓕 G (s.om (J.d.emb0 h₀, 1) Φ) n.1 := by
    funext n
    simp only [fjSrcKerFun, JacLev.ker, th, Step.lift, liftS_apply, zl, weilRepresentationOnFunctions_embed_mul]
    ring
  have hR' : (fun h => G h * fl ψ J.d B.V s.vS vb s.vU (th J ψ B (Y h₀)) (rat x₀) (s.om (1, h) (s.om (J.d.emb0 h₀, 1) Φ))) =
      fun h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) := by
    funext h
    rw [weilRepresentationOnFunctions_embed_mul, one_mul, hx₀, (_root_.GlobalTheory.Unf.FB.fl_base_eq_tFlat D ψ σ J B s vb vL (Y h₀) _ hq (s.weil.om_pres _ _ hΦ)).1]
  rw [hL, ← hR']
  exact key

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSpaceMovedLevelClassPointsRepresentativesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_space_moved_level_class_points_representatives : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  first | exact @GlobalTheory.ClassPtReps.isReps_stabOrd_top | exact GlobalTheory.ClassPtReps.isReps_stabOrd_top | (intros; apply GlobalTheory.ClassPtReps.isReps_stabOrd_top <;> assumption)
end

