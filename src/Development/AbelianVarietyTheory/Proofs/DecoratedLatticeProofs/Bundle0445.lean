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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLattices
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SameOrbEquivalence

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRebase

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem zero_placeModel {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 0 0 := by
  refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, ?_⟩
  · funext w; simp [heisO]
  · funext w; simp [heisO]
  · simp

theorem local_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (p : GlobalTheory.FinPl.Pl D)
    (hsp : ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (hu1 : ∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧
      incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p))
    (hu2 : ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) :
    ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧ (f ≠ 0 → comb ψ S T c f ≠ 0) := by
  obtain ⟨e, ε, he, hε, hs⟩ := hsp
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D p e ε he hε hs
  have hU : q.UnitAA := by
    unfold GlobalTheory.FinPl.SplitPt.UnitAA
    rw [hq]
    exact ⟨hu1, hu2⟩
  rw [← hq]
  obtain ⟨glS, hS1, hS2⟩ := _root_.GlobalTheory.GlEmbed.exists_gl D _ q S (Fin S.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  obtain ⟨glT, hT1, hT2⟩ := _root_.GlobalTheory.GlEmbed.exists_gl D _ q T (Fin T.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  let α : GlobalTheory.FinPl.Frame q S (Fin S.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T (Fin T.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glT, hT1, hT2⟩
  obtain ⟨ΛS, hl1, hαN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α N hN
  obtain ⟨ΛT, hl2, hβN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β N' hN'
  obtain ⟨ΛSm, hl3, hαM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α M hM
  obtain ⟨ΛTm, hl4, hβM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β M' hM'
  haveI : ΛS.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α N hN ΛS hαN
  haveI : ΛT.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β N' hN' ΛT hβN
  haveI : ΛSm.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual α M hM ΛSm hαM
  haveI : ΛTm.IsFullLattice _ := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β M' hM' ΛTm hβM
  have R := _root_.GlobalTheory.FinPl.Rebase.rebase D _ q (Fin T.rank) (Fin S.rank) ψ hψ hU S T α β M N M' N' hM hM' hN hN'
  obtain ⟨c, hc, hov⟩ := R.2 (GlobalTheory.LatPair.latInd ΛS ΛT) (GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT)
  refine ⟨c, hc, fun f hf => ?_⟩
  have hO := hov f hf
  have h1 := R.1 ΛS ΛT hαN hβN f _ hO
  refine ⟨h1.1, fun hf0 hg => hf0 ?_⟩
  obtain ⟨⟨Tm, hTm⟩, -⟩ := hO.2.2.2.2
  have hOf : GlobalTheory.FinPl.Over ψ α β M M' f (GlobalTheory.LatPair.latInd ΛSm ΛTm) f := by
    refine ⟨hM, hM', hf, GlobalTheory.LatPair.latInd_mem_SB _ _, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    rw [GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D _ q _ _ S T α β M M' hM hM' hU ΛSm ΛTm hαM hβM]
    have hv := hT'.vac
    rw [one_smul] at hv
    exact hv.symm
  have hN0 := h1.2 _ _ hOf
  rw [hg] at hN0
  have := hN0.2.2.2.2.2 0 (zero_placeModel ψ S T _ _)
  simpa using this

end GlobalTheory.VacRebase

namespace GlobalTheory.VacRebase

theorem idAt_mono' {D : D7} {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → P' v) :
    GlobalTheory.FinPl.idAt D P ≤ GlobalTheory.FinPl.idAt D P' := by
  unfold GlobalTheory.FinPl.idAt
  exact inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hp => w.2 (h _ hp)⟩ le_rfl)

theorem foldr_vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) (X : GlobalTheory.FinPl.Pl D → Prop) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p)) → (∀ p ∈ l, ¬ X p) → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T LS LT X f → GlobalTheory.FinPl.Vac ψ S T LS LT X (l.foldr (fun p g => comb ψ S T (c p) g) f) := by
  intro l
  induction l with
  | nil => intro _ _ f hf; exact hf
  | cons p l ih =>
    intro hc hX f hf
    rw [List.foldr_cons]
    have hd : ∀ x, x = p → ¬ X x := fun x hx => hx ▸ hX p List.mem_cons_self
    exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = p) X hd).2.1 (c p) (hc p List.mem_cons_self)).2 LS LT _
      (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (fun x hx => hX x (List.mem_cons_of_mem _ hx)) f hf)

theorem foldr_vac_on {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), l.Nodup → (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p) ∧ ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T (c p) f) ∧
        (f ≠ 0 → comb ψ S T (c p) f ≠ 0)) → ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ l) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ l) (l.foldr (fun p g => comb ψ S T (c p) g) f) ∧
        (f ≠ 0 → l.foldr (fun p g => comb ψ S T (c p) g) f ≠ 0) := by
  intro l
  induction l with
  | nil =>
    intro _ _ f hf
    refine ⟨⟨hf.1, ?_⟩, fun h => h⟩
    rw [_root_.GlobalTheory.FinPl.LatCong.latO_congr D S T N M N' M' hN hM hN' hM' _ (fun x hx => absurd hx List.not_mem_nil)]
    exact hf.2
  | cons p l ih =>
    intro hnd hc f hf
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hd : ∀ x, x = p → ¬ x ∈ l := fun x hx => hx ▸ hpl
    have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· = p) (· ∈ l) hd
    have hfun : (fun x => x ∈ p :: l) = fun x => x = p ∨ x ∈ l := by
      funext x; exact propext List.mem_cons
    rw [hfun] at hf ⊢
    have hf2 := (DC.2.2.2.2 M M' f hM hM').1 hf
    obtain ⟨ihv, ihn⟩ := ih (List.nodup_cons.1 hnd).2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) f hf2.2
    have hgp := foldr_vac_off hψ c (· = p) M M' l (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).1)
      (fun x hx hxp => hpl (hxp ▸ hx)) f hf2.1
    obtain ⟨hcp, hloc⟩ := hc p List.mem_cons_self
    obtain ⟨hv1, hn1⟩ := hloc _ hgp
    rw [List.foldr_cons]
    refine ⟨(DC.2.2.2.2 N N' _ hN hN').2 ⟨hv1, (DC.2.1 (c p) hcp).2 N N' _ ihv⟩, fun h0 => hn1 (ihn h0)⟩

end GlobalTheory.VacRebase

theorem GlobalTheory.VacRebase.rebase_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  intro D ψ hψ S T M N M' N' Q hM hN hM' hN' hQ hoff
  have hc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ (p ∈ Q → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧
        (f ≠ 0 → comb ψ S T c f ≠ 0)) := by
    intro p
    by_cases hp : p ∈ Q
    · obtain ⟨h1, h2, h3⟩ := hQ p hp
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.VacRebase.local_step hψ hM hN hM' hN' p h1 h2 h3
      exact ⟨c, hc1, fun _ => hc2⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hp⟩
  choose c hc1 hc2 using hc
  let l := Q.toList
  have hmem : ∀ p, p ∈ l ↔ p ∈ Q := fun p => Finset.mem_toList
  refine ⟨convList ψ S T (l.map c), ?_, fun f hf => ?_⟩
  · refine support_convList (p := GlobalTheory.FinPl.MxAt (· ∈ Q)) (fun i j => Ideal.zero_mem _)
      (fun x y hx hy i j => by rw [Matrix.add_apply]; exact Ideal.add_mem _ (hx i j) (hy i j)) ?_
    intro c' hc' x hx i j
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    exact GlobalTheory.VacRebase.idAt_mono' (fun v hv => hv ▸ (hmem p).1 hp) (hc1 p x hx i j)
  rw [comb_convList]
  have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· ∈ l) (· ∉ l) (fun x h1 h2 => h2 h1)
  have hfun : (fun x => x ∈ l ∨ x ∉ l) = fun _ => True := by
    funext x; exact propext ⟨fun _ => trivial, fun _ => em _⟩
  have hf' : GlobalTheory.FinPl.Vac ψ S T M M' (fun x => x ∈ l ∨ x ∉ l) f := by rw [hfun]; exact hf
  obtain ⟨hin, hout⟩ := (DC.2.2.2.2 M M' f hM hM').1 hf'
  obtain ⟨v1, n1⟩ := GlobalTheory.VacRebase.foldr_vac_on hψ hM hN hM' hN' c l (Finset.nodup_toList Q)
    (fun p hp => ⟨hc1 p, hc2 p ((hmem p).1 hp)⟩) f hin
  have hout' : GlobalTheory.FinPl.Vac ψ S T N N' (· ∉ l) f := by
    refine ⟨hout.1, ?_⟩
    rw [_root_.GlobalTheory.FinPl.LatCong.latO_congr D S T N M N' M' hN hM hN' hM' _ (fun x hx => by
      obtain ⟨a, b⟩ := hoff x (fun h => hx ((hmem x).2 h)); exact ⟨a.symm, b.symm⟩)]
    exact hout.2
  have v2 := GlobalTheory.VacRebase.foldr_vac_off hψ c (· ∉ l) N N' l (fun p _ => hc1 p) (fun p hp h => h hp) f hout'
  refine ⟨?_, n1⟩
  rw [← hfun]
  exact (DC.2.2.2.2 N N' _ hN hN').2 ⟨v1, v2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevPin
open GlobalTheory.FinPl (idAt MxAt grpAt SplitPt)

variable {D : D7}

theorem idAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, P w → P' w) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mxAt_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {m n : ℕ} (w : Mx D m n)
    (h : IsHalf (q.e + cA D q.e) w) : MxAt P w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  refine idAt_mono (fun w (hw : w = q.v) => hw ▸ hP) (GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_)
  rw [← h2]
  exact h i j

theorem exists_fold (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) {ι : Type} (c : ι → WO S T →₀ ℂ)
    (hc : ∀ i, ∀ w ∈ (c i).support, MxAt P w) (l : List ι) : ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, MxAt P w) ∧
      ∀ f, comb ψ S T c' f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun w hw => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hw)
      exact fun i j => zero_mem _
    · rw [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul,
        GlobalTheory.MixPer.heisO_zero]
      rfl
  | cons i l ih =>
    obtain ⟨c', h1, h2⟩ := ih
    obtain ⟨c'', h3, h4⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c i) c'
    refine ⟨c'', fun w hw => ?_, fun f => by rw [h4, h2]; rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h3 w hw
    exact fun a b => add_mem (hc i x hx a b) (h1 y hy a b)

theorem mxAt_cast {F : ℕ → HSp D} {T : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {s j : ℕ} (h : s = j) (x : WO (F s) T →₀ ℂ)
    (hx : ∀ w ∈ x.support, MxAt P w) : ∀ w ∈ (cast (congrArg (fun n => WO (F n) T →₀ ℂ) h) x).support, MxAt P w := by
  subst h
  exact hx

def conjHom {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) :
    GL (Fin N) k →* GL Y k where
  toFun g := ⟨F.γ * g.val * F.β, F.γ * (g⁻¹).val * F.β, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc g.val,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, F.γβ], by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc (g⁻¹).val,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (1 : Matrix (Fin N) (Fin N) k) * F.β = 1
    rw [Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (g.val * h.val) * F.β = (F.γ * g.val * F.β) * (F.γ * h.val * F.β)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul])

theorem conj_iff {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y)
    (M : GL (Fin N) k) (x : GL Y k) : M.val = F.β * x.val * F.γ ↔ x = conjHom F M := by
  constructor
  · intro h
    refine Units.ext ?_
    change x.val = F.γ * M.val * F.β
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  · rintro rfl
    change M.val = F.β * (F.γ * M.val * F.β) * F.γ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) : Subgroup G :=
  J.comap ((conjHom F).comp ρ)

theorem mem_frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) (g : G) :
    g ∈ frameSub ρ F J ↔ ∀ x : GL Y k, (ρ g).val = F.β * x.val * F.γ → x ∈ J := by
  constructor
  · intro h x hx
    rw [(conj_iff F _ x).1 hx]
    exact h
  · intro h
    exact h _ ((conj_iff F _ _).2 rfl)

theorem under_inj {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hT : GlobalTheory.Core.Mi.IsTypePlaces Pg) {PP PP' : Formalism.L2.DIV.Pl D.host.E}
    (h : PP ∈ Pg) (h' : PP' ∈ Pg) (e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) : PP = PP' := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    have := hT.1 PP h
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using this
  obtain ⟨Q, _, hu⟩ := hT.2 _ hm
  exact (hu PP ⟨h, rfl⟩).trans (hu PP' ⟨h', e.symm⟩).symm

end GlobalTheory.LevPin

namespace GlobalTheory.LevPin

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_locComb {a : XGeo D} {y : YRat a} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) {N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)} {β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)}
    {b : ∀ j, GA D (Yc D j)} {bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k}
    (Y : LocY l y N β b bas) (ν : Measure l.k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (eg : ∀ j, WO (Yc D j) (Yc D (j + 1)) →₀ ℂ) (egT : WO (Yc D (l.s + 1)) D.sp.X' →₀ ℂ)
      (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ),
      (∀ j a' (H : j + a' = l.s), (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) (eg j)
        ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      (ofSplit l.q).IsCombAt ψ (Y.FY (l.s + 1) 0 rfl) l.FT egT (S.T (Fin D.R.t)).PhiTop ∧
      (∀ j a' (H : j + 1 + a' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) (cg j)
        ((S.T (Fin D.R.t)).entry S.ψ ν j a' H 1 1)) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl) (cg l.s)
        (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX (l.s + 1) le_rfl) l.FM (cg (l.s + 1))
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) ∧
      (∀ j, ∀ w ∈ (eg j).support, IsHalf (l.q.e + cA D l.q.e) w) ∧ (∀ j, ∀ w ∈ (cg j).support, IsHalf (l.q.e + cA D l.q.e) w) := by
  have keyE : ∀ j, ∃ c : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ a' (H : j + a' = l.s),
      (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) c ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j ≤ l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY j (l.s - j + 1) (by omega))
        (Y.FY (j + 1) (l.s - j) (by omega)) ((S.T (Fin D.R.t)).Phi j (l.s - j) (by omega))
      refine ⟨c, fun a' H => ?_, hc.1⟩
      obtain rfl : a' = l.s - j := by omega
      exact hc
    · exact ⟨0, fun a' H => by omega, by simp⟩
  choose eg heg sEg using keyE
  obtain ⟨egT, hegT⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY (l.s + 1) 0 rfl) l.FT
    (S.T (Fin D.R.t)).PhiTop
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX (l.s + 1) le_rfl) l.FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have keyC : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = l.s → HEq c c₁) ∧ (j = l.s + 1 → HEq c c₂) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j < l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX j (by omega)) (l.FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j (l.s - j - 1) (by omega) 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega, hc.1⟩
      obtain rfl : c'' = l.s - j - 1 := by omega
      exact hc
    · by_cases h1 : j = l.s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega, h₁.1⟩
      · by_cases h2 : j = l.s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl, h₂.1⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim, by simp⟩
  choose cg k1 k2 k3 k4 using keyC
  refine ⟨eg, egT, cg, heg, hegT, k1, ?_, ?_, sEg, k4⟩
  · rw [eq_of_heq (k2 l.s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (l.s + 1) rfl)]; exact h₂

end GlobalTheory.LevPin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitReps
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.CosExt


set_option maxHeartbeats 4000000 in
theorem exists_qExt_cos : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∀ (C : Type) [Fintype C] (cs : C → XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k), (∀ y y', SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk (cs y')) → y = y') → (∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹, ∃ y, SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk z)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M ∧ (∃ e : C ≃ E.Ch (G.s + 1), ∀ y, E.cos (e y) = Submodule.Quotient.mk (cs y)) ∧ ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j)) := by
  intro D c v B PP G χ hc δ hδ η hη hμ A hA M hM C _ cs hinj hall
  obtain ⟨E, rfl, rfl, rfl, rfl, -⟩ := GlobalTheory.QTw.Inh.exists_ext_of_reps D c v B PP G χ hc δ hδ η hη hμ A hA M hM
  classical
  let Ch' : ℕ → Type := fun j => if j = G.s + 1 then C else if G.s + 1 + 1 < j then Unit else E.Ch j
  have eC : Ch' (G.s + 1) = C := if_pos rfl
  have eE : ∀ j, j ≤ G.s + 1 + 1 → j ≠ G.s + 1 → Ch' j = E.Ch j := fun j h1 h2 => by
    simp only [Ch', if_neg h2, if_neg (not_lt.2 h1)]
  have eU : ∀ j, G.s + 1 + 1 < j → Ch' j = Unit := fun j h1 => by
    simp only [Ch', if_neg (show j ≠ G.s + 1 by omega), if_pos h1]
  let fC : ∀ j, Fintype (Ch' j) := fun j => by
    simp only [Ch']; split_ifs <;> infer_instance
  let rep' : ∀ j d, j + d = G.s → Ch' j → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k :=
    fun j d h x => E.rep j d h (cast (eE j (by omega) (by omega)) x)
  let cos' : Ch' (G.s + 1) → (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k) ⧸ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ E.M) :=
    fun y => Submodule.Quotient.mk (cs (cast eC y))
  have hpen : ∀ (α : Ch' G.s) (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX G.s (by omega)) (G.FX (G.s + 1) le_rfl) e
      ((G.T E.δ E.tame E.η).xiPen (box _ (G.ϖ ^ E.M)) (rep' G.s 0 rfl α) (cos' y)) :=
    fun α y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  have htop : ∀ (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX (G.s + 1) le_rfl) G.FM e
      ((G.T E.δ E.tame E.η).xiTop (box _ (G.ϖ ^ E.M)) G.ψk G.ν (-1) (cos' y)) :=
    fun y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  choose dPen hdPen using hpen
  choose dTop hdTop using htop
  let dL' : ∀ j, Ch' j → Ch' (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ := fun j =>
    if h : j + 1 ≤ G.s then fun α γ => E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
    else if h' : j = G.s then (by subst h'; exact dPen)
    else if h'' : j = G.s + 1 then (by subst h''; exact fun y _ => dTop y)
    else fun _ _ => 0
  let wt' : ∀ j, Ch' j → ℂ := fun j =>
    if h : j = G.s + 1 then (by subst h; exact fun y => (E.idx (G.s + 1) : ℂ) *
      (Nat.card {yb | SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (cos' y) yb} : ℂ))
    else if h' : j ≤ G.s then fun α => E.wt j (cast (eE j (by omega) (by omega)) α)
    else fun _ => (E.idx (G.s + 1 + 1) : ℂ)
  let εL' : ∀ j, Ch' j → GA D (c.V j) →₀ ℂ := fun j =>
    if h : j ≤ G.s then fun α => E.εL j (cast (eE j (by omega) (by omega)) α) else fun _ => 0
  let E' : QExt G χ :=
    { δ := E.δ, tame := E.tame, η := E.η, unr := E.unr, mu_comp := E.mu_comp, A := E.A, reps := E.reps, Ch := Ch', fC := fC, rep := rep'
      rep_bij := fun j d h => (E.rep_bij j d h).comp
        ((Equiv.cast (eE j (by omega) (by omega))).bijective.bijOn_univ)
      M := E.M, adapt := E.adapt, cos := cos'
      cos_inj := fun y y' h => (Equiv.cast eC).injective (hinj _ _ h)
      cos_all := fun z hz => by
        obtain ⟨y, hy⟩ := hall z hz
        exact ⟨cast eC.symm y, by simpa [cos'] using hy⟩
      one := (Fintype.card_congr (Equiv.cast (eE (G.s + 1 + 1) le_rfl (by omega)))).trans E.one
      eL := E.eL, eLT := E.eLT, eL_at := E.eL_at, eLT_at := E.eLT_at, dL := dL'
      dL_mid := fun j d H α γ => by
        have := E.dL_mid j d H (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
        have e : dL' j α γ = E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ) := by
          simp only [dL']; rw [dite_eq_left (show j + 1 ≤ G.s by omega)]
        rw [e]; exact this
      dL_pen := fun α y => by
        have e : dL' G.s α y = dPen α y := by
          simp only [dL']; rw [dite_eq_right (by omega), dite_eq_left trivial]
        rw [e]; exact hdPen α y
      dL_top := fun y u => by
        have e : dL' (G.s + 1) y u = dTop y := by
          simp only [dL']; rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left trivial]
        rw [e]; exact hdTop y
      εL := εL'
      εL_at := fun j ρ hρ d h α => by
        obtain ⟨e, h1, h2⟩ := E.εL_at j ρ hρ d h (cast (eE j (by omega) (by omega)) α)
        refine ⟨e, h1, ?_⟩
        rw [← h2]; simp only [εL']; rw [dite_eq_left (show j ≤ G.s by omega)]
      εL_zero := fun α => by
        simp only [εL']; rw [dite_eq_left (Nat.zero_le _)]; exact E.εL_zero _
      idx := E.idx, idx_mid := E.idx_mid, idx_top := E.idx_top, m := E.m, haar := E.haar, wt := wt'
      wt_mid := fun j d h α => by
        rw [← E.wt_mid j d h (cast (eE j (by omega) (by omega)) α)]
        simp only [wt']; rw [dite_eq_right (show j ≠ G.s + 1 by omega), dite_eq_left (show j ≤ G.s by omega)]
      wt_pen := fun y => by simp only [wt']; rw [dite_eq_left trivial]
      wt_top := fun u => by simp only [wt']; rw [dite_eq_right (by omega), dite_eq_right (by omega)] }
  refine ⟨E', rfl, rfl, rfl, rfl, ⟨Equiv.cast eC.symm, fun y => ?_⟩, fun j hj => ⟨(Equiv.cast (eU j hj)).unique⟩⟩
  simp [E', cos']

end GlobalTheory.QTw.CosExt
end
end

