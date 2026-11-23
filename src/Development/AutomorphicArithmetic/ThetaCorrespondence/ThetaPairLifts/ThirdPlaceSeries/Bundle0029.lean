module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamified
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeTame
theorem typeTame_of_ramified_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : CharacterChoiceData hL D) (S : Reading P.T) (hT : IsFaithfulReading P S)
    (i : D.nd.Loc) (w : PlE D.host) (hw : IsSplitPl D.host w)
    (hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k))
    (htame : GlobalTheory.SplitWeil.IsTame (S i w hw).mu)
    (hram : ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu) : TypeTame S i w hw := by
  refine ⟨htame, hram, fun Q => ?_⟩
  obtain ⟨h1, h2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hcomp := hT.mu i w hw j hj
  obtain ⟨v, hov, hvq⟩ := _root_.GlobalTheory.GeoUnder.exists_under_in_qPl D _ w hg (_root_.GlobalTheory.VTypeTame.ramified_of_isComp _ _ w _ hcomp hram)
  obtain ⟨s, ξ, hsv, hcs, hlp⟩ := P.H.level.para i j hj v hvq
  obtain ⟨f, hfI, hfT, hf0⟩ : ∃ f, f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) ∧
      f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ f ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    rw [P.H.av.typeV] at hy
    refine ⟨(P.M.loc i).real y, hy, ?_, ?_⟩
    · rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
    · intro h; exact hy0 ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨K, θ, hKm, hθ, hKi, hθo, hχθ⟩ := _root_.GlobalTheory.ParaLevel.exists_parahoric_char _ _ s D.R.r _ _ ξ hlp hcs.1
  have hfK : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc D.R.nV κ ∈ K,
      NG.rt D.host.E D.R.nV κ f = ((θ ⟨s.loc D.R.nV κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hJ : κ ∈ (P.M.loc i).J := (hlp.mem κ hκ).2 ((hKm _).1 h)
    rw [← hχθ κ hκ hJ h]
    exact hfT.2 ⟨κ, hJ⟩
  have hmu_eq : ∀ g (hg : NG.ParaRT s D.R.r g) (d : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ),
      (d : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r g →
      θ ⟨g, (hKm g).2 hg⟩ = ξ d := fun g hg d hd => hθ g _ d hd
  rcases _root_.GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w (hsv ▸ hov) with hsw | hconj
  · subst hsw
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i s hw Q
    obtain ⟨u, hu0, hu⟩ := _root_.GlobalTheory.LocVec.main _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _ (hT.rep i s hw Q) c hc hci
      K θ hKi hθo f hfI hf0 hfK
    refine ⟨u, hu0, _root_.GlobalTheory.SameParahoric.isParahoricVec_of_eigen _ s D.R.r D.R.t _ ξ _ c hc hci hcomp.1 hcs.1 (fun k => (hcs.2 k).trans (hcomp.2 k).symm) u ?_⟩
    intro g hg d hd
    rw [← hmu_eq g hg d hd]
    exact hu g _
  · obtain ⟨hw', hci'⟩ := _root_.GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w hconj
    subst hw'
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q
    obtain ⟨K', θ', hK'i, hθ'o, hK'iff, hθ'eq, hK'of⟩ := _root_.GlobalTheory.TypeTame.exists_conj_level _ _ s K θ hKi hθo
    have hfK' : ∀ κ, TrivOutside {(GlobalTheory.TypeTame.conjSP s).v} κ → ∀ h' : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ ∈ K',
        NG.rt D.host.E D.R.nV κ f = ((θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ, h'⟩ : ℂˣ) : ℂ) • f := by
      intro κ hκ h'
      have h := (hK'iff κ).1 h'
      rw [hθ'eq κ h h']
      exact hfK κ hκ h
    obtain ⟨u, hu0, hu⟩ := _root_.GlobalTheory.LocVec.main _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) (GlobalTheory.TypeTame.conjSP s) _
      (hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q) c hc hci K' θ' hK'i hθ'o f hfI hf0 hfK'
    have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
      rw [← P.chr.muC i j hj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
    refine _root_.GlobalTheory.ConjParahoric.exists_parahoricVec _ (GlobalTheory.TypeTame.conjSP s) D.R.r D.R.t _ ξ _ c hc hci hcomp.1 htame hcs.1 ?_ u hu0 ?_
    · intro k
      have e : Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k =
          Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHom.ofClass D.host.conj) k) := by
        apply Units.ext
        exact hci' (k : D.host.E)
      have e2 := hcs.2 (Units.map (MonoidHom.ofClass D.host.conj) k)
      rw [e, e2, hcomp.2 k]
      exact hcsd.1 _ _ hconj k
    · intro g h hg hh d hd
      obtain ⟨h', e⟩ := hK'of g ((hKm g).2 hg) h hh
      rw [← hmu_eq g hg d hd, ← e]
      exact hu h h'
end GlobalTheory.TypeTame
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVecBlockCharFixedPlace
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open Filter Topology
namespace GlobalTheory.TypeBlockFix
variable {F : Type} [Field F] [NumberField F] {F' : Type} [Field F'] [NumberField F']
section loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end loc
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open ValuativeRel
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open Filter Topology
end GlobalTheory.TypeBlockFix
open GlobalTheory.TypeBlockFix in
theorem GlobalTheory.typeVec_blockChar_fixedPlace_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hsw _hT c hc hci Q
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i Q)
  rw [P.H.av.typeV] at hy
  have hfT : (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  refine ⟨(P.M.loc i).real y, hy, fun h0 => hy0 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)), ?_⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hLv⟩ := P.H.level.uni i j hj k v s hsw
  intro x hx hblk
  set G := s.loc D.R.nV x with hG
  set h := Matrix.GeneralLinearGroup.map c.toRingHom G with hh
  have hent : ∀ a b, h.val a b = c (G.val a b) := fun a b => rfl
  have hient : ∀ a b, (h⁻¹).val a b = c ((G⁻¹).val a b) := by
    intro a b; rw [hh, ← map_inv]; rfl
  have hle : ∀ y, ValuativeRel.valuation _ (c y) ≤ 1 → Valued.v y ≤ 1 := fun y hy' =>
    (v_map_le_one_iff _ _ c hc y).1 ((complRel_le_one _ _).1 hy')
  have hlt : ∀ y, ValuativeRel.valuation _ (c y) < 1 → Valued.v y < 1 := fun y hy' =>
    (v_map_lt_one_iff _ _ c hc y).1 ((complRel_lt_one _ _).1 hy')
  have hI : ∀ a b, Valued.v (G.val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hent]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO hblk.1 a b)
  have hI' : ∀ a b, Valued.v ((G⁻¹).val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hient]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO ((KO _ _).inv_mem hblk.1) a b)
  have hcol : ∀ a (b : Fin D.R.nV), b.val < D.R.r → a ≠ b → Valued.v (G.val a b) < 1 := by
    intro a b hb hab
    refine hlt _ ?_
    have := hblk.2 a ⟨b.val, hb⟩
    rw [← hent]
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) a b) < 1 at this
    rw [Matrix.one_apply_ne hab, sub_zero] at this
    exact this
  have hdiag : ∀ (b : Fin D.R.nV), b.val < D.R.r → Valued.v (G.val b b - 1) < 1 := by
    intro b hb
    refine hlt _ ?_
    have := hblk.2 b ⟨b.val, hb⟩
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val b b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) b b) < 1 at this
    rw [Matrix.one_apply_eq, hent] at this
    rwa [map_sub, map_one]
  have hpara : NG.ParaRT s D.R.r G := by
    refine ⟨mem_GLint_of_entries _ G (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI a b))
      (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI' a b)), ?_⟩
    · intro a b ha hb
      exact hcol a b hb (fun e => by rw [e] at ha; omega)
  have huni : NG.UniRT s D.R.r G := by
    refine ⟨hpara, fun a b ha hb => ⟨fun hab => hcol a b hb (fun e => by rw [e] at hab; omega), fun e => ?_⟩⟩
    subst e; exact hdiag a ha
  have hmem : x ∈ (P.M.loc i).J := (hLv.mem x hx).2 huni
  have hcdet : c (NG.detDD s D.R.r G) = (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {a : Fin D.R.nV // D.R.r ≤ a.val} :=
      { toFun := fun b => ⟨Fin.natAdd D.R.r b, by simp⟩
        invFun := fun a => ⟨a.1.val - D.R.r, by have h1 : a.1.val < D.R.r + D.R.t := a.1.2; omega⟩
        left_inv := fun b => by ext; simp
        right_inv := fun a => by ext; simp; have := a.2; omega }
    rw [NG.detDD, show c (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det =
      c.toRingHom (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det from rfl,
      RingHom.map_det, ← Matrix.det_submatrix_equiv_self e]
    congr 1
  have hdet : NG.detDD s D.R.r G ≠ 0 := by
    intro h0
    exact (det_ne_zero_of_mem_blockGrp _ _ _ _ hblk) (hcdet.symm.trans (by rw [h0, map_zero]))
  refine (hfT.2 ⟨x, hmem⟩).trans ?_
  congr 1
  rw [hLv.chr x hmem hx (Units.mk0 _ hdet) rfl]
  have hsd : Valued.v (NG.supDiag s D.R.r G) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · exact hcol a b hab.2 (fun e => by rw [e] at hab; omega)
    · simp
  rw [hψ.1 _ hsd, one_mul, comp_agree _ s _ ξ _ c hc hci hξ (hS.mu i s.w hw j hj)]
  exact (GlobalTheory.BlockType.blockChar_eq _ _ _ hcdet).symm
end
end
end

