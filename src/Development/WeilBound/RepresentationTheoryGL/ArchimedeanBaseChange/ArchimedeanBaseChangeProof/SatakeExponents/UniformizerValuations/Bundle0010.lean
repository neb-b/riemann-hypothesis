module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0748
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemDCand
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical
set_option synthInstance.maxHeartbeats 200000
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemDd

theorem cand_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} {F₀ : Frame0 hR π S} {d} {i} {s₁ s₂ Pa Pb D} (c : F₀.Cand d i s₁ s₂ Pa Pb D) :
    (∀ τ, ∑ j, Pa.m j τ = mOf (F₀.A i).χa τ) ∧ (∀ τ, ∑ j, Pb.m j τ = mOf (F₀.A i).χb τ) := by
  obtain ⟨G, hG, h0, -⟩ := c.vec
  have h := PairNe_holds _ _ _ _ _ G hG h0
  exact ⟨fun τ => lemD _ _ s₁ Pa τ _ c.ctx.g₁ c.ctx.u₁ c.ctx.t₁ (c.inf₁ τ) h.1,
    fun τ => lemD _ _ s₂ Pb τ _ c.ctx.g₂ c.ctx.u₂ c.ctx.t₂ (c.inf₂ τ) h.2⟩

end PositivityTheory.Rg.BcB.F.LemDd

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalExistenceOfUnramified
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Loc0 (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (μ : HChar E) (Sec : Set (Pl E)) (d₀ : LocData E n) : Prop where
  hSec : IsSection Sec
  inert : ∀ w, ¬ IsSplitAt w → w ∈ Sec
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  S_le : ∀ w ∈ S, IsSplitAt w → w ∈ d₀.S₀
  bad : ∀ w ∈ d₀.Bad, w ∈ Sec ∧ (¬ IsSplitAt w → ¬ IsUnramU π w)
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → IsUnramU π w ∧ μ.UnrAt w
  levFam : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) d₀.KU
  level : ∀ K' : ∀ w : Pl E, Subgroup (UL n w), (∀ w, K' w ≤ d₀.KU w) → HasLevel Sec π K'
  fix : ∀ a ≤ n, ∀ w ∈ d₀.Bad, Match n a (n - a) w (μ.loc w) (U.lone (d₀.KB w)) (d₀.fix a w)
  mok₀ : MLM.MOk d₀
  off : ∀ w, w ∉ d₀.Bad → d₀.KB w = KL n w ∧ ∀ a, d₀.fix a w = 0

theorem isLevel_KL (w : Pl E) {K : Subgroup (UL n w)} (h : GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) K) :
    GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨Subgroup.isOpen_mono h.2.1 h.1, le_rfl, fun _ hk => hk⟩

theorem local_existence_of_unramified (hSec : SecEx) (hU : UnifEx) (hLev : LevelEx) (hS : SplitEx) (hB : BadEx2) (hE : GlobalTheory.BCT.Unr E)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hun : ∀ᶠ w : Pl E in cofinite, IsUnramU π w) (S : Finset (Pl E))
    (hS1 : S.card ≤ 1) (μ : HChar E) (hin : ∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) (hae : ∀ᶠ w : Pl E in cofinite, μ.UnrAt w)
    (hop : ∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)) : ∃ Sec d₀, Loc0 π S μ Sec d₀ := by
  set S₀ := S.filter IsSplitAt with hS₀
  obtain ⟨Sec, hsec, hS₀S, hinS⟩ := hSec E S₀ ((Finset.card_filter_le _ _).trans hS1)
  have hfin : {w : Pl E | ¬ (IsUnramU π w ∧ μ.UnrAt w)}.Finite := Filter.eventually_cofinite.1 (hun.and hae)
  set Bad := (hfin.toFinset.filter (· ∈ Sec)) \ S₀ with hBad
  have memBad : ∀ w, w ∈ Bad ↔ (¬ (IsUnramU π w ∧ μ.UnrAt w) ∧ w ∈ Sec) ∧ w ∉ S₀ := fun w => by
    simp only [hBad, Finset.mem_sdiff, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  obtain ⟨K₀, m, -, hm, hfam, hgood, hcong, hlev⟩ := hLev E n π hπ Sec hsec (S₀ ∪ Bad) 1
  choose ϖ hϖ using hU E hE
  have h1 : ∀ w : Pl E, ∃ (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (e : GLw n w → ℂ)
      (L : ∀ a : ℕ, Subgroup (GLw a w × GLw (n - a) w)), w ∈ S₀ →
      K'.subgroupOf (UL n w) = K₀ w ∧ IsOpen (K' : Set (GLw n w)) ∧ K' ≤ KGL w (n := n) ∧
      (∀ k ∈ KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') ∧ (∀ x ∈ X, x ∈ KGL w (n := n)) ∧ (∀ k ∈ KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') ∧
      IsHk K' e ∧ ∀ a (ha : a ≤ n), IsPairLevel (L a) ∧ ∀ y ∈ L a, y ∈ leviOf (Nat.add_sub_of_le ha) w K' ∧
        μ.loc w (GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) = 1 := fun w => by
    by_cases hw : w ∈ S₀
    · obtain ⟨K', X, e, L, h⟩ := hS E n w (Finset.mem_filter.1 hw).2 (μ.loc w) (hop w) m hm (K₀ w)
        (hcong w (Or.inr (Finset.mem_union_left _ hw)))
      exact ⟨K', X, e, L, fun _ => h⟩
    · exact ⟨⊥, ∅, 0, fun _ => ⊥, fun h => absurd h hw⟩
  choose K' X e LS hSp using h1
  let fx : ∀ (a : ℕ) (w : Pl E), LF a (n - a) w := fun a w => fixFn n a w (μ.loc w) m (K₀ w)
  have h2 : ∀ (a : ℕ) (w : Pl E), ∃ L : Subgroup (GLw a w × GLw (n - a) w), a ≤ n → w ∈ Bad →
      IsPairLevel L ∧ IsHecke L (fx a w) ∧ Match n a (n - a) w (μ.loc w) (U.lone (K₀ w)) (fx a w) := fun a w => by
    by_cases hw : a ≤ n ∧ w ∈ Bad
    · obtain ⟨L, h⟩ := hB E hE n a hw.1 w (μ.loc w) (hop w) m hm (K₀ w) (hcong w (Or.inr (Finset.mem_union_right _ hw.2)))
      exact ⟨L, fun _ _ => h⟩
    · exact ⟨⊥, fun h h' => absurd ⟨h, h'⟩ hw⟩
  choose LB hBd using h2
  let d : LocData E n := ⟨∅, S₀, Bad, fun w => μ.loc w, ϖ, 0, K', X, e, fun a w => if w ∈ S₀ then LS w a else LB a w,
    fun a w => if w ∈ Bad then fx a w else 0, fun _ => 1, fun w => if w ∈ Bad then K₀ w else KL n w⟩
  have dK : ∀ w ∈ Bad, d.KB w = K₀ w := fun w hw => if_pos hw
  have dF : ∀ a, ∀ w ∈ Bad, d.fix a w = fx a w := fun a w hw => if_pos hw
  have hKU : ∀ w, d.KU w = if w ∈ S₀ ∪ Bad then K₀ w else KL n w := fun w => by
    show (if w ∈ (∅ : Finset (Pl E)) then _ else if w ∈ S₀ then (K' w).subgroupOf (UL n w) else if w ∈ Bad then (if w ∈ Bad then K₀ w else KL n w) else KL n w) = _
    by_cases a1 : w ∈ S₀
    · simp [a1, (hSp w a1).1]
    · by_cases a2 : w ∈ Bad <;> simp [a1, a2]
  have hgd : ∀ w ∈ Sec, w ∉ S₀ → w ∉ Bad → IsUnramU π w ∧ μ.UnrAt w := fun w a1 a2 a3 => by
    by_contra h
    exact a3 ((memBad w).2 ⟨⟨h, a1⟩, a2⟩)
  refine ⟨Sec, d, hsec, hinS, ⟨⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, Finset.disjoint_sdiff⟩,
    fun w => (hϖ w).1.1, fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => ?_, fun a ha w hw => ?_,
    fun a ha w hw y hy => ?_, fun a ha w hw => ?_⟩, rfl, fun _ => rfl, hϖ,
    fun w hw => ⟨hS₀S w hw, (Finset.mem_filter.1 hw).2⟩, fun w hw hs => Finset.mem_filter.2 ⟨hw, hs⟩,
    fun w hw => ⟨((memBad w).1 hw).1.2, fun hs hu => ((memBad w).1 hw).1.1 ⟨hu, hin w hs⟩⟩, hgd, ⟨fun w => ?_, ?_⟩,
    fun K'' hK'' => ?_, fun a ha w hw => by rw [dK w hw, dF a w hw]; exact (hBd a w ha hw).2.2,
    ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => ?_, fun w hw hs => ⟨by rw [dK w hw]; exact hfam.1 w, fun a ha => ?_⟩,
      fun w hw hs => ⟨m, hm, by rw [dK w hw]; exact hfam.1 w, fun γ => ?_, fun a ha => ?_⟩⟩,
    fun w hw => ⟨if_neg hw, fun a => if_neg hw⟩⟩
  · obtain ⟨-, b1, b2, b3, b4, b5, b6, -⟩ := hSp w hw
    exact ⟨b1, b2, b3, b4, b5, b6⟩
  · show IsPairLevel (if w ∈ S₀ then LS w a else LB a w)
    by_cases a1 : w ∈ S₀
    · rw [if_pos a1]; exact ((hSp w a1).2.2.2.2.2.2.2 a ha).1
    · rw [if_neg a1]; exact (hBd a w ha ((Finset.mem_union.1 hw).resolve_left a1)).1
  · have hy' : y ∈ (if w ∈ S₀ then LS w a else LB a w) := hy
    rw [if_pos (show w ∈ S₀ from hw)] at hy'
    exact ((hSp w hw).2.2.2.2.2.2.2 a ha).2 y hy'
  · rw [dF a w hw]
    show IsHecke (if w ∈ S₀ then LS w a else LB a w) (fx a w)
    rw [if_neg ((memBad w).1 hw).2]
    exact (hBd a w ha hw).2.1
  · rw [hKU]
    split_ifs
    · exact hfam.1 w
    · exact isLevel_KL w (hfam.1 w)
  · filter_upwards [(S₀ ∪ Bad).eventually_cofinite_notMem] with w hw
    rw [hKU, if_neg hw]
  · obtain ⟨φ, a1, a2, a3⟩ := hlev (fun w => if w ∈ Sec then K'' w else K₀ w) fun w => by
      split_ifs with hw
      · refine (hK'' w).trans ?_
        rw [hKU]
        split_ifs with hR
        · exact le_rfl
        · rw [Finset.mem_union, not_or] at hR
          rw [hgood w (hgd w hw hR.1 hR.2).1 (by rw [Finset.mem_union, not_or]; exact hR)]
      · exact le_rfl
    exact ⟨φ, a1, a2, fun w hw x hx hk => a3 w hw x hx (by simpa only [if_pos hw] using hk)⟩
  · have hs : IsSplitAt w := (Finset.mem_filter.1 hw).2
    refine ⟨hs, fun g => by simp [UL, hs], ?_⟩
    show GlobalTheory.BCT.IsLevel _ _ ((K' w).subgroupOf (UL n w))
    rw [(hSp w hw).1]
    exact hfam.1 w
  · rw [dF a w hw, dK w hw]
    show fixFn n a w (μ.loc w) m (K₀ w) = _
    rw [fixFn, dite_eq_left ha, if_pos hs]
  · rw [dK w hw]
    exact hcong w (Or.inr (Finset.mem_union_right _ hw)) γ
  · rw [dF a w hw, dK w hw]
    show fixFn n a w (μ.loc w) m (K₀ w) = _
    rw [fixFn, dite_eq_left ha, if_neg hs]

end PositivityTheory.Rg.BcB.F.Ex0

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchTorusOfTwistedMatching
section
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.TorusMatching

def MatchLin2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a b : ℕ) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (J : Type) [Fintype J] (c : J → ℂ) (f : J → UL n w → ℂ)
    (φ : J → GLw a w × GLw b w → ℂ),
    (∀ j, IsLocallyConstant (f j) ∧ HasCompactSupport (f j) ∧ IsLocallyConstant (φ j) ∧ HasCompactSupport (φ j)) →
    (∀ j, Match n a b w μ (f j) (φ j)) → Match n a b w μ (fun γ => ∑ j, c j * f j γ) (fun y => ∑ j, c j * φ j y)

theorem matchLin2 : MatchLin2 := GlobalTheory.CompanionTheory.MatchLinear.matchLin

theorem isHecke_lc {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {L : Subgroup G}
    (ho : IsOpen (L : Set G)) {f : G → ℂ} (h : IsHecke L f) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
  have hop : IsOpen {y : G | x⁻¹ * y ∈ L} := ho.preimage (continuous_const.mul continuous_id)
  filter_upwards [hop.mem_nhds (by simp [L.one_mem] : x ∈ {y : G | x⁻¹ * y ∈ L})] with y hy
  have := (h.2 _ hy x).2
  rwa [mul_inv_cancel_left] at this

def MatchTOf2 : Prop := M4 → FUMul → DcosMul → MatchLin2 → MatchT

theorem matchTOf2 : MatchTOf2 := by
  intro hM4 hFU hD hLin E _ _ _ hU w hw n a ha b hb ϖ hϖ J _ c x hx k hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨J', _, c', x', hx', e1, e2⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim hFU hD hU hw a hb hϖ c x hx k
  have hc : Continuous (cj w) := (_root_.GlobalTheory.ConjAtPlace.main E hU w).1
  have hoU := GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b
  have hoG := GlobalTheory.CompanionTheory.MatchPow.iwahori_pair_open a (n - a) w
  have hm := hLin E hU n a (n - a) w 1 J' (fun j => GlobalTheory.CompanionTheory.MatchPow.alpha n w b ^ k * c' j)
    (fun j => fU n w b ϖ (lOf (x' j))) (fun j => phiX n w b ϖ (x' j) a)
    (fun j => ⟨isHecke_lc hoU (GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ _ hc), (GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ _ hc).1,
      isHecke_lc hoG (GlobalTheory.CompanionTheory.MatchPow.phiX_hecke n w b ϖ _ a), (GlobalTheory.CompanionTheory.MatchPow.phiX_hecke n w b ϖ _ a).1⟩)
    (fun j => (hM4 E hU w hw n a ha b hb ϖ hϖ (x' j) (hx' j).1 (hx' j).2).1)
  have hcon : cR n a w b * GlobalTheory.CompanionTheory.MatchPow.beta a (n - a) w = GlobalTheory.CompanionTheory.MatchPow.alpha n w b := by
    have h1 : (((iwGL a w).relIndex (GlobalTheory.LFun.KGL w (n := a)) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.CompanionTheory.MatchPow.iw_idx a w)
    have h2 : (((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n := (n - a))) : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (GlobalTheory.CompanionTheory.MatchPow.iw_idx (n - a) w)
    unfold cR GlobalTheory.CompanionTheory.MatchPow.beta GlobalTheory.CompanionTheory.MatchPow.alpha
    rw [GlobalTheory.CompanionTheory.MatchPow.relIndex_prod, Nat.cast_mul]
    field_simp
  have ef : lpow (iwU n w b) (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) (k + 1) =
      fun γ => ∑ j, (GlobalTheory.CompanionTheory.MatchPow.alpha n w b ^ k * c' j) * fU n w b ϖ (lOf (x' j)) γ := by
    rw [e1]
    funext γ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have eφ : (fun y => cR n a w b ^ (k + 1) * ∑ s, mpow w (entT n w ϖ a c x s) (k + 1) y) =
      fun y => ∑ j, (GlobalTheory.CompanionTheory.MatchPow.alpha n w b ^ k * c' j) * phiX n w b ϖ (x' j) a y := by
    funext y
    simp only [e2, GlobalTheory.CompanionTheory.MatchPow.entT_eq, GlobalTheory.CompanionTheory.MatchPow.phiX_eq]
    have e3 : ∑ s, GlobalTheory.CompanionTheory.MatchPow.beta a (n - a) w ^ k * ∑ j, c' j * GlobalTheory.CompanionTheory.MatchPow.tm n w ϖ a (x' j) s y =
        GlobalTheory.CompanionTheory.MatchPow.beta a (n - a) w ^ k * ∑ j, c' j * ∑ s, GlobalTheory.CompanionTheory.MatchPow.tm n w ϖ a (x' j) s y := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    rw [e3, ← hcon, mul_pow, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [ef, eφ]
  exact hm

theorem match_torus_of_twisted_matching (h : M4) : MatchT :=
  matchTOf2 h GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul matchLin2

end PositivityTheory.Rg.BcB.F.TorusMatching

end
end

