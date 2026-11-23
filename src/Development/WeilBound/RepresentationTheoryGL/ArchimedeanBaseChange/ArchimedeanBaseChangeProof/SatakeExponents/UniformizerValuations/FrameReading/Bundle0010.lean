module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.ContinuousRingHom

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FRGood
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LevRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (d : LocData E n) (a : ℕ),
  a ≤ n → IsSection S → d.Ok → (↑d.P : Set (Pl E)) ⊆ S → IsLev (d.lev a) ∧ IsLev (d.lev₂ a) ∧
  ∀ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E (n - a) → ℂ)) (G : H E a (n - a) → ℂ),
    TypeH (lev₁ S d a) (lev₂ S d a) W₁ W₂ G → OfLev S (d.lev a) (d.lev₂ a) G


set_option maxHeartbeats 1000000 in
def FRGood : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T) (i : F₀.C.ι)
  (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n),
  Ctx F₀.μ s₁ s₂ Pa Pb D → ∀ (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ), G ≠ 0 →
  (∀ j, G j ∈ pairSpace s₁.space s₂.space) → (∀ j, OfLev F₀.Sec (F.d.lev _) (F.d.lev₂ _) (G j)) →
  (∀ x : {w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool,
    convF (F.B i).ν (F.ψ i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) G = (F.ug (.inr (.inr x))).p F.fam F.i₀ • G) →
  ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w


set_option maxHeartbeats 1000000 in
def FRWeight : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (d : LocData E n) (i : F₀.C.ι)
  (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n),
  F₀.Cand d i s₁ s₂ Pa Pb D → ∀ τ lam, HasWeightAt π τ lam → ∑ j, D.m j τ = infOfWeight lam

def LevReadOf : Prop := LevIdem → LevRead

def FRGoodOf : Prop := GoodL → LevRead → FRGood

def FRWeightOf : Prop := WeightL → FRWeight

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandSa
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PCandSa

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locM_comp {a b : ℕ} {k k' : Type} [Fintype k] [Fintype k'] (w : Pl E) (φ : k ≃ k')
    (N : k' → k' → LF a b w) (Y : k' → H E a b → ℂ) (m : ℕ) :
    (locM w (fun x y => N (φ x) (φ y)))^[m] (Y ∘ φ) = ((locM w N)^[m] Y) ∘ φ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [locM, Function.comp]
    exact Equiv.sum_comp φ (fun y' => actP w (N (φ x) y') (((locM w N)^[m] Y) y'))

theorem isLev_lev {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) : Tail.IsLev (d.lev a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, e⟩ := LocOk.lev_lv d hd ha w
    rw [e]
    exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev_out d (LocOk.out3 d h).1 (LocOk.out3 d h).2)

theorem isLev_lev₂ {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) : Tail.IsLev (d.lev₂ a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, e⟩ := LocOk.lev₂_lv d hd ha w
    rw [e]
    exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev₂_out d (LocOk.out3 d h).2)

theorem betaL_hecke {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) :
    ∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) ((d.betaL a ha).m w x y) := by
  intro w hw x y
  show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d w z.1.1) x y
  · have hS : w ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hw
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

def kapX {n : ℕ} (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) : d.kap w ≃ (d.X w) :=
  Equiv.ofBijective (fun x => ⟨x.1.2, LocOk.kap_X d hT hS x⟩) (by
    have e : d.idx w = {∅} ×ˢ d.X w := by unfold LocData.idx; rw [if_neg hT, if_pos hS]
    constructor
    · rintro ⟨⟨s, x⟩, hx⟩ ⟨⟨s', x'⟩, hx'⟩ h
      have h1 := (Finset.mem_product.1 (e ▸ hx)).1
      have h2 := (Finset.mem_product.1 (e ▸ hx')).1
      simp only [Finset.mem_singleton] at h1 h2
      simp only [Subtype.mk.injEq] at h
      subst h1 h2 h
      rfl
    · rintro ⟨x, hx⟩
      exact ⟨⟨(∅, x), by rw [e]; simp [hx]⟩, rfl⟩)

end PCandSa

open PCandSa in
theorem candS_of (h : Tail.ReadS) : CandS := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwS hsplit
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  obtain ⟨hS0, hBad, hμ, hϖ, hK', hX, hL, hfix, hKB⟩ := F.same
  have hw0 : w ∈ F₀.d₀.S₀ := F₀.S_le w hwS hsplit
  have hwd : w ∈ F.d.S₀ := hS0 ▸ hw0
  have hwT : w ∉ F.d.T := fun h => Finset.disjoint_left.1 F.ok.disj.1 h hwd
  have hwP : w ∈ F.d.P := Finset.mem_union_right _ hwd
  have hwSec : w ∈ F₀.Sec := (F₀.S₀ w hw0).1
  have hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h1 | h1
    · exact (F.T_in u h1).1
    · exact (F₀.S₀ u (hS0 ▸ h1)).1
  have hpow := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _)
    F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d F.ok ha) (isLev_lev₂ F.d F.ok ha)
    ((BlockFiniteConvolution.locOk₀ E n F.d F.ok _ ha).2.1) (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => ((betaL_hecke F.d F.ok ha u hu x y).2 k hk g)) hl hne ⟨w, hwP⟩
  obtain ⟨α, x₀, hx₀⟩ := hpow
  have hGy : ∀ j, G j ∈ pairSpace s₁.space s₂.space ∧ G j ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun j => ⟨hG j, ((hl j).2 w hwSec).1⟩
  set G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ :=
    fun y => G (α, (Equiv.refl _).symm (Function.update x₀ ⟨w, hwP⟩ y)) with hG'def
  have hG'p : ∀ y, G' y ∈ pairSpace s₁.space s₂.space ∧ G' y ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun y => hGy _
  change (locM w ((F.d.betaL _ ha).m w))^[F.m] G' ≠ 0 at hx₀
  clear_value G'
  set φ := kapX F.d hwT hwd with hφ
  let N : (F.d.X w) → (F.d.X w) → LF (F₀.C.a i) (n - F₀.C.a i) w :=
    fun x y => phiMu (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) x y
  have hm : (F.d.betaL _ ha).m w = fun x y => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • N (φ x) (φ y) := by
    funext x y g
    simp only [LocData.betaL, if_neg hwT, LocData.mac, Pi.smul_apply, smul_eq_mul, N, hμ, F₀.μloc]
    rfl
  rw [hm] at hx₀
  have hopen : IsOpen (F.d.lev (F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) :=
    ((isLev_lev F.d F.ok ha).1 w).1
  have h1 := (Tail.locPow_holds E _ _ w (F.d.kap w) (F.d.lev _ w) G' F.m hopen (fun y => (hG'p y).2)).1 _
    (fun x y => N (φ x) (φ y)) hx₀
  have h2 : (matS (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) (F.d.X w))^[F.m] (G' ∘ φ.symm) ≠ 0 := by
    intro h0
    apply h1
    have e1 := locM_comp w φ N (G' ∘ φ.symm) F.m
    rw [show (G' ∘ φ.symm) ∘ φ = G' from by funext y; simp] at e1
    rw [e1]
    change ((matS (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) (F.d.X w))^[F.m] (G' ∘ φ.symm)) ∘ φ = 0
    rw [h0]
    rfl
  obtain ⟨P, hPc, hkill⟩ := F.choiceS w hw0
  have hOk := F.ok.K' w hwd
  rw [hK'] at hOk
  obtain ⟨hO, hle, hN, hXK, hU, hHk⟩ := hOk
  exact ⟨P, h E n (F₀.C.a i) (n - F₀.C.a i) (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F₀.d₀.K' w) (F.d.X w)
    (F.d.lev _ w) (F.d.e w) P F.m (G' ∘ φ.symm) hO hle hN hXK hU hopen hHk (hkill i s₁ s₂ Pa Pb D hc)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).1 w hw0) (fun x => hG'p _) h2, hPc⟩

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandTb
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.PCandTb

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

set_option linter.unusedSectionVars false

theorem isLev_of {a b : ℕ} (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (Q : Finset (Pl E))
    (h : ∀ w, LocOk.IsLv (U w)) (hout : ∀ w ∉ Q, U w = K2 a b w) : IsLev U := by
  refine ⟨fun w => ?_, Filter.eventually_cofinite.2 (Q.finite_toSet.subset fun w hw => ?_)⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := h w
    rw [he]
    exact LocOk.prod_open_le h₁ h₂
  · by_contra hq
    exact hw (hout w hq)

variable {n : ℕ} (d : LocData E n) {a : ℕ}

theorem isLev_lev (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev_lv d hd ha) fun _ hw =>
    LocOk.lev_out d (LocOk.out3 d hw).1 (LocOk.out3 d hw).2

theorem isLev_lev₂ (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev₂ a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev₂_lv d hd ha) fun _ hw => LocOk.lev₂_out d (LocOk.out3 d hw).2

theorem betaL_H (hd : d.Ok) (ha : a ≤ n) {u : Pl E} (hu : u ∈ d.P) (x y : d.kap u) :
    IsHecke (d.lev a u) ((d.betaL a ha).m u x y) := by
  show IsHecke _ (if u ∈ d.T then d.diag (fun x => d.qT a u x.1.1) x y else d.mac a ha u (d.e u) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d u z.1.1) x y
  · have hS : u ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hu
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

theorem gap_restr {m : ℕ} {x : Fin n → ℤ} (hx : x ∈ coneGL n 2) (S : Finset (Fin n)) (h : S.card = m) :
    Gap (PositivityTheory.Rg.Bc.ArchbcB.B.restr x S h) := by
  intro p q hpq
  have := hx _ _ ((S.orderEmbOfFin h).strictMono hpq)
  show x _ + 1 ≤ x _
  omega

theorem unrAt_pow {μ : HChar E} {w : Pl E} (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := by
  induction k with
  | zero => intro x _; rw [pow_zero]; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ]
    show (μ ^ k).loc w x * μ.loc w x = 1
    rw [ih x hx, h x hx, one_mul]

end PositivityTheory.Rg.BcB.F.PCandTb

namespace PositivityTheory.Rg.BcB.F

open PCandTb

theorem candT_of (h1 : Tail.ReadT) (h2 : Tail.ExpRead) (h3 : RS.JoinSat) : CandT := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwT hunr hns
  have hd := F.ok
  have hwd : w ∈ F.d.T := F.T_le w hwT hunr hns
  have hwSec : w ∈ F₀.Sec := (F.T_in w hwd).1
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · exact (F.T_in u h).1
    · rw [F.same.1] at h
      exact (F₀.S₀ u h).1
  have hwP : w ∈ F.d.P := Finset.mem_union_left _ hwd
  obtain ⟨α, x, hx⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i)
    (Equiv.refl _) F₀.hSec hP (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (F.d.betaL _ (F₀.C.le i)) A G F.m
    (isLev_lev F.d hd (F₀.C.le i)) (isLev_lev₂ F.d hd (F₀.C.le i))
    (locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E n F.d hd _ (F₀.C.le i)).2.1 (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => (betaL_H F.d hd (F₀.C.le i) hu x y).2 k hk g) hl hne ⟨w, hwP⟩
  have hm : (F.d.betaL _ (F₀.C.le i)).m w = fun x y => if x = y then F.d.qT (F₀.C.a i) w x.1.1 else 0 := by
    funext x y
    show (if w ∈ F.d.T then _ else _) = _
    rw [if_pos hwd]
    rfl
  let G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ := fun y => G (α, Function.update x ⟨w, hwP⟩ y)
  change (locM w ((F.d.betaL _ (F₀.C.le i)).m w))^[F.m] G' ≠ 0 at hx
  rw [hm] at hx
  have hfix : ∀ y, G' y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (I2 (F₀.C.a i) (n - F₀.C.a i) w) := fun y => by
    have h := ((hl (α, Function.update x ⟨w, hwP⟩ y)).2 w hwSec).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  have hIo : IsOpen (I2 (F₀.C.a i) (n - F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) := by
    have h := ((isLev_lev F.d hd (F₀.C.le i)).1 w).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  obtain ⟨s, hs⟩ := (locPow_holds E _ _ w _ _ G' F.m hIo hfix).2 (fun x => F.d.qT (F₀.C.a i) w x.1.1) (by convert hx)
  by_cases hadm : LocData.admitted n (F₀.C.a i) s.1.1
  swap
  · exfalso
    have h0 : F.d.qT (F₀.C.a i) w s.1.1 = 0 := by
      funext y
      simp only [LocData.qT, dif_neg hadm]
      rfl
    obtain ⟨k, hk⟩ : ∃ k, F.m = k + 1 := ⟨F.m - 1, by have := F.m_pos; omega⟩
    rw [h0, hk, Function.iterate_succ_apply', Psmall.actP_zero] at hs
    exact hs rfl
  have hq : F.d.qT (F₀.C.a i) w s.1.1 = fun g => ∑ j : (F.d.c w).support,
      (F.d.c w j * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf (j : Fin n → ℤ)) s.1.1) *
        (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ)) *
      dc2 w (F.d.ϖ w) (restr (j : Fin n → ℤ) _ hadm.2.1) (restr (j : Fin n → ℤ) _ hadm.2.2) g := by
    funext g
    simp only [LocData.qT, dif_pos hadm, Finsupp.sum]
    rw [← Finset.sum_coe_sort]
  rw [hq] at hs
  obtain ⟨ξa, ξb, hJ, hsum⟩ := h1 E n (F₀.C.a i) (n - F₀.C.a i) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.ϖ w)
    (F.d.c w).support _ (fun j => restr (j : Fin n → ℤ) _ hadm.2.1) (fun j => restr (j : Fin n → ℤ) _ hadm.2.2) F.m (G' s)
    (hd.unif w)
    (fun j => ⟨gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _, gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _⟩)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).2 w hwd) (hG _) (hfix s) hs
  have hsum' : ((F.d.c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s.1.1) *
      ev2 w ξa ξb (restr x _ hadm.2.1) (restr x _ hadm.2.2)) ≠ 0 := by
    intro h0
    rw [Finsupp.sum, ← Finset.sum_coe_sort] at h0
    apply hsum
    rw [show (0 : ℂ) = (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ) * 0 by ring,
      ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ' : JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb := by
    rw [← F.same.2.2.2.1]
    exact hJ
  obtain ⟨hma, hmb, hbc⟩ := F.choiceT i s₁ s₂ Pa Pb D hc w hwd s.1.1 hadm ξa ξb hJ' hsum'
  obtain ⟨hSa, hSb⟩ := h2 E (F₀.C.a i) (n - F₀.C.a i) Pa Pb w (F.d.ϖ w) ξa ξb (hd.unif w) hma hmb hJ
  have hS0 : w ∉ F₀.d₀.S₀ := by
    rw [← F.same.1]
    exact Finset.disjoint_left.1 hd.disj.1 hwd
  have hBad : w ∉ F₀.d₀.Bad := by
    rw [← F.same.2.1]
    exact Finset.disjoint_left.1 hd.disj.2.1 hwd
  have hμ := (F₀.good w hwSec hS0 hBad).2
  have hDs := h3 E n (F₀.C.a i) (n - F₀.C.a i) (F₀.μ ^ (n - F₀.C.a i)) (F₀.μ ^ F₀.C.a i) Pa Pb D w _ _ hc.ctx.join
    (unrAt_pow hμ _) (unrAt_pow hμ _) hSa hSb
  refine ⟨_, hDs, fun s' ϖ q hs' hq' α' hα' => ?_⟩
  have e := LemB.cjEq E w hns s' hs'
  subst e
  exact hbc ϖ q hq' α' hα'

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PChiPin
section
noncomputable section

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.BcB.F.ChiPin

open PositivityTheory.Rg.BcB.F

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem chi_pin (gen : Γ → Prod' H d) (a₀ : Γ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (ha₀ : (gen a₀).2 v = v)
    (s : ι) (X : H s →L[ℂ] H s)
    (χ : StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})
      →⋆ₐ[ℂ] ℂ)
    (heig : ∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c)
    (a : StarAlgebra.adjoin ℂ (Set.range gen)) (c : ℂ) (hc : a.1.2 v = c • v) :
    χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c := by
  have key : ∀ b : StarAlgebra.adjoin ℂ (Set.range gen), ∀ e : ℂ, e ≠ 0 → b.1.2 v = e • v →
      χ ⟨b.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨b, rfl⟩)⟩ = e := by
    intro b e he hb
    obtain ⟨c', hc', hχ⟩ := heig b (by rw [hb]; exact smul_ne_zero he hv)
    rw [hχ]
    have h2 : (c' - e) • v = 0 := by rw [sub_smul, ← hc', ← hb, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv)
  by_cases h0 : c = 0
  · subst h0
    let g : StarAlgebra.adjoin ℂ (Set.range gen) := ⟨gen a₀, StarAlgebra.subset_adjoin ℂ _ ⟨a₀, rfl⟩⟩
    have hg : g.1.2 v = (1 : ℂ) • v := by rw [one_smul]; exact ha₀
    have hab : (a + g).1.2 v = (1 : ℂ) • v := by
      change (a.1.2 + g.1.2) v = _
      rw [ContinuousLinearMap.add_apply, hc, hg, zero_smul, zero_add]
    have e1 := key (a + g) 1 one_ne_zero hab
    have e2 := key g 1 one_ne_zero hg
    have hsum : (⟨(a + g).1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a + g, rfl⟩)⟩ :
        StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})) =
        ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ +
          ⟨g.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ := rfl
    rw [hsum, show ∀ p q, χ (p + q) = χ p + χ q from fun p q => χ.toAlgHom.map_add p q, e2] at e1
    linear_combination e1
  · exact key a c h0 hc

end PositivityTheory.Rg.BcB.F.ChiPin

end
end

