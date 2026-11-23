module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem allLeaves_imp {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q
  | _, .leaf V _, hp => h _ V hp
  | _, .node t₁ t₂, hp => ⟨allLeaves_imp h t₁ hp.1, allLeaves_imp h t₂ hp.2⟩


set_option maxHeartbeats 2000000 in
def CandTOut : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    (∀ τ lam, HasWeightAt π τ lam → ∑ k, D.m k τ = infOfWeight lam) →
    (∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w) →
    TOut π S T F₀.K F₀.W D

def CandS : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    ∀ w ∈ S, IsSplitAt w → ∃ P : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def CandT : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w

def CandLev : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
    F₀.Cand F.d i s₁ s₂ Pa Pb D → (∀ j, G j ∈ pairSpace s₁.space s₂.space) →
    (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) →
    (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 →
    ∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (F₀.K w)

theorem candTOut_of (hS : CandS) (hT : CandT) (hL : CandLev) : CandTOut := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne hwt hgood
  refine tout_of hwt hgood (hS hR E hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne)
    (hT hR E hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne) (hL hR E hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne)
    (F₀.W_join i s₁ s₂ Pa Pb D hc.ctx ?_ ?_)
  · exact allLeaves_imp (fun _ _ h => h.imp_right fun ⟨K', _, W', hW', h'⟩ => ⟨K', W', hW', h'⟩) _ hc.leaves₁
  · exact allLeaves_imp (fun _ _ h => h.imp_right fun ⟨K', _, W', hW', h'⟩ => ⟨K', W', hW', h'⟩) _ hc.leaves₂

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IwahoriPairLeMaximal
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.F.Tail (I2)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rd.LevOC

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem maximal_pair_isCompact (a b : ℕ) (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  rw [K2, Subgroup.coe_prod]
  exact (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)

theorem KGL_open (w : Pl E) (m : ℕ) : IsOpen (GlobalTheory.LFun.KGL w (n := m) : Set (GLw m w)) := by
  rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isOpen_KO

theorem maximal_pair_isOpen (a b : ℕ) (w : Pl E) : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) := by
  rw [K2, Subgroup.coe_prod]
  exact (KGL_open w a).prod (KGL_open w b)

theorem iwahori_pair_isOpen (a b : ℕ) (w : Pl E) : IsOpen (I2 a b w : Set (GLw a w × GLw b w)) := by
  rw [I2, Subgroup.coe_prod]
  exact (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)).prod
    (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin b))

theorem I2_le_K2 (a b : ℕ) (w : Pl E) : I2 a b w ≤ K2 a b w :=
  Subgroup.prod_mono (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w b)

theorem compact_of_le {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) (ho : IsOpen (L : Set (GLw a w × GLw b w)))
    (hle : L ≤ K2 a b w) : IsCompact (L : Set (GLw a w × GLw b w)) :=
  (maximal_pair_isCompact a b w).of_isClosed_subset (Subgroup.isClosed_of_isOpen L ho) hle

theorem L_open_le (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) (w : Pl E) (hw : w ∈ d.S₀ ∪ d.Bad) :
    IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w)) ∧ d.L a w ≤ K2 a (n - a) w := by
  obtain ⟨L₁, L₂, h, ⟨h1o, h1le, -⟩, ⟨h2o, h2le, -⟩⟩ := hd.L a ha w hw
  rw [h, Subgroup.coe_prod]
  exact ⟨h1o.prod h2o, Subgroup.prod_mono h1le h2le⟩

theorem locLev_oc (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ IsCompact (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧
      d.lev a w ≤ K2 a (n - a) w := by
  have h : IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w := by
    unfold LocData.lev
    split_ifs with h1 h2
    · exact ⟨iwahori_pair_isOpen a (n - a) w, I2_le_K2 a (n - a) w⟩
    · exact L_open_le d hd a ha w h2
    · exact ⟨maximal_pair_isOpen a (n - a) w, le_rfl⟩
  exact ⟨h.1, compact_of_le _ h.1 h.2, h.2⟩

theorem locLev₂_oc (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ IsCompact (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧
      d.lev₂ a w ≤ K2 a (n - a) w := by
  have h : IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev₂ a w ≤ K2 a (n - a) w := by
    unfold LocData.lev₂
    split_ifs with h2
    · exact L_open_le d hd a ha w h2
    · exact ⟨maximal_pair_isOpen a (n - a) w, le_rfl⟩
  exact ⟨h.1, compact_of_le _ h.1 h.2, h.2⟩

def gSet (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Set (Hf E a (n - a)) :=
  {h | ∀ w ∈ Sec, atW w h ∈ d.lev a w ∧ (IsSplitAt w → atW w (thP E a (n - a) h) ∈ d.lev₂ a w)}

def g₁ (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (GL (Fin a) (Af E)) :=
  Subgroup.closure {g | (g, 1) ∈ gSet Sec d a}

def g₂ (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (GL (Fin (n - a)) (Af E)) :=
  Subgroup.closure {g | (1, g) ∈ gSet Sec d a}

def C (d : LocData E n) (a : ℕ) {S : Set (Pl E)} : ∀ i : Slot S, Set (GLw a i.pl × GLw (n - a) i.pl)
  | .inl w => (d.lev a w.1 : Set (GLw a w.1 × GLw (n - a) w.1))
  | .inr w => (d.lev₂ a w.1 : Set (GLw a w.1 × GLw (n - a) w.1))

theorem position_cof {S : Set (Pl E)} {P : Pl E → Prop} (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ i : Slot S in cofinite, P i.pl := by
  rw [Filter.eventually_cofinite] at h ⊢
  have h1 : {w : {w // w ∈ S} | ¬ P w.1}.Finite := h.preimage Subtype.val_injective.injOn
  have h2 : {w : {w // w ∈ S ∧ IsSplitAt w} | ¬ P w.1}.Finite := h.preimage Subtype.val_injective.injOn
  refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
  rintro (w | w) hw
  · exact Or.inl ⟨w, hw, rfl⟩
  · exact Or.inr ⟨w, hw, rfl⟩

theorem C_cof (d : LocData E n) (a : ℕ) {S : Set (Pl E)} :
    ∀ᶠ i : Slot S in cofinite, C d a i = (K2 a (n - a) i.pl : Set (GLw a i.pl × GLw (n - a) i.pl)) := by
  filter_upwards [position_cof (S := S) (Rd.levCof d a)] with i hi
  rcases i with w | w
  · show ((d.lev a w.1 : Subgroup _) : Set (GLw a w.1 × GLw (n - a) w.1)) = (K2 a (n - a) w.1 : Set _)
    have h' : d.lev a w.1 = K2 a (n - a) w.1 := hi.1
    rw [h']
  · show ((d.lev₂ a w.1 : Subgroup _) : Set (GLw a w.1 × GLw (n - a) w.1)) = (K2 a (n - a) w.1 : Set _)
    have h' : d.lev₂ a w.1 = K2 a (n - a) w.1 := hi.2
    rw [h']

theorem gSet_eq (S : Set (Pl E)) (d : LocData E n) (a : ℕ) :
    gSet S d a = {x : Hf E a (n - a) | ∀ i : Slot S, i.cp a (n - a) x ∈ C d a i} := by
  ext x
  constructor
  · intro hx i
    rcases i with w | w
    · exact (hx w.1 w.2).1
    · exact (hx w.1 w.2.1).2 w.2.2
  · intro hx w hw
    exact ⟨hx (.inl ⟨w, hw⟩), fun hs => hx (.inr ⟨w, hw, hs⟩)⟩

def levSub (S : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (Hf E a (n - a)) where
  carrier := gSet S d a
  one_mem' := by
    simp only [gSet, Set.mem_ofPred_eq, map_one]
    intro w _
    have e1 : atW w (1 : Hf E a (n - a)) = 1 := by simp [atW]
    rw [e1]
    exact ⟨one_mem _, fun _ => one_mem _⟩
  mul_mem' := by
    intro x y hx hy
    simp only [gSet, Set.mem_ofPred_eq] at hx hy ⊢
    intro w hw
    have e : ∀ z z' : Hf E a (n - a), atW w (z * z') = atW w z * atW w z' := fun z z' => by simp [atW]
    simp only [map_mul, e]
    exact ⟨mul_mem (hx w hw).1 (hy w hw).1, fun hs => mul_mem ((hx w hw).2 hs) ((hy w hw).2 hs)⟩
  inv_mem' := by
    intro x hx
    simp only [gSet, Set.mem_ofPred_eq] at hx ⊢
    intro w hw
    have e : ∀ z : Hf E a (n - a), atW w z⁻¹ = (atW w z)⁻¹ := fun z => by simp [atW]
    simp only [map_inv, e]
    exact ⟨inv_mem (hx w hw).1, fun hs => inv_mem ((hx w hw).2 hs)⟩

theorem g₁_coe (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) :
    (g₁ Sec d a : Set (GL (Fin a) (Af E))) = (fun g => ((g, 1) : Hf E a (n - a))) ⁻¹' gSet Sec d a := by
  rw [g₁, show {g | ((g, 1) : Hf E a (n - a)) ∈ gSet Sec d a} =
    (((levSub Sec d a).comap (MonoidHom.inl _ _) : Subgroup _) : Set _) from rfl, Subgroup.closure_eq]
  rfl

theorem g₂_coe (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) :
    (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) = (fun g => ((1, g) : Hf E a (n - a))) ⁻¹' gSet Sec d a := by
  rw [g₂, show {g | ((1, g) : Hf E a (n - a)) ∈ gSet Sec d a} =
    (((levSub Sec d a).comap (MonoidHom.inr _ _) : Subgroup _) : Set _) from rfl, Subgroup.closure_eq]
  rfl

end PositivityTheory.Rg.BcB.F.Rd.LevOC

end
end

