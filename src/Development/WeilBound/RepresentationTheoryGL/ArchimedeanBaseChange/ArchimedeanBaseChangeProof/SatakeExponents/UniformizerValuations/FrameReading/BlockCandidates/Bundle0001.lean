module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.CandOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}

set_option maxHeartbeats 1000000 in
theorem cand_of (O : BO F i χ) (ia : ∀ τ, mOf O.χa τ = mOf (F₀.A i).χa τ) (ib : ∀ τ, mOf O.χb τ = mOf (F₀.A i).χb τ)
    (h5 : PreOfTree) (h6 : JoinEx) : ∃ Pa Pb D, F₀.Cand F.d i O.s₁ O.s₂ Pa Pb D := by
  obtain ⟨Pa, ta⟩ := h5 E _ O.s₁ O.good₁ O.untw₁ fun τ => ⟨_, O.inf₁ τ⟩
  obtain ⟨Pb, tb⟩ := h5 E _ O.s₂ O.good₂ O.untw₂ fun τ => ⟨_, O.inf₂ τ⟩
  obtain ⟨D, hJ⟩ := h6 E n _ _ F₀.μ F₀.e Pa Pb F₀.hμ (Nat.add_sub_of_le (F₀.C.le i))
  obtain ⟨j, hj⟩ := Function.ne_iff.1 O.ne
  refine ⟨Pa, Pb, D, ⟨O.good₁, O.good₂, O.untw₁, O.untw₂, ta, tb, hJ⟩, O.leaves₁, O.leaves₂, fun τ => ?_, fun τ => ?_,
    O.F j, O.mem j, hj, O.type j⟩
  · have := O.inf₁ τ
    rw [ia τ] at this
    exact this
  · have := O.inf₂ τ
    rw [ib τ] at this
    exact this

end PositivityTheory.Rg.BcB.F.BC

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PChiTrS
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem restr {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (S T : StarSubalgebra ℂ A) (hle : S ≤ T)
    (χ : T →⋆ₐ[ℂ] ℂ) : ∃ χ' : S →⋆ₐ[ℂ] ℂ, ∀ (y : A) (hy : y ∈ S) (hy' : y ∈ T), χ' ⟨y, hy⟩ = χ ⟨y, hy'⟩ :=
  ⟨χ.comp (StarSubalgebra.inclusion hle), fun _ _ _ => rfl⟩

section Gen

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem gen_tr (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (a₀ : Γ)
    (c : Γ → ℂ) (hc : ∀ x, (gen x).2 v = c x • v) (h₀ : c a₀ = 1) (Q : Prop)
    (h : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      (∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s)‖) →
      (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) →
      χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → Q) : GRead gen β m v Q := by
  intro s χ h1 h2 h3
  have hle : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) ≤
      StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪
        {star (β s ^ m) * β s ^ m}) := by
    refine StarAlgebra.adjoin_le ?_
    rintro y (⟨x, rfl⟩ | hy)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩, rfl⟩)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr hy)
  obtain ⟨χ', e⟩ := restr _ _ hle χ
  refine h s χ' (fun y => ?_) (fun x => ?_) ?_
  · exact (congrArg norm (e y.1 y.2 (hle y.2))).trans_le (h1 ⟨y.1, hle y.2⟩)
  · have p := ChiPin.chi_pin gen a₀ v hv (by rw [hc, h₀, one_smul]) s _ χ h2
      ⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩ (c x) (hc x)
    exact (e _ _ _).trans p
  · exact (e _ _ _).trans_ne h3

end Gen

set_option maxHeartbeats 2000000 in
theorem chiTr' : ChiTr := fun _ _ _ _ _ _ _ _ _ _ G Q h₀ h =>
  gen_tr (H := G.H) G.gen G.βop G.m G.v G.v_ne G.a₀ (fun x => G.c x G.i₀) (fun x => (G.vblk x).1) h₀ Q
    fun s χ h1 h2 h3 => h s χ ⟨h1, h2, h3⟩

end PositivityTheory.Rg.BcB.F.BC

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PIdentN
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
  {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)} {μ₂ : Measure (GA E b)} {μa : Measure (G a)}
  {μb : Measure (G b)}

theorem prod_valW_ite (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) {k : ℕ} (χ : InfinitePlace E → Inf k) (v : InfinitePlace E)
    (w : List (Bool × ℕ)) (p : Prop) [Decidable p] :
    (∏ v', A.valW (if v' = v ∧ p then w else []) (χ v')) =
      (if p then zVal w (χ v) else 1) * ∏ v', A.valW [] (χ v') := by
  have e : ∀ v', A.valW (if v' = v ∧ p then w else []) (χ v') =
      (if v' = v then (if p then zVal w (χ v) else 1) else 1) * A.valW [] (χ v') := by
    intro v'
    by_cases h1 : v' = v
    · subst h1
      by_cases hp : p
      · simp [hp, Arch.valW, zVal]
      · simp [hp]
    · simp [h1]
  rw [Finset.prod_congr rfl fun v' _ => e v', Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)

theorem val_tD (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool)
    (χa : InfinitePlace E → Inf (F.B i).a) (χb : InfinitePlace E → Inf (F.B i).b) :
    (F.tD i v s m side).val χa χb =
      (if side then zVal [(s, m)] (χb v) else zVal [(s, m)] (χa v)) * (F.t₀ i).val χa χb := by
  simp only [PT.val, valA, RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
  rw [prod_valW_ite, prod_valW_ite]
  cases side <;> simp <;> ring

end

set_option maxHeartbeats 2000000 in
theorem identOf' : IdentOf := by
  intro hG hR E _ _ _ n π S T F₀ F i χ hχ O
  have h0 := O.eigArch (.inl ()) (F.t₀ i) rfl rfl
  have h3 := hχ.2.1 (.inl ())
  have one : (F.t₀ i).val O.χa O.χb = 1 := by
    rw [← h0]
    exact h3
  have key : ∀ (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool),
      (if side then zVal [(s, m)] (O.χb v) else zVal [(s, m)] (O.χa v)) =
        (if side then zVal [(s, m)] ((F₀.A i).χb v) else zVal [(s, m)] ((F₀.A i).χa v)) := by
    intro v s m side
    have h1 := O.eigArch (.inr (.inl (i, v, s, m, side))) (F.tD i v s m side) (by simp [RunFrame.g]) rfl
    have h2 := hχ.2.1 (.inr (.inl (i, v, s, m, side)))
    rw [val_tD, one, mul_one] at h1
    rw [← h1, h2]
    cases side <;> rfl
  constructor
  · intro τ
    refine hG _ _ _ fun m => ?_
    have := key (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding)) m false
    simpa [zVal] using this
  · intro τ
    refine hG _ _ _ fun m => ?_
    have := key (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding)) m true
    simpa [zVal] using this

end PositivityTheory.Rg.BcB.F.BC

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PLimAtOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem gelfand_value_fin_zero {k : ℕ} (hk : k = 0) (x y : Fin k → ℂ) (m : ℕ) : GlobalTheory.Dec.gelfVal x m = GlobalTheory.Dec.gelfVal y m := by
  subst hk; simp [GlobalTheory.Dec.gelfVal]


set_option maxHeartbeats 4000000 in
theorem limAtOf_holds : LimAtOf := by
  intro hSq hLev hGI _ hR E _ _ _ n hn π S T F₀ F h i χ hχ
  have : Countable (Pl E) := Small.countable_pl E
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))
  obtain ⟨⟨o₁, c₁⟩, ⟨o₂, c₂⟩, -, hν⟩ := hLev E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP
  obtain ⟨cK, hcK, hψ⟩ := hν (F.B i).ν (F.B i).hν
  obtain ⟨-, -, hsO, hsop, hsval, -⟩ := hSq E (F.B i) (F.β i) (F₀.A i).bump (F.m - 1) (h.βok i) (F₀.A i).isBump
    (fun v => ⟨(F₀.A i).kera [] v, fun χ => by simp [RunFrame.β, RunFrame.ptL, Arch.pt, Arch.valW, zVal]⟩)
    (fun v => ⟨(F₀.A i).kerb [] v, fun χ => by simp [RunFrame.β, RunFrame.ptL, Arch.pt, Arch.valW, zVal]⟩)
  rw [Nat.sub_add_cancel F.m_pos] at hsop hsval
  have h0 : χ ⟨(F.g (.inl ()) i).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨.inl (), rfl⟩)⟩ = 1 := hχ.2.1 (.inl ())
  have hM := (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  refine hM (F.B i) _ _ o₁ c₁ o₂ c₂ F.Γ (fun x => F.g x i) (.inl ()) (F.t₀ i) (F₀.A i).bump cK
    (fun v s m => (.inr (.inl (i, v, s, m, false)), .inr (.inl (i, v, s, m, true)))) (X F i) ((F.β i).sq (F.m - 1))
    (2 * F.m) χ ?_ (fun x => h.ok x i) hsO hsop.symm (fun χa χb => hsval χa χb) rfl (F₀.A i).isBump ?_
    (fun v => (F₀.A i).kera [] v) (fun v => (F₀.A i).kerb [] v) hcK ?_ ?_ ?_
    (fun x y => ⟨h.comm x y i, h.commStar x y i⟩) ?_ (IsSelfAdjoint.star_mul_self _) hχ.1 (h0.trans_ne one_ne_zero) ?_
  · have := F₀.C.le i
    show 0 < F₀.C.a i + (n - F₀.C.a i)
    omega
  · rintro (⟨⟩ | x | x) t hx
    · simp only [RunFrame.g, Sum.inr.injEq] at hx
      subst hx
      exact Or.inr rfl
    · simp only [RunFrame.g] at hx
      by_cases hi : i = x.1
      · rw [if_pos hi, Sum.inr.injEq] at hx
        subst hx
        exact Or.inr rfl
      · rw [if_neg hi] at hx
        cases hx
    · simp only [RunFrame.g, Sum.inr.injEq] at hx
      subst hx
      exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro x y g
    rw [show (F.t₀ i).ψ x y g = _ from hψ x y g]
    split_ifs <;> rfl
  · intro v s m _ _
    refine ⟨F.tD i v s m false, by simp [RunFrame.g], rfl, ?_, ?_, ?_⟩
    · funext v'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
    · simpa [RunFrame.tD, Arch.pt] using (F₀.A i).kera [(s, m)] v
    · intro v' hv'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt, hv']
  · intro v s m _ _
    refine ⟨F.tD i v s m true, by simp [RunFrame.g], rfl, ?_, ?_, ?_⟩
    · funext v'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt]
    · simpa [RunFrame.tD, Arch.pt] using (F₀.A i).kerb [(s, m)] v
    · intro v' hv'
      simp [RunFrame.tD, RunFrame.t₀, RunFrame.ptL, Arch.pt, hv']
  · intro x
    obtain ⟨c1, c2⟩ := h.βcomm i x
    have c3 : Commute (star (F.β i).op) (F.g x i).op := by simpa using c2.star_star
    have c4 : Commute (star (F.β i).op) (star (F.g x i).op) := c1.star_star
    refine ⟨?_, ?_⟩
    · show Commute (star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m) _
      rw [star_pow]
      exact (c3.pow_left _).mul_left (c1.pow_left _)
    · show Commute (star ((F.β i).op ^ F.m) * (F.β i).op ^ F.m) _
      rw [star_pow]
      exact (c4.pow_left _).mul_left (c2.pow_left _)
  · intro χa χb ha hb
    have hreg := gamma_zeta_nabla_cancel.reg_of hGI
    have ka : ∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m = GlobalTheory.Dec.gelfVal (infOf ((F₀.C.l₁ i) v).w s) m := by
      intro v s m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [GlobalTheory.Dec.gelfVal]
      rcases Nat.eq_zero_or_pos (F₀.C.a i) with ha0 | ha0
      · exact gelfand_value_fin_zero ha0 _ _ m
      rw [ha v s m hm ha0]
      refine (congrArg₂ (· / ·) (hχ.2.1 (.inr (.inl (i, v, s, m, false)))) h0).trans ?_
      show F.dval (i, v, s, m, false) / 1 = _
      simp [RunFrame.dval, zVal, Arch.χa]
    have kb : ∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m = GlobalTheory.Dec.gelfVal (infOf ((F₀.C.l₂ i) v).w s) m := by
      intro v s m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [GlobalTheory.Dec.gelfVal]
      rcases Nat.eq_zero_or_pos (n - F₀.C.a i) with hb0 | hb0
      · exact gelfand_value_fin_zero hb0 _ _ m
      rw [hb v s m hm hb0]
      refine (congrArg₂ (· / ·) (hχ.2.1 (.inr (.inl (i, v, s, m, true)))) h0).trans ?_
      show F.dval (i, v, s, m, true) / 1 = _
      simp [RunFrame.dval, zVal, Arch.χb]
    obtain ⟨r1, g1⟩ := hreg E _ (F₀.C.l₁ i) χa ka
    obtain ⟨r2, g2⟩ := hreg E _ (F₀.C.l₂ i) χb kb
    exact ⟨r1, r2, fun τ => ⟨g1 τ, g2 τ⟩⟩

theorem limAt_holds : LimAt := limAtOf_holds BlockFiniteConvolution.sqOk₀ (levIdem slots) gamma_zeta_nabla_cancel.gelfInj gamma_zeta_nabla_cancel.regDom

end PositivityTheory.Rg.BcB.F.BC

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PPowNe
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem pw_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (t : PT B) (h : IsFinM t.ψ) :
    ∀ j, IsFinM (t.pw j).ψ := by
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  haveI := B.hν
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact CG.PMul.mulF_fin B.ν h ih

theorem adj_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {κ : Type} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (h : IsFinM ψ) : IsFinM (adjF ψ) := fun x y =>
  ⟨Complex.continuous_conj.comp ((h y x).1.comp continuous_inv),
    ((h y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem powNeOf_holds : PowNeOf := by
  intro hCM E _ _ _ B t m A _ G ht hG hne h0
  choose U hU hF using hG
  have ho : IsOpen ((⨅ j, U j : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hU
  have hf : ∀ i, ∀ u ∈ (⨅ j, U j : Subgroup (Hf E B.a B.b)), ∀ x, G i (x * finH u) = G i x :=
    fun i u hu => hF i u (Subgroup.mem_iInf.1 hu i)
  apply hne
  rw [R3.sq_psi, (hCM E B A _ _ _ G (pw_fin t.adj' (adj_fin ht) m) (pw_fin t ht m) ho hf).1,
    R3.convF_pw hCM t _ G ho hf m fun j _ => pw_fin t ht j, h0, R3.convF_zero]

end PositivityTheory.Rg.BcB.F.BC

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.SqNe
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.BcB.F.BC

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T) (i : F₀.C.ι)
  {χ : Rd.ChAlg (fun x => F.g x i) (X F i) →⋆ₐ[ℂ] ℂ}

set_option maxHeartbeats 1000000 in
theorem sq_ne (c : F.Γ → ℂ) (hc : c (.inl ()) = 1) (hχ : Chi (fun x => F.g x i) (X F i) c χ) (O : BO F i χ) :
    convF (F.B i).ν ((F.β i).sq (F.m - 1)).ψ O.F ≠ 0 := by
  have e := O.eigX
  intro h0
  rw [h0] at e
  refine smul_ne_zero (div_ne_zero hχ.2.2 (pow_ne_zero _ ?_)) O.ne e.symm
  exact ((hχ.2.1 (.inl ())).trans hc).trans_ne one_ne_zero

set_option maxHeartbeats 1000000 in
theorem eig_h (c : F.Γ → ℂ) (hc : c (.inl ()) = 1) (hχ : Chi (fun x => F.g x i) (X F i) c χ) (O : BO F i χ)
    (x : {w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool) :
    convF (F.B i).ν (F.ψ i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) O.F = c (.inr (.inr x)) • O.F := by
  have e := O.eigFin (.inr (.inr x)) (F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)) rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [hχ.2.1 (.inr (.inr x)), hχ.2.1 (.inl ()), hc, div_one] at e
  exact e

end PositivityTheory.Rg.BcB.F.BC

end
end

