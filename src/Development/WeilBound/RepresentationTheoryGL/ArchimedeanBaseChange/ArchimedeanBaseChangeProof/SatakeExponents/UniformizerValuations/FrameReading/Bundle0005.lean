module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FGLeaf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ConjFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  (∀ (w u : Pl E) (G : H E a b → ℂ), IsSplitAt w → ConjPl w u → G ∈ fixed (pairRtT a b w) (K2 a b w) →
    G ∈ fixed (pairRt a b u) (K2 a b u)) ∧
  ∀ S : Set (Pl E), IsSection S → (∀ u, IsSplitAt u → u ∈ S ∨ ∃ w ∈ S, IsSplitAt w ∧ ConjPl w u) ∧
    ∀ X : Finset (Pl E), {u | ∃ w ∈ X, ConjPl w u}.Finite

def USat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E)
  (σ : SmIrr (UL n w)), IsSplitAt w → IsCompU π w σ → fixed σ.ρ (KL n w) ≠ ⊥ →
  ∃ B, SatAtU π w B ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ k ≤ n,
    twTr σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id = satEig (qV E w) n B k

def CtHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
  (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E) (k : ℕ), IsSplitAt w → IsUnifV E w ϖ →
  (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → ν u = 1) →
  HasCompactSupport (ctT h w ν ϖ k) ∧ (∀ y ∈ K2 a b w, ∀ g, ctT h w ν ϖ k (g * y) = ctT h w ν ϖ k g) ∧ ν ((-1) ^ (a * b)) = 1

def USatOf : Prop := SplitDict → USat

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def actS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : Slot S → (H E a b → ℂ) → H E a b → ℂ
  | .inl w => actP w.1 (φ₁ w.1)
  | .inr w => actT w.1 (φ₂ w.1)

def FinAct : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (S : Set (Pl E)), IsSection S →
  ∀ φ₁ φ₂ : ∀ w : Pl E, LF B.a B.b w, IsTestP φ₁ → IsTestP φ₂ → ∀ G : H E B.a B.b → ℂ, HasLev G →
  ∀ l : List (Slot S), l.Nodup → (∀ i ∉ l, actS φ₁ φ₂ i G = G) →
    ∀ x, ∫ h, finFn S φ₁ φ₂ h * G (x * finH h) ∂B.ν = B.vol * l.foldr (fun i g => actS φ₁ φ₂ i g) G x

def ActAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w, IsTestP φ₁ → IsTestP φ₂ → IsTestP ψ₁ → IsTestP ψ₂ →
  ∀ G G' : H E a b → ℂ, HasLev G → HasLev G' → ∀ i j : Slot S,
    HasLev (actS φ₁ φ₂ i G) ∧ (∀ c : ℂ, actS φ₁ φ₂ i (G + c • G') = actS φ₁ φ₂ i G + c • actS φ₁ φ₂ i G') ∧
    (i ≠ j → actS φ₁ φ₂ i (actS ψ₁ ψ₂ j G) = actS ψ₁ ψ₂ j (actS φ₁ φ₂ i G)) ∧
    actS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i G =
      actS φ₁ φ₂ i (actS ψ₁ ψ₂ i G)

def ActIdem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
  (L : Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ), IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ K2 a b w → HasLev G →
  (actP w (idem L) G = G ↔ G ∈ fixed (pairRt a b w) L) ∧
  (actT w (idem L) G = G ↔ G ∈ fixed (pairRtT a b w) L)

section

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)

def Quiet {A : Type} (L : LM κ B.a B.b) (i₀ : Slot S) (F : A × B.κ → H E B.a B.b → ℂ) : Prop :=
  (∀ w ∈ P, (∀ h : w ∈ S, i₀ ≠ Sum.inl ⟨w, h⟩) → ∀ x y, x ≠ y → L.m w x y = 0) ∧
    ∀ i : Slot S, i ≠ i₀ → ∀ p x y, (∀ w : P, (∀ h : w.1 ∈ S, i₀ ≠ Sum.inl ⟨w.1, h⟩) → e x w = e y w) →
      actS (L.ent P (e x) (e y)) L.t i (F (p, y)) = F (p, y)

end

def FmAtP : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)]
  (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → ∀ hP : (↑P : Set (Pl E)) ⊆ S,
  ∀ (A : Type) (L : LM κ B.a B.b) (w₀ : P) (F : A × B.κ → H E B.a B.b → ℂ), L.Ok P → (∀ i, HasLev (F i)) →
    Quiet S P B e L (Sum.inl ⟨w₀.1, hP w₀.2⟩) F → ∀ p x,
    convF B.ν (fm S P B e L) F (p, x) =
      ∑ y : κ w₀, actP w₀.1 (L.m w₀ (e x w₀) y) (F (p, e.symm (Function.update (e x) w₀ y)))

def FmOff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)]
  (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (A : Type) (L : LM κ B.a B.b) (i₀ : Slot S) (F : A × B.κ → H E B.a B.b → ℂ), L.Ok P → (∀ i, HasLev (F i)) →
    (∀ w ∈ P, ∀ h : w ∈ S, i₀ ≠ Sum.inl ⟨w, h⟩) → Quiet S P B e L i₀ F → ∀ p x,
    convF B.ν (fm S P B e L) F (p, x) = actS L.s L.t i₀ (F (p, x))

def FinActOf : Prop := IntHint → Slots → FinConv → ActAlg → FinAct

def FmAtPOf : Prop := FinConv → FinAct → FmAtP

def FmOffOf : Prop := FinConv → FinAct → FmOff

def FmOneOf : Prop := FmOff → ActIdem → FmOne

def FmPowOf : Prop := FmAlg → FmAtP → Tail.ConvMul → ActAlg → ActIdem → FmPow

end PositivityTheory.Rg.BcB.F.FA

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbC
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd


set_option maxHeartbeats 1000000 in
theorem hecke_setup (hFH : FinHecke) (hBO : BlockOperatorsProductAdjoint) (hFin : FinSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (B : Block E) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (t₀ : PT B) (h₀ : t₀.Ok) (cK : ℂ)
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (Λ : Type) (tΛ : Λ → PT B) (hok : ∀ l, (tΛ l).Ok) (f : ℕ → B.I → H E B.a B.b → ℂ) (hf0 : ∀ k, f k ≠ 0)
    (hflev : ∀ k i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x)
    (r : Λ → ℕ → ℂ) (r₀ : Λ → ℂ) (hr : ∀ l k, convF B.ν (tΛ l).ψ (f k) = r l k • f k)
    (hlim : ∀ l, Tendsto (r l) atTop (𝓝 (r₀ l))) :
    ∃ (hm : Λ → HeckeM E B.a B.b B.I) (lam : ℕ → HeckeM E B.a B.b B.I → ℂ) (lam₀ : HeckeM E B.a B.b B.I → ℂ),
      (∀ k, ∀ h ∈ Set.range hm, heckeAct h (f k) = lam k h • f k) ∧
      (∀ h ∈ Set.range hm, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) ∧
      ∀ l (F : B.I → H E B.a B.b → ℂ),
        (∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x) →
        heckeAct (hm l) F = convF B.ν (tΛ l).ψ F ∧ lam₀ (hm l) = r₀ l := by
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hFinA, hFinB⟩ := hFin E B K₁ K₂ o₁ c₁ o₂ c₂ cK t₀.ψ hcK hψ₀
  have hUo : IsOpen (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact o₁.prod o₂
  have hUc : IsCompact (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact c₁.prod c₂
  have hψF : ∀ l, IsFinM (mulF B.ν (tΛ l).ψ t₀.ψ) := fun l => (hBO E B (tΛ l) t₀ (hok l) h₀).2.2.1.ψ
  have hex := fun l => hFH E B.a B.b B.ν (IxA B.Ma × IxA B.Mb) B.κ (mulF B.ν (tΛ l).ψ t₀.ψ)
    (K₁.prod K₂) (hψF l) hUo hUc (hFinB _ ((hok l).ψ))
  choose hm _ _ hm₃ using hex

  have hact : ∀ l (F : B.I → H E B.a B.b → ℂ),
      (∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x) →
      heckeAct (hm l) F = convF B.ν (tΛ l).ψ F := fun l F hF => by
    rw [← hm₃ l F hF, (hFinA _ F hF).2 _ (hok l).ψ]
  have heig : ∀ l k, heckeAct (hm l) (f k) = r l k • f k := fun l k => by
    rw [hact l (f k) (hflev k), hr l k]

  have hcons : ∀ l l', hm l = hm l' → ∀ k, r l k = r l' k := fun l l' e k =>
    smul_cancel (hf0 k) (by rw [← heig l k, ← heig l' k, e])
  have hcons₀ : ∀ l l', hm l = hm l' → r₀ l = r₀ l' := fun l l' e =>
    tendsto_nhds_unique (hlim l) (by
      have : r l = r l' := funext (hcons l l' e)
      rw [this]; exact hlim l')
  let lam : ℕ → HeckeM E B.a B.b B.I → ℂ := fun k h => if hh : ∃ l, hm l = h then r hh.choose k else 0
  let lam₀ : HeckeM E B.a B.b B.I → ℂ := fun h => if hh : ∃ l, hm l = h then r₀ hh.choose else 0
  have hlam : ∀ l k, lam k (hm l) = r l k := fun l k => by
    have hh : ∃ l', hm l' = hm l := ⟨l, rfl⟩
    simp only [lam, dif_pos hh]
    exact hcons _ _ hh.choose_spec k
  have hlam₀ : ∀ l, lam₀ (hm l) = r₀ l := fun l => by
    have hh : ∃ l', hm l' = hm l := ⟨l, rfl⟩
    simp only [lam₀, dif_pos hh]
    exact hcons₀ _ _ hh.choose_spec
  refine ⟨hm, lam, lam₀, ?_, ?_, fun l F hF => ⟨hact l F hF, hlam₀ l⟩⟩
  · rintro k _ ⟨l, rfl⟩
    rw [hlam, heig]
  · rintro _ ⟨l, rfl⟩
    simp only [hlam, hlam₀]
    exact hlim l

theorem val_tendsto (hVC : ValCont) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B)
    (ht : t.Ok) (χak : ℕ → InfinitePlace E → Inf B.a) (χa : InfinitePlace E → Inf B.a)
    (χbk : ℕ → InfinitePlace E → Inf B.b) (χb : InfinitePlace E → Inf B.b)
    (hA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χa v s) m)))
    (hB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χb v s) m))) :
    Tendsto (fun k => t.val (χak k) (χbk k)) atTop (𝓝 (t.val χa χb)) := by
  unfold PT.val valA
  refine Tendsto.mul (tendsto_finsetProd _ fun v _ => ?_) (tendsto_finsetProd _ fun v _ => ?_)
  · exact hVC B.a B.μa (B.Ma v) (t.ka v) (t.va v) t.T (fun k => χak k v) (χa v) (ht.ka v) (hA v)
  · exact hVC B.b B.μb (B.Mb v) (t.kb v) (t.vb v) t.T (fun k => χbk k v) (χb v) (ht.kb v) (hB v)

set_option maxHeartbeats 2000000 in
theorem blockOut_lim (hFH : FinHecke) (hVC : ValCont) (hIC : InfConv) (hIL : InfLim) (hRE : ReproEx) (hBO : BlockOperatorsProductAdjoint)
    (hFin : FinSt) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ W₁' : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ W₂' : Submodule ℂ (Kinf E B.b → ℂ)) (hW₁ : W₁ ≤ W₁') (hW₂ : W₂ ≤ W₂')
    (Ω₁ Ω₂ Ω₁' Ω₂' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (hΩ₁ : ∀ M, Ω₁ M ⊆ Ω₁' M) (hΩ₂ : ∀ M, Ω₂ M ⊆ Ω₂' M)
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (hEB : EFinalAt E B.a B.b W₁' W₂' Ω₁ Ω₂ K₁ K₂ Θ₁ Θ₂)
    (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (ha₀ : g a₀ = Sum.inr t₀)
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hχ0 : χ (genE g X a₀) ≠ 0)
    (hreg : ∀ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, 1 ≤ m → 0 < B.a → GlobalTheory.Dec.gelfVal (χa v s) m = χ (genE g X (der v s m).1) / χ (genE g X a₀)) →
      (∀ v s m, 1 ≤ m → 0 < B.b → GlobalTheory.Dec.gelfVal (χb v s) m = χ (genE g X (der v s m).2) / χ (genE g X a₀)) →
      RealSym (mOf χa) ∧ RealSym (mOf χb) ∧ ∀ τ, GapM (mOf χa τ) ∧ GapM (mOf χb τ))
    (hK : PerKOut B W₁ W₂ K₁ K₂ g a₀ t₀ der X tX jX χ) :
    Nonempty (BlockOut B g a₀ t₀ X tX jX χ K₁ K₂ W₁' W₂' Θ₁ Θ₂ Ω₁' Ω₂') := by
  obtain ⟨M, sk, f, χak, χbk, hsg, hsX, hgA, hgB, hk⟩ := hK
  have h₀ : t₀.Ok := by have := hok a₀; rw [ha₀] at this; exact this

  choose χa hχa using fun v s => hIL B.a (fun k => χak k v s) _ (hgA v s)
  choose χb hχb using fun v s => hIL B.b (fun k => χbk k v s) _ (hgB v s)
  obtain ⟨hRa, hRb, hGap⟩ := hreg χa χb (fun v s m h1 h2 => by rw [hχa, if_pos ⟨h1, h2⟩])
    (fun v s m h1 h2 => by rw [hχb, if_pos ⟨h1, h2⟩])
  have cA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χa v s) m)) :=
    fun v s m => by rw [hχa]; exact hgA v s m
  have cB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χb v s) m)) :=
    fun v s m => by rw [hχb]; exact hgB v s m

  let Λ := {y : Γ // ∃ t, g y = Sum.inr t ∧ FinType t₀ t} ⊕ Unit
  let tΛ : Λ → PT B := Sum.elim (fun y => y.2.choose) (fun _ => tX)
  have hokΛ : ∀ l, (tΛ l).Ok := by
    rintro (y | _)
    · have := hok y.1; rw [y.2.choose_spec.1] at this; exact this
    · exact htX
  let r : Λ → ℕ → ℂ := Sum.elim (fun y k => sk k (genE g X y.1) / sk k (genE g X a₀))
    (fun _ k => sk k (XE g X) / sk k (genE g X a₀) ^ jX)
  let r₀ : Λ → ℂ := Sum.elim (fun y => χ (genE g X y.1) / χ (genE g X a₀)) (fun _ => χ (XE g X) / χ (genE g X a₀) ^ jX)
  have hr : ∀ l k, convF B.ν (tΛ l).ψ (f k) = r l k • f k := by
    rintro (y | _) k
    · exact (hk k).2.2.2.2.2.2.2.2.2.2.2.2.1 y.1 _ y.2.choose_spec.1 y.2.choose_spec.2
    · exact (hk k).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlim : ∀ l, Tendsto (r l) atTop (𝓝 (r₀ l)) := by
    rintro (y | _)
    · exact (hsg y.1).div (hsg a₀) hχ0
    · exact hsX.div ((hsg a₀).pow jX) (pow_ne_zero _ hχ0)
  have hflev : ∀ k i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x :=
    fun k i u hu x => ((hk k).2.2.2.2.2.1 i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  obtain ⟨hm, lam, lam₀, hHe, hHl, hHF⟩ := hecke_setup hFH hBO hFin B K₁ K₂ o₁ c₁ o₂ c₂ t₀ h₀ cK hcK hψ₀ Λ tΛ hokΛ f
    (fun k => (hk k).2.2.1) hflev r r₀ hr hlim

  obtain ⟨s₁, s₂, F, g₁, g₂, u₁, u₂, l₁, l₂, i₁, i₂, hF0, hFm, hFt, hFh⟩ := hEB B.D B.I M
    (fun k => mOf (χak k)) (fun k => mOf (χbk k)) (mOf χa) (mOf χb) (Set.range hm) lam lam₀ f
    (Set.countable_range hm) (fun N _ _ ν _ K' W' R' hK' hW' => hRE E N ν K' W' R' hK' hW')
    (fun k => (hk k).2.1) (fun k => (hk k).2.2.1) (fun k => (hk k).2.2.2.1) (fun k => (hk k).2.2.2.2.1)
    (fun k i => typeH_mono hW₁ hW₂ ((hk k).2.2.2.2.2.1 i)) (fun k => (hk k).2.2.2.2.2.2.1)
    (fun k => (hk k).2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.2.1)
    (fun k => (hk k).2.2.2.2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.2.2.2.1)
    hHe (fun τ ε hε => (mclose_of hIC χak χa cA τ ε hε).and (mclose_of hIC χbk χb cB τ ε hε))
    hRa hRb hGap hHl
  have hFlev : ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x :=
    fun i u hu x => (hFt i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  have hFeig : ∀ l, convF B.ν (tΛ l).ψ F = r₀ l • F := fun l => by
    obtain ⟨e1, e2⟩ := hHF l F hFlev
    rw [← e1, hFh _ ⟨l, rfl⟩, e2]
  have L₁ : s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁' M, HasType K' W' V) := allLeaves_mono (fun M V h => h.imp id fun ⟨K', hK', W', hW', ht⟩ => ⟨K', hK', W', hΩ₁ M hW', ht⟩) s₁ l₁
  have L₂ : s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂' M, HasType K' W' V) := allLeaves_mono (fun M V h => h.imp id fun ⟨K', hK', W', hW', ht⟩ => ⟨K', hK', W', hΩ₂ M hW', ht⟩) s₂ l₂
  refine ⟨⟨s₁, s₂, F, χa, χb, g₁, g₂, u₁, u₂, L₁, L₂, i₁, i₂, ⟨herm_of_realSym χa hRa, herm_of_realSym χb hRb⟩,
    hF0, hFm, hFt, ?_, ?_, ?_⟩⟩
  · intro x t hx hft
    have l := (Sum.inl ⟨x, t, hx, hft⟩ : Λ)
    have ht : (Classical.choose (⟨t, hx, hft⟩ : ∃ t, g x = Sum.inr t ∧ FinType t₀ t)) = t := by
      have := (Classical.choose_spec (⟨t, hx, hft⟩ : ∃ t, g x = Sum.inr t ∧ FinType t₀ t)).1
      exact Sum.inr_injective (this.symm.trans hx)
    have := hFeig (Sum.inl ⟨x, t, hx, hft⟩)
    simp only [tΛ, r₀, Sum.elim_inl, ht] at this
    exact this
  · intro x t hx hat
    have hto : t.Ok := by have := hok x; rw [hx] at this; exact this
    have e : ∀ k, t.val (χak k) (χbk k) = sk k (genE g X x) := fun k =>
      (hk k).2.2.2.2.2.2.2.2.2.2.2.2.2.2 x t hx hat
    have h1 := val_tendsto hVC B t hto χak χa χbk χb cA cB
    simp only [e] at h1
    exact tendsto_nhds_unique (hsg x) h1
  · exact hFeig (Sum.inr ())

end PositivityTheory.Rg.BcB.F.Rd.B

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PackK
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd


set_option maxHeartbeats 4000000 in
theorem packK (hBO : BlockOperatorsProductAdjoint) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E))))
    (hP : PackAt E B.a B.b B.Ma B.Mb W₁ W₂)
    {Γ : Type} (g : Γ → BGen B) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (ht₀ : t₀.Ok) (hbump : IsBump bump t₀.T)
    (hka0 : ∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) (hkb0 : ∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v))
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hderA : ∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v'))
    (hderB : ∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v'))
    (M : ℕ) (f : B.I → H E B.a B.b → ℂ) (c : ℂ) (σ : Γ → ℂ) (hf : ∀ i, Continuous (f i)) (hf0 : f ≠ 0)
    (hLI : LeftInv f) (hW : WL2 B.D M f) (hc : c ≠ 0) (h0 : PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ f = c • f)
    (hAt : ∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ f = σ y • f) :
    ∃ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, GlobalTheory.Dec.gelfVal (χa v s) m =
        (if 1 ≤ m ∧ 0 < B.a then σ (der v s m).1 else if m = 0 then (B.a : ℂ) * c else 0) / c) ∧
      (∀ v s m, GlobalTheory.Dec.gelfVal (χb v s) m =
        (if 1 ≤ m ∧ 0 < B.b then σ (der v s m).2 else if m = 0 then (B.b : ℂ) * c else 0) / c) ∧
      EigAll χa χb f ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) ∧
      (∀ i m₂, ∃ φ : Sm E B.a, φ.1 = fun x => f i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E B.b, φ.1 = fun x => f i (m₁, x)) ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
      (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
      ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ) := by
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  choose ta hta using hderA
  choose tb htb using hderB
  let ka' : Bool → ℕ → Kers B.Ma := fun s m v =>
    if h : 1 ≤ m ∧ 0 < B.a then (ta v s m h.1 h.2).ka v else if m = 0 then (B.a : ℂ) • t₀.ka v else 0
  let kb' : Bool → ℕ → Kers B.Mb := fun s m v =>
    if h : 1 ≤ m ∧ 0 < B.b then (tb v s m h.1 h.2).kb v else if m = 0 then (B.b : ℂ) • t₀.kb v else 0
  let ca : InfinitePlace E → Bool → ℕ → ℂ := fun v s m =>
    if 1 ≤ m ∧ 0 < B.a then σ (der v s m).1 else if m = 0 then (B.a : ℂ) * c else 0
  let cb : InfinitePlace E → Bool → ℕ → ℂ := fun v s m =>
    if 1 ≤ m ∧ 0 < B.b then σ (der v s m).2 else if m = 0 then (B.b : ℂ) * c else 0
  have hkerA : ∀ s m v, IsKer B.μa (B.Ma v) [(s, m)] bump (ka' s m v) := by
    intro s m v
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · have e1 : ka' s m v = (ta v s m h.1 h.2).ka v := dif_pos h
      rw [e1]; exact (hta v s m h.1 h.2).2.2.2.1
    · by_cases hm : m = 0
      · have e1 : ka' s m v = (B.a : ℂ) • t₀.ka v := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        rw [e1, hm]; exact isKer_smul_rank _ _ _ _ s (hka0 v)
      · have e1 : ka' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have ha : B.a = 0 := by omega
        rw [e1]; exact isKer_zero_rank ha _ _ _ s m
  have hkerB : ∀ s m v, IsKer B.μb (B.Mb v) [(s, m)] bump (kb' s m v) := by
    intro s m v
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · have e1 : kb' s m v = (tb v s m h.1 h.2).kb v := dif_pos h
      rw [e1]; exact (htb v s m h.1 h.2).2.2.2.1
    · by_cases hm : m = 0
      · have e1 : kb' s m v = (B.b : ℂ) • t₀.kb v := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        rw [e1, hm]; exact isKer_smul_rank _ _ _ _ s (hkb0 v)
      · have e1 : kb' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have hb : B.b = 0 := by omega
        rw [e1]; exact isKer_zero_rank hb _ _ _ s m
  have hderA' : ∀ v s m, PositivityTheory.Rg.BcB.E.conv B.D.μ (tens (Function.update t₀.ka v (ka' s m v)) t₀.kb t₀.ψ) f =
      ca v s m • f := by
    intro v s m
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · have e1 : ka' s m v = (ta v s m h.1 h.2).ka v := dif_pos h
      have e2 : ca v s m = σ (der v s m).1 := if_pos h
      obtain ⟨h1, h3, h4, -, h5⟩ := hta v s m h.1 h.2
      have hu : Function.update t₀.ka v ((ta v s m h.1 h.2).ka v) = (ta v s m h.1 h.2).ka := by
        funext v'
        by_cases hv : v' = v
        · subst hv; simp
        · rw [Function.update_of_ne hv]; exact (h5 v' hv).symm
      rw [e1, e2, hu, ← h4, ← show (ta v s m h.1 h.2).ψ = t₀.ψ from h3]
      exact hAt _ _ h1
    · by_cases hm : m = 0
      · have e1 : ka' s m v = (B.a : ℂ) • t₀.ka v := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        have e2 : ca v s m = (B.a : ℂ) * c := by
          show (if 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [if_neg h, if_pos hm]
        rw [e1, e2, tens_update_smul, conv_smulM, show tens t₀.ka t₀.kb t₀.ψ = t₀.Φ from rfl, h0, smul_smul]
      · have e1 : ka' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have e2 : ca v s m = 0 := by
          show (if 1 ≤ m ∧ 0 < B.a then _ else _) = _
          rw [if_neg h, if_neg hm]
        rw [e1, e2, tens_update_zero, conv_zeroM, zero_smul]
  have hderB' : ∀ v s m, PositivityTheory.Rg.BcB.E.conv B.D.μ (tens t₀.ka (Function.update t₀.kb v (kb' s m v)) t₀.ψ) f =
      cb v s m • f := by
    intro v s m
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · have e1 : kb' s m v = (tb v s m h.1 h.2).kb v := dif_pos h
      have e2 : cb v s m = σ (der v s m).2 := if_pos h
      obtain ⟨h1, h3, h4, -, h5⟩ := htb v s m h.1 h.2
      have hu : Function.update t₀.kb v ((tb v s m h.1 h.2).kb v) = (tb v s m h.1 h.2).kb := by
        funext v'
        by_cases hv : v' = v
        · subst hv; simp
        · rw [Function.update_of_ne hv]; exact (h5 v' hv).symm
      rw [e1, e2, hu, ← h4, ← show (tb v s m h.1 h.2).ψ = t₀.ψ from h3]
      exact hAt _ _ h1
    · by_cases hm : m = 0
      · have e1 : kb' s m v = (B.b : ℂ) • t₀.kb v := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_pos hm]
        have e2 : cb v s m = (B.b : ℂ) * c := by
          show (if 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [if_neg h, if_pos hm]
        rw [e1, e2, tens_update_smul_b, conv_smulM, show tens t₀.ka t₀.kb t₀.ψ = t₀.Φ from rfl, h0, smul_smul]
      · have e1 : kb' s m v = 0 := by
          show (if h : 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [dite_eq_right h, if_neg hm]
        have e2 : cb v s m = 0 := by
          show (if 1 ≤ m ∧ 0 < B.b then _ else _) = _
          rw [if_neg h, if_neg hm]
        rw [e1, e2, tens_update_zero_b, conv_zeroM, zero_smul]
  have hψl : ∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, t₀.ψ x y ((u₁, u₂) * h) = t₀.ψ x y h := by
    intro x y u₁ hu₁ u₂ hu₂ h
    have hu : ((u₁, u₂) : Hf E B.a B.b) ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) := Subgroup.mem_prod.2 ⟨hu₁, hu₂⟩
    rw [hψ₀, hψ₀]
    simp only [Subgroup.mul_mem_cancel_left _ hu]
  exact hP B.D B.μa B.μb B.ν B.κ t₀.ka t₀.kb t₀.va t₀.vb t₀.T t₀.ψ bump ka' kb' K₁ K₂ M
    f c ca cb B.compat ht₀.ka ht₀.kb ht₀.ψ hbump hka0 hkb0 hkerA hkerB o₁ o₂
    hψl hf hf0 hLI hW hc h0 hderA' hderB'

end PositivityTheory.Rg.BcB.F.Rd.B

end
end

