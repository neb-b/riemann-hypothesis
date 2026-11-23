module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Tail

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def idem {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) : LF a b w :=
  (U : Set (GLw a w × GLw b w)).indicator fun _ => ((U.relIndex (K2 a b w) : ℕ) : ℂ)

def IsLev (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) : Prop :=
  (∀ w, IsOpen (U w : Set (GLw a w × GLw b w)) ∧ U w ≤ K2 a b w) ∧ ∀ᶠ w in cofinite, U w = K2 a b w

def HasLev (G : H E a b → ℂ) : Prop :=
  ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ u ∈ U, ∀ x, G (x * finH u) = G x

def OfLev (S : Set (Pl E)) (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ) : Prop :=
  HasLev G ∧ ∀ w ∈ S, G ∈ fixed (pairRt a b w) (U₁ w) ∧ (IsSplitAt w → G ∈ fixed (pairRtT a b w) (U₂ w))

def actT (w : Pl E) (u : LF a b w) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRtT a b w m G z

def locM {k : Type} [Fintype k] (w : Pl E) (M : k → k → LF a b w) (G : k → H E a b → ℂ) : k → H E a b → ℂ :=
  fun x => ∑ y, actP w (M x y) (G y)

def DiagIdem {κ : Pl E → Type} (P : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (L : LM κ a b) : Prop :=
  ∀ w ∈ P, ∀ x y, L.m w x y = if x = y then idem (U w) else 0

def FmOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (w₀ : Pl E), IsLev U₁ → IsLev U₂ → L.Ok P → DiagIdem P U₁ L → (∀ i, OfLev S U₁ U₂ (F i)) → w₀ ∈ S →
    (w₀ ∉ P → (∀ w, w ≠ w₀ → L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actP w₀ (L.s w₀) (F i)) ∧
    (IsSplitAt w₀ → (∀ w, L.s w = idem (U₁ w)) → (∀ w, w ≠ w₀ → L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actT w₀ (L.t w₀) (F i))

def FmPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (m : ℕ), IsLev U₁ → IsLev U₂ → L.Ok P → (∀ w, L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
    (∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g) →
    (∀ i, OfLev S U₁ U₂ (F i)) → (convF B.ν (fm S P B e L))^[m] F ≠ 0 →
    ∀ w₀ : P, ∃ (α : A) (x : ∀ w : P, κ w), (locM w₀.1 (L.m w₀.1))^[m] (fun y => F (α, e.symm (Function.update x w₀ y))) ≠ 0

def ConvMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (A : Type)
  (ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (U : Subgroup (Hf E B.a B.b)) (F : A × B.κ → H E B.a B.b → ℂ), IsFinM ψ → IsFinM ψ' →
  IsOpen (U : Set (Hf E B.a B.b)) → (∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) →
    convF B.ν (mulF B.ν ψ ψ') F = convF B.ν ψ (convF B.ν ψ' F) ∧
      ((∀ x y, ∀ u ∈ U, ∀ h, ψ' x y (u * h) = ψ' x y h) → ∀ i, ∀ u ∈ U, ∀ x, convF B.ν ψ' F i (x * finH u) = convF B.ν ψ' F i x)

def LocPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (k : Type) [Fintype k]
  (U : Subgroup (GLw a w × GLw b w)) (G : k → H E a b → ℂ) (m : ℕ), IsOpen (U : Set (GLw a w × GLw b w)) →
  (∀ y, G y ∈ fixed (pairRt a b w) U) →
  (∀ (c : ℂ) (M : k → k → LF a b w), (locM w fun x y => c • M x y)^[m] G ≠ 0 → (locM w M)^[m] G ≠ 0) ∧
    ∀ q : k → LF a b w, (locM w fun x y => if x = y then q x else 0)^[m] G ≠ 0 → ∃ x, (actP w (q x))^[m] (G x) ≠ 0

def ActHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f : LF a b w) (G : H E a b → ℂ),
  HasCompactSupport f → (∀ k ∈ K2 a b w, ∀ g, f (g * k) = f g) →
  (G ∈ fixed (pairRt a b w) (K2 a b w) → actP w f G = GlobalTheory.LFun.heckeVec (pairRt a b w) (K2 a b w) f G) ∧
    (G ∈ fixed (pairRtT a b w) (K2 a b w) → actT w f G = GlobalTheory.LFun.heckeVec (pairRtT a b w) (K2 a b w) f G)

end PositivityTheory.Rg.BcB.F.Tail

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ConjEqConjugate
section
noncomputable section

open NumberField
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

namespace RegH

theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ ≠ τ := by
  intro h
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    exact RingHom.ext fun x => by simpa using congrArg (fun f : E →+* ℂ => f x) h
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]; exact hr
  · rw [e, ComplexEmbedding.isReal_iff.1 hr]; exact hr

theorem conj_eq_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl

theorem mk_conj {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ := by
  rw [conj_eq_conjugate, InfinitePlace.mk_conjugate_eq]

theorem dec_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk ((starRingEnd ℂ).comp τ)).embedding) =
      !decide (τ = (InfinitePlace.mk τ).embedding) := by
  rw [mk_conj]
  have hne := conj_ne τ
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]
    simp [hne]
  · rw [e, ← conj_eq_conjugate]
    have : τ ≠ (starRingEnd ℂ).comp τ := fun h => hne h.symm
    simp [this]

theorem infOf_not {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) :
    PositivityTheory.RgBcC.infOf lam (!s) a = -PositivityTheory.RgBcC.infOf lam s a := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

theorem infOf_im {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) : (PositivityTheory.RgBcC.infOf lam s a).im = 0 := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

theorem infOf_sep {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) (a b : Fin n) (hab : a ≠ b) :
    (1 : ℝ) ≤ ‖PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b‖ := by
  have key : ∀ a b : Fin n, a < b → (1 : ℝ) ≤ ((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) := by
    intro a b h
    have h1 : lam b ≤ lam a := hl h.le
    have h2 : (a : ℕ) + 1 ≤ (b : ℕ) := h
    have h1' : (lam b : ℝ) ≤ lam a := by exact_mod_cast h1
    have h2' : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast h2
    linarith
  have e : ∀ a b : Fin n, PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b =
      ((if s then 1 else -1 : ℂ)) * ((((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) : ℝ) : ℂ) := by
    intro a b
    simp only [PositivityTheory.RgBcC.infOf]
    push_cast
    ring
  have hs : ‖(if s then 1 else -1 : ℂ)‖ = 1 := by cases s <;> simp
  rcases lt_or_gt_of_ne hab with h | h
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (key a b h).trans (le_abs_self _)
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := key b a h
    exact le_abs.mpr (Or.inr (by linarith))

theorem infOf_inj {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) :
    Function.Injective (PositivityTheory.RgBcC.infOf lam s) := by
  intro a b h
  by_contra hab
  have := infOf_sep lam hl s a b hab
  rw [h, sub_self, norm_zero] at this
  norm_num at this

end RegH

open RegH

theorem regDom : RegDom := by
  intro E _ _ _ n l
  refine ⟨fun τ => ⟨?_, ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · intro x hx
    simp only [mOf, Multiset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact infOf_im _ _ _
  · simp only [mOf]
    rw [mk_conj, show decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk τ).embedding) =
        !decide (τ = (InfinitePlace.mk τ).embedding) from by rw [← dec_conj τ, mk_conj], Multiset.map_map]
    congr 1
    funext a
    exact infOf_not _ _ _
  · simp only [mOf]
    exact Multiset.Nodup.map (infOf_inj _ (l _).anti _) Finset.univ.nodup
  · intro x hx y hy hxy
    simp only [mOf, Multiset.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact le_trans (by norm_num) (infOf_sep _ (l _).anti _ a b hab)

theorem reg_of (h : GelfInj) : Reg := by
  intro E _ _ _ n l χ hχ
  have e : mOf χ = mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) := by
    funext τ
    simp only [mOf]
    exact h n _ _ (hχ _ _)
  rw [e]
  exact regDom E n l

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.DetGelfandMatrixEq
section
noncomputable section

open Polynomial Matrix
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

namespace GelfH

def qm (S : Multiset ℂ) : ℂ[X] := (S.map fun c => 1 - C c * X).prod

theorem qm_add (S T : Multiset ℂ) : qm (S + T) = qm S * qm T := by
  simp [qm, Multiset.map_add (f := _), Multiset.prod_add]

theorem one_sub_eq (c : ℂ) (hc : c ≠ 0) : (1 - C c * X : ℂ[X]) = C (-c) * (X - C c⁻¹) := by
  rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hc]
  simp only [C_neg, neg_mul, C_1, sub_neg_eq_add]
  ring

theorem qm_eq (S : Multiset ℂ) :
    qm S = C ((S.filter (· ≠ 0)).map (fun c => -c)).prod * ((S.filter (· ≠ 0)).map fun c => X - C c⁻¹).prod := by
  induction S using Multiset.induction_on with
  | empty => simp [qm]
  | cons a S ih =>
    by_cases ha : a = 0
    · subst ha
      rw [show qm (0 ::ₘ S) = qm S by simp [qm]]
      rw [Multiset.filter_cons_of_neg (p := fun c : ℂ => c ≠ 0) S (by simp)]
      exact ih
    · rw [show qm (a ::ₘ S) = (1 - C a * X) * qm S by simp [qm], ih, Multiset.filter_cons_of_pos (p := fun c : ℂ => c ≠ 0) S ha]
      simp only [Multiset.map_cons, Multiset.prod_cons, C_mul, one_sub_eq a ha]
      ring

theorem roots_qm (S : Multiset ℂ) : (qm S).roots = (S.filter (· ≠ 0)).map fun c => c⁻¹ := by
  rw [qm_eq, roots_C_mul]
  · have := roots_multiset_prod_X_sub_C ((S.filter (· ≠ 0)).map fun c => c⁻¹)
    rw [Multiset.map_map] at this
    exact this
  · exact Multiset.prod_ne_zero (by simp)

theorem filter_eq_of_qm {S T : Multiset ℂ} (h : qm S = qm T) : S.filter (· ≠ 0) = T.filter (· ≠ 0) := by
  have e := congrArg Polynomial.roots h
  rw [roots_qm, roots_qm] at e
  have e2 := congrArg (Multiset.map fun c : ℂ => c⁻¹) e
  simp only [Multiset.map_map, Function.comp_def, inv_inv, Multiset.map_id'] at e2
  exact e2

theorem eq_of_qm {S T : Multiset ℂ} (h : qm S = qm T) (hc : Multiset.card S = Multiset.card T) : S = T := by
  have h1 := filter_eq_of_qm h
  have hS := Multiset.filter_add_not (· ≠ (0 : ℂ)) S
  have hT := Multiset.filter_add_not (· ≠ (0 : ℂ)) T
  have z1 : S.filter (fun c => ¬ c ≠ 0) = Multiset.replicate (Multiset.card (S.filter fun c => ¬ c ≠ 0)) 0 :=
    Multiset.eq_replicate.2 ⟨rfl, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩
  have z2 : T.filter (fun c => ¬ c ≠ 0) = Multiset.replicate (Multiset.card (T.filter fun c => ¬ c ≠ 0)) 0 :=
    Multiset.eq_replicate.2 ⟨rfl, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩
  have cS := congrArg Multiset.card hS
  have cT := congrArg Multiset.card hT
  rw [Multiset.card_add] at cS cT
  rw [← hS, ← hT, h1, z1, z2]
  congr 2
  rw [h1] at cS
  omega

def sh (M : Multiset ℂ) : Multiset ℂ := M.map (· + 1)

theorem count_sh_top {M : Multiset ℂ} {x : ℂ} (hx : ∀ c ∈ M, c.re ≤ x.re) : M.count (x + 1) = 0 :=
  Multiset.count_eq_zero.2 fun h => by have := hx _ h; simp at this; linarith

theorem count_sh (M : Multiset ℂ) (x : ℂ) : (sh M).count (x + 1) = M.count x := by
  rw [sh, Multiset.count_map_eq_count' _ _ (add_left_injective 1)]

theorem eq_of_shift : ∀ (N : ℕ) (a b : Multiset ℂ), Multiset.card a + Multiset.card b = N →
    a + sh b = b + sh a → a = b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a b hN h
  by_cases h0 : a + b = 0
  · rw [add_eq_zero] at h0
    rw [h0.1, h0.2]
  obtain ⟨x, hx, hmax⟩ : ∃ x ∈ a + b, ∀ c ∈ a + b, c.re ≤ x.re := by
    exact Multiset.exists_max_image (fun c : ℂ => c.re) h0
  have ha : ∀ c ∈ a, c.re ≤ x.re := fun c hc => hmax c (Multiset.mem_add.2 (Or.inl hc))
  have hb : ∀ c ∈ b, c.re ≤ x.re := fun c hc => hmax c (Multiset.mem_add.2 (Or.inr hc))
  have e := congrArg (fun M => Multiset.count (x + 1) M) h
  simp only [Multiset.count_add, count_sh_top ha, count_sh_top hb, count_sh, zero_add] at e
  have hxa : x ∈ a := by
    rcases Multiset.mem_add.1 hx with h1 | h1
    · exact h1
    · rw [← Multiset.count_pos, ← e]; exact Multiset.count_pos.2 h1
  have hxb : x ∈ b := by rw [← Multiset.count_pos, e]; exact Multiset.count_pos.2 hxa
  obtain ⟨a', rfl⟩ := Multiset.exists_cons_of_mem hxa
  obtain ⟨b', rfl⟩ := Multiset.exists_cons_of_mem hxb
  have e1 : x ::ₘ a' + sh (x ::ₘ b') = x ::ₘ (x + 1) ::ₘ (a' + sh b') := by
    rw [sh, sh, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
  have e2 : x ::ₘ b' + sh (x ::ₘ a') = x ::ₘ (x + 1) ::ₘ (b' + sh a') := by
    rw [sh, sh, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
  rw [e1, e2] at h
  have h' : a' + sh b' = b' + sh a' := (Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 h)
  have := ih (Multiset.card a' + Multiset.card b') (by rw [← hN]; simp; omega) a' b' rfl h'
  rw [this]

end GelfH

namespace GelfM

open PowerSeries

variable {n : ℕ}

def S (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ⟦X⟧ := Matrix.of fun i j => mk fun k => (A ^ k) i j

def M (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ⟦X⟧ := 1 - (PowerSeries.X : ℂ⟦X⟧) • A.map (fun a => (PowerSeries.C a : ℂ⟦X⟧))

theorem mapC_mul_S (A : Matrix (Fin n) (Fin n) ℂ) :
    A.map (fun a => (PowerSeries.C a : ℂ⟦X⟧)) * S A = Matrix.of fun i j => mk fun k => (A ^ (k + 1)) i j := by
  ext i j m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, S, Matrix.map_apply, Matrix.of_apply, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  rw [pow_succ', Matrix.mul_apply]

theorem X_mul_shift (f : ℕ → ℂ) : (PowerSeries.X : ℂ⟦X⟧) * mk (fun k => f (k + 1)) = mk f - PowerSeries.C (f 0) := by
  refine PowerSeries.ext (R := ℂ) fun m => ?_
  cases m with
  | zero => simp [coeff_zero_X_mul]
  | succ m => simp [coeff_succ_X_mul]

theorem M_mul_S (A : Matrix (Fin n) (Fin n) ℂ) : M A * S A = 1 := by
  rw [M, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, mapC_mul_S]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, S]
  rw [X_mul_shift (fun k => (A ^ k) i j)]
  simp only [pow_zero, sub_sub_cancel]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem isUnit_det (A : Matrix (Fin n) (Fin n) ℂ) : IsUnit (M A).det := by
  have h := congrArg Matrix.det (M_mul_S A)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem inv_M (A : Matrix (Fin n) (Fin n) ℂ) : (M A)⁻¹ = S A := Matrix.inv_eq_right_inv (M_mul_S A)

def tot (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ := ∑ a, ∑ b, (A ^ k) a b

theorem det_rank_one (A : Matrix (Fin n) (Fin n) ℂ) :
    (M A + Matrix.replicateCol (Fin 1) (fun _ => -(PowerSeries.X : ℂ⟦X⟧)) * Matrix.replicateRow (Fin 1) (fun _ => (1 : ℂ⟦X⟧))).det =
      (M A).det * (1 - PowerSeries.X * mk (tot A)) := by
  refine (Matrix.det_add_replicateCol_mul_replicateRow (ι := Fin 1) (isUnit_det A) _ _).trans ?_
  rw [inv_M]
  have hdet : ∀ B : Matrix (Fin 1) (Fin 1) ℂ⟦X⟧,
      @Matrix.det (Fin 1) (fun a b => decidableEq_of_subsingleton a b) Unique.fintype _ _ B = B 0 0 := fun B => by
    exact Matrix.det_unique B
  rw [hdet]
  have hsum : ∑ i, ∑ j, S A i j = mk (tot A) := by
    refine PowerSeries.ext (R := ℂ) fun m => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp [S, tot, map_sum, coeff_mk]
  congr 1
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, one_mul]
  rw [← Finset.sum_mul, Finset.sum_comm, hsum]
  ring

end GelfM

namespace GelfM

open PowerSeries

variable {n : ℕ}

theorem coe_qm (S : Multiset ℂ) :
    Polynomial.coeToPowerSeries.ringHom (GelfH.qm S) = (S.map fun c => 1 - PowerSeries.C c * PowerSeries.X).prod := by
  rw [GelfH.qm, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun c _ => ?_
  simp only [Function.comp_apply, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X]

theorem det_M (l : Fin n → ℂ) :
    (M (Formalism.REAL.Amat l)).det = Polynomial.coeToPowerSeries.ringHom (GelfH.qm (Finset.univ.val.map l)) := by
  rw [Matrix.det_of_isUpperTriangular, coe_qm, Multiset.map_map]
  · rw [show (Finset.univ.val.map ((fun c => 1 - PowerSeries.C c * PowerSeries.X) ∘ l)) =
        Finset.univ.val.map (fun i => M (Formalism.REAL.Amat l) i i) from ?_]
    · rfl
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [M, Formalism.REAL.Amat, mul_comm]
  · intro i j hij
    have h1 : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    have h2 : ¬ i < j := fun h => lt_asymm h hij
    simp [M, Formalism.REAL.Amat, h1, h2]

def M1 (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ⟦X⟧ :=
  M A + Matrix.replicateCol (Fin 1) (fun _ => -(PowerSeries.X : ℂ⟦X⟧)) * Matrix.replicateRow (Fin 1) (fun _ => (1 : ℂ⟦X⟧))

theorem det_gelfand_matrix_eq (l : Fin n → ℂ) :
    (M1 (Formalism.REAL.Amat l)).det = Polynomial.coeToPowerSeries.ringHom (GelfH.qm (GelfH.sh (Finset.univ.val.map l))) := by
  rw [Matrix.det_of_isLowerTriangular, coe_qm, GelfH.sh, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  · congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [M1, M, Formalism.REAL.Amat, Matrix.mul_apply]
    ring
  · intro i j hij
    have h3 : i < j := hij
    have h1 : i ≠ j := ne_of_lt h3
    simp [M1, M, Formalism.REAL.Amat, h1, h3, Matrix.mul_apply]

theorem key (l : Fin n → ℂ) :
    Polynomial.coeToPowerSeries.ringHom (GelfH.qm (GelfH.sh (Finset.univ.val.map l))) =
      Polynomial.coeToPowerSeries.ringHom (GelfH.qm (Finset.univ.val.map l)) * (1 - PowerSeries.X * mk (tot (Formalism.REAL.Amat l))) := by
  rw [← det_gelfand_matrix_eq, M1, det_rank_one, det_M]

end GelfM

open GelfH GelfM in
theorem gelfInj : GelfInj := by
  intro n x y h
  set l : Fin n → ℂ := fun c => x c + ((n : ℂ) - 1) / 2 with hl
  set l' : Fin n → ℂ := fun c => y c + ((n : ℂ) - 1) / 2 with hl'
  have ht : tot (Formalism.REAL.Amat l) = tot (Formalism.REAL.Amat l') := funext fun k => h k
  have k1 := key l
  have k2 := key l'
  rw [← ht] at k2
  set a := Finset.univ.val.map l
  set b := Finset.univ.val.map l'
  have e : Polynomial.coeToPowerSeries.ringHom (qm (a + sh b)) = Polynomial.coeToPowerSeries.ringHom (qm (b + sh a)) := by
    rw [qm_add, qm_add, map_mul, map_mul, k1, k2]
    ring
  have e2 : qm (a + sh b) = qm (b + sh a) := Polynomial.coe_injective ℂ (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using e)
  have hc : Multiset.card (a + sh b) = Multiset.card (b + sh a) := by simp [a, b, sh]
  have e3 := eq_of_qm e2 hc
  have e4 := eq_of_shift _ a b rfl e3
  have e5 := congrArg (Multiset.map fun c => c - ((n : ℂ) - 1) / 2) e4
  simp only [a, b, Multiset.map_map, Function.comp_def, hl, hl', add_sub_cancel_right] at e5
  exact e5

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
end

