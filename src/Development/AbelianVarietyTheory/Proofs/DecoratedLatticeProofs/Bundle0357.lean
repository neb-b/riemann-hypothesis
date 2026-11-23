module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.LastTwoSteps
open GlobalTheory.StepData GlobalTheory.SymChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intInd_mem_SB (a b : Type) [Fintype a] [Fintype b] :
    Set.indicator {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈ SB (Matrix a b k) := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix a b k) := inferInstanceAs (T2Space (a → b → k))
  have e : {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} =
      Set.pi Set.univ fun _ : a => Set.pi Set.univ fun _ : b => (𝒪[k] : Set k) := by
    ext x; exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩
  have hK : IsCompact {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have ho : IsOpen {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have := GlobalTheory.FinPl.Comm.ite_mem_SB hK ho
  convert this using 1
  funext x
  by_cases h : ∀ r q, x r q ∈ 𝒪[k] <;> simp [Set.indicator_apply, h]

variable [MeasurableSpace k] [BorelSpace k]

theorem hat_const_mul {n : Type} [Fintype n] (ψ : AddChar k Circle) (ν : Measure k) (ε : k) (c : ℂ)
    (f : (n → k) → ℂ) (η : n → k) : hat ψ ν ε (fun y => c * f y) η = c * hat ψ ν ε f η := by
  simp only [hat, mul_assoc]
  rw [integral_const_mul]


open Classical in
theorem hat_int {n : Type} [Fintype n] [DecidableEq n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k}
    (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (η : n → k) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0)) η = if ∀ i, η i ∈ 𝒪[k] then 1 else 0 := by
  classical
  have := hν.1
  have := secondCountable k
  split_ifs with hη
  · have hε' : ε ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, hε]
    rw [GlobalTheory.StepData.Model.hat_coset hψ hν hε' 0 hη]
    simp
  · have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) (x + z) =
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) x := fun z hz x => by
      have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
        (Submodule.Quotient.eq _).2 (by simpa using hz)
      simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
    refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
      (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
    · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

section Entries
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

theorem psi_mem_SB (T : Chain k s X Z) (hT : T.Regular) (y : X (s + 1) → k) :
    (fun x₀ => T.Psi 1 x₀ y) ∈ SB (Matrix (X (s + 1)) (X s) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := X (s + 1)) (n' := X s)
  refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (T.mu (s + 1)) 1 1 (hT.1 s 0 rfl))
    (p := fun x₀ => withCol x₀ y) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
  · unfold withCol; fun_prop
  · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))

variable [MeasurableSpace k] [BorelSpace k]

theorem xiTop_mem_SB (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) (1 : kˣ)) :
    T.xiTop (box _ (1 : kˣ)) ψ ν ε yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν ε hψ hν hε (X (s + 1)) 1 1 _ (cosetInd_mem_SB 1 yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

end Entries

section Ones
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [Fintype c]


open Classical in
theorem cosetInd_zero (y : a → k) :
    cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y = if ∀ i, y i ∈ 𝒪[k] then 1 else 0 := by
  have hy : (Submodule.Quotient.mk y : (a → k) ⧸ box a (1 : kˣ)) = Submodule.Quotient.mk 0 ↔ ∀ i, y i ∈ 𝒪[k] := by
    simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
  unfold cosetInd
  by_cases h : ∀ i, y i ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (hy.2 h), if_pos h]
  · rw [Set.indicator_of_notMem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (mt hy.1 h), if_neg h]


open Classical in
theorem intInd_fromCols (q : Matrix a b k) (y : a → k) :
    Set.indicator {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ))
        (fromCols q (Matrix.of fun r _ => y r)) =
      Set.indicator {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q *
        cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
  have hf : (∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]) ↔
      (∀ r c, q r c ∈ 𝒪[k]) ∧ ∀ i, y i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => by simpa using h r (Sum.inl c), fun r => by simpa using h r (Sum.inr ())⟩
    · rintro ⟨hq, hy⟩ r (c | c)
      · simpa using hq r c
      · simpa using hy r
  rw [cosetInd_zero]
  by_cases h : ∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h,
      Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) (hf.1 h).1, if_pos (hf.1 h).2,
      mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h]
    by_cases hq : ∀ r c, q r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq,
        if_neg fun h2 => h (hf.2 ⟨hq, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq, zero_mul]


open Classical in
theorem intInd_rows (q : Matrix (c ⊕ Unit) a k) :
    Set.indicator {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q =
      Set.indicator {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q.toRows₁ *
        if ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] then 1 else 0 := by
  have hr : (∀ r c, q r c ∈ 𝒪[k]) ↔ (∀ r c, q.toRows₁ r c ∈ 𝒪[k]) ∧ ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => h (Sum.inl r) c, fun i => h (Sum.inr ()) i⟩
    · rintro ⟨hr, hη⟩ (r | r) c
      · exact hr r c
      · exact hη c
  by_cases h : ∀ r c, q r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h,
      Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) (hr.1 h).1,
      if_pos (hr.1 h).2, mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h]
    by_cases h1 : ∀ r c, q.toRows₁ r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1,
        if_neg fun h2 => h (hr.2 ⟨h1, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1, zero_mul]

end Ones

theorem gLast : ∀ (D : D7), LastLoc D → GlobalTheory.SymChain.AtMostOne → GLast D := by
  classical
  intro D hLL hAMO k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    FA F₀ FS FT FX hcore hFX c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have := hν.1
  obtain ⟨-, -, h1, h2, -⟩ := hAMO k ν hν s κ S t
  obtain ⟨Λ, hΛ, hK⟩ := hLL k p ν hν.1 ψ hstd S.ψ hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz _ _ _ FA F₀ FS FT FX
    hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hreg : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have hv1 : valuation k (-1 : k) = 1 := by simp
  let Ξ₁ : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, psi_mem_SB _ hreg (S.y0 t)⟩
  let Ξ₂ : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) :=
    ⟨_, xiTop_mem_SB _ hreg S.cond hν hv1 (Submodule.Quotient.mk (S.y0 t))⟩
  let O₁' : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) := ⟨_, intInd_mem_SB _ _⟩
  have hcp : ∀ x₀ y, (S.T t).Psi 1 x₀ y =
      (S.T t).Psi 1 x₀ (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := fun x₀ y => by
    by_cases hy : y - S.y0 t ∈ box _ (1 : kˣ)
    · rw [h2 x₀ y hy, cosetInd, Set.indicator_of_mem, mul_one]
      exact (Submodule.Quotient.eq _).2 hy
    · rw [cosetInd, Set.indicator_of_notMem, mul_zero]
      · exact not_not.1 (mt (h1 x₀ y) hy)
      · exact fun h => hy ((Submodule.Quotient.eq _).1 h)
  have hprod : ∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2 := fun q => by
    rw [hΞ q, hΦ₂]
    have e : (fun y => Φ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        (S.T t).Psi 1 q.1 (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := by
      funext y
      rw [hΦ₁, ← hcp]
      rfl
    rw [e, hat_const_mul]
    show _ = (S.T t).Psi 1 q.1 (S.y0 t) * ((S.T t).PhiTop (fromCols q.2.toRows₁ 0) * _)
    ring
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact intInd_fromCols q.1 y
    rw [e, hat_const_mul, hat_int S.cond hν hv1]
    simp only [O₁', O₂']
    rw [intInd_rows q.2]
    ring
  have key := (_root_.GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A W X FA FS FX Λ c₁ c₂ Ξ₁ O₁' Ξ₂ O₂' Ξ Ξ' hΛ hc₁ hc₂ rfl rfl hprod hone
  have e1 := funext hΞK
  have e2 := funext hΞ'K
  rw [e1, e2]
  exact key

end GlobalTheory.LastTwoSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicator
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TOneModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem pi_e : p.π p.e = 1 := by
  have h : p.ι 1 = p.e := by simpa using p.ι_π 1
  rw [← h, p.π_ι]

theorem pi_of_mul {e : AE D} (he : e * p.e = 0) : p.π e = 0 := by
  have h := congrArg p.π he
  rwa [map_mul, pi_e, mul_one, map_zero] at h

theorem up_down_eq (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun a => p.e * a) := by
  unfold Place.up Place.down
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply]
  exact p.ι_π _

theorem down_half_zero (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0) {x : WO S T}
    (hx : IsHalf e x) : p.down FS FT x = 0 := by
  unfold Place.down
  have h : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, pi_of_mul p he, zero_mul]
  rw [h, Matrix.mul_zero, Matrix.zero_mul]

theorem half_sum {e : AE D} (he : e * p.e = 0) {x : WO S T} (hx : IsHalf e x) : IsHalf (e + p.e) x := by
  intro i j
  have h : p.e * x i j = 0 := by rw [← hx i j, ← mul_assoc, mul_comm p.e e, he, zero_mul]
  rw [add_mul, hx i j, h, add_zero]

theorem half_sum_conj {e : AE D} (he : e * p.e = 0) {y : WO S T} (hy : IsHalf (cA D e) y) :
    IsHalf (cA D (e + p.e)) y := by
  intro i j
  have h : cA D p.e * y i j = 0 := by
    rw [← hy i j, ← mul_assoc, ← map_mul, mul_comm p.e e, he, map_zero, zero_mul]
  rw [map_add (f := _), add_mul, hy i j, h, add_zero]

theorem hO_zero {e : AE D} (he : e * p.e = 0) {w y : WO S T} (hw : IsHalf p.e w) (hy : IsHalf (cA D e) y) :
    hO S T w y = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have h1 : cA D (y c b) = e * cA D (y c b) := by
    conv_lhs => rw [← hy c b, map_mul, Formalism.L2.Theta.cA_cA]
  rw [h1, ← hw d a]
  linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * w d a) * he

theorem symplO_sub_half {e : AE D} (he : e * p.e = 0) (t : WO S T) {w y : WO S T} (hw : IsHalf p.e w)
    (hy : IsHalf (cA D e) y) : symplO S T (t - w) y = symplO S T t y := by
  have h : hO S T (t - w) y = hO S T t y - hO S T w y := by
    simp only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  unfold symplO
  rw [h, hO_zero p he hw hy, sub_zero]

end GlobalTheory.LocMod.TOneModel

namespace GlobalTheory.LocMod.TOneModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem tensorOne_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorOne FS FT (fun t => Φ (t + x)) = fun t => p.tensorOne FS FT Φ (t + x) := by
  funext t
  simp only [Place.tensorOne_apply, Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, down_half_zero p FS FT he hx, add_zero, sub_add_eq_add_sub]

theorem tensorOne_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorOne FS FT (fun t => ψ (symplO S T t y) * Φ t) = fun t => ψ (symplO S T t y) * p.tensorOne FS FT Φ t := by
  funext t
  simp only [Place.tensorOne_apply, Place.tensorAt]
  rw [symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]

open Classical in
theorem intInd_eq (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (hint : ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) (x : Matrix Y Y' k) :
    Place.intInd Y Y' x = if p.up FS FT x ∈ stdHom S T then 1 else 0 := by
  classical
  unfold Place.intInd
  rw [Set.indicator_apply]
  exact if_congr (hint x) rfl rfl

theorem tensorOne_vac (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (hint : ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T)
    (hstab : ∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) :
    p.tensorOne FS FT ((1 : ℂ) • halfInd e (stdHom S T)) = (1 : ℂ) • halfInd (e + p.e) (stdHom S T) := by
  classical
  funext t
  simp only [one_smul]
  rw [Place.tensorOne_apply]
  simp only [Place.tensorAt]
  rw [intInd_eq p FS FT hint, up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ stdHom S T ∧ IsHalf e (t - M)) ∧ M ∈ stdHom S T) ↔ (t ∈ stdHom S T ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ stdHom S T := hstab t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ stdHom S T ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ stdHom S T
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

theorem isPlaceModel_tensorOne : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → (∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ, IsSBHalf e (stdHom S T) Φ → IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ (Place.intInd Y Y'))) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ (T' ∘ₗ p.tensorOne FS FT) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he hint hstab f₀ T' hT' hsb
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.comp_apply, tensorOne_trans p FS FT he Φ hx]
    exact hT'.trans (p.tensorOne FS FT Φ) (hsb Φ hΦ) x (half_sum p he hx)
  · rw [LinearMap.comp_apply, tensorOne_modul p ψ FS FT he Φ hy]
    exact hT'.modul (p.tensorOne FS FT Φ) (hsb Φ hΦ) y (half_sum_conj p he hy)
  · rw [LinearMap.comp_apply, tensorOne_vac p FS FT he hint hstab]
    exact hT'.vac

end GlobalTheory.LocMod.TOneModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem padicValRat_pow_mul_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a * s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.mul (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem padicValRat_pow_div_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a / s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.div (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem unitRatio_ne_zero {S : ℕ → Prop} {x y : ℂ} (h : UnitRatio S x y) : x ≠ 0 := by
  obtain ⟨hy, n, hn, r, hr, he, -⟩ := h
  intro hx
  rw [hx, zero_div, zero_pow hn.ne'] at he
  exact hr (by exact_mod_cast he.symm)

theorem unitRatio_refl (S : ℕ → Prop) {y : ℂ} (hy : y ≠ 0) : UnitRatio S y y :=
  ⟨hy, 1, one_pos, 1, one_ne_zero, by simp [div_self hy], fun p _ h => by simp at h⟩

theorem unitRatio_mul {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x * x') (y * y') := by
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨mul_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' * r' ^ n,
    mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x * x' / (y * y') = (x / y) * (x' / y') := by field_simp
    rw [this, mul_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_mul_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_div {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x / x') (y / y') := by
  have hx' := unitRatio_ne_zero h'
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨div_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' / r' ^ n,
    div_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x / x' / (y / y') = (x / y) / (x' / y') := by field_simp
    rw [this, div_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_div_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_of_pow_eq (S : ℕ → Prop) {x y : ℂ} {n : ℕ} (hy : y ≠ 0) (hn : 0 < n) (h : x ^ n = y ^ n) :
    UnitRatio S x y :=
  ⟨hy, n, hn, 1, one_ne_zero, by rw [div_pow, h, div_self (pow_ne_zero _ hy)]; simp, fun p _ h => by simp at h⟩

theorem unitRatio_prod (S : ℕ → Prop) {I : Type} (s : Finset I) (x y : I → ℂ)
    (h : ∀ i ∈ s, UnitRatio S (x i) (y i)) : UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitRatio_refl S one_ne_zero
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact unitRatio_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitRatio_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) :=
  fun S => ⟨fun y hy => unitRatio_refl S hy,
    fun x y x' y' h h' => ⟨unitRatio_mul h h', unitRatio_div h h', unitRatio_ne_zero h⟩,
    fun x y n hy hn h => unitRatio_of_pow_eq S hy hn h,
    fun I s x y h => unitRatio_prod S s x y h⟩

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SBHalfAt

theorem isSBHalf_extFun_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT Ψ hΨ
  exact GlobalTheory.FinPl.CombProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ

end GlobalTheory.FinPl.SBHalfAt
end

