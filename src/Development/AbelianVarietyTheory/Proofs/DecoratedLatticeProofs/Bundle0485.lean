module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionsDoubleIntegralExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch


open GlobalTheory.LatPair in
theorem exists_pair_of_line {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (Λ : Submodule 𝒪[k] (n ⊕ Fin 1 → k)) (hΛ : Λ.IsFullLattice k) (q : Unif k) (m : k)
    (h1 : ∀ t : k, (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k) ∈ Λ ↔ m * t ∈ 𝒪[k])
    (h2 : ∀ s : k, (∀ x ∈ Λ, s * ((q.1 : k) * (m * x (Sum.inr 0))) ∈ 𝒪[k]) ↔ s ∈ 𝒪[k]) :
    ∃ P : Pair k n, ∀ x : n ⊕ Fin 1 → k, x ∈ Λ ↔
      Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ gluedS q 1 P.ker P.vec := by
  have hq := GlobalTheory.LevelUnfold.mul_inv_q q
  have hint : ∀ x ∈ Λ, (q.1 : k) * (m * x (Sum.inr 0)) ∈ 𝒪[k] := fun x hx => by
    simpa using (h2 1).2 (one_mem _) x hx
  have hqi : q.inv ∉ 𝒪[k] := fun h => q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext hq))
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Λ, (q.1 : k) * (m * e (Sum.inr 0)) = 1 := by
    have h := mt (h2 q.inv).1 hqi
    push Not at h
    obtain ⟨x, hx, hx'⟩ := h
    have hu : IsUnit (⟨_, hint x hx⟩ : 𝒪[k]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, q.mem_max_iff]
      rintro ⟨c, hc⟩
      have hc' : (q.1 : k) * (m * x (Sum.inr 0)) = (q.1 : k) * c := congrArg Subtype.val hc
      apply hx'
      rw [hc', ← mul_assoc, mul_comm q.inv, hq, one_mul]
      exact c.2
    obtain ⟨c, hc⟩ := hu.exists_left_inv
    have hc' : (c : k) * ((q.1 : k) * (m * x (Sum.inr 0))) = 1 := congrArg Subtype.val hc
    refine ⟨c • x, Λ.smul_mem c hx, ?_⟩
    rw [← hc']
    change _ * (m * ((c : k) * _)) = _
    ring
  have hsplit : ∀ x : n ⊕ Fin 1 → k, x = inX k n 1 (x ∘ Sum.inl) + (Sum.elim 0 (fun _ => x (Sum.inr 0)) : n ⊕ Fin 1 → k) := fun x => by
    ext (j | j)
    · simp [inX]
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [inX]
  let L : Submodule 𝒪[k] (n → k) := Λ.comap (inX k n 1)
  have hL : ∀ x : n ⊕ Fin 1 → k, m * x (Sum.inr 0) ∈ 𝒪[k] → (x ∈ Λ ↔ x ∘ Sum.inl ∈ L) := fun x hx => by
    conv_lhs => rw [hsplit x]
    exact Λ.add_mem_iff_left ((h1 _).2 hx)
  have key : ∀ (x : n ⊕ Fin 1 → k) (s : 𝒪[k]), (q.1 : k) * (m * x (Sum.inr 0)) = s →
      (x ∈ Λ ↔ x ∘ Sum.inl - s • (e ∘ Sum.inl) ∈ L) := fun x s hs => by
    rw [← Λ.sub_mem_iff_left (Λ.smul_mem s he)]
    refine hL (x - s • e) ?_
    have h0 : (q.1 : k) * (m * (x - s • e) (Sum.inr 0)) = 0 := by
      change (q.1 : k) * (m * (x _ - (s : k) * e _)) = 0
      linear_combination hs - (s : k) * he1
    rw [(mul_eq_zero.1 h0).resolve_left q.ne_zero]
    exact zero_mem _
  have hqe : q.1 • (e ∘ Sum.inl) ∈ L := by
    refine (hL (q.1 • e) ?_).1 (Λ.smul_mem _ he)
    change m * ((q.1 : k) * e _) ∈ _
    rw [mul_left_comm, he1]
    exact one_mem _
  have hlat : L.IsLattice k := by
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (inX k n 1) (fun x y h => ?_) (hΛ.fg.of_le (Submodule.map_comap_le _ _))
      funext j
      exact congrFun h (Sum.inl j)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  have hfull : L.IsFullLattice k := by
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro y _
    have hy : inX k n 1 y ∈ Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)) := by
      rw [hΛ.span_eq_top]
      trivial
    have hproj : ∀ x ∈ Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)),
        x ∘ Sum.inl ∈ Submodule.span k (L : Set (n → k)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have hm : q.1 • (x ∘ Sum.inl) ∈ L := by
          refine (hL (q.1 • x) ?_).1 (Λ.smul_mem _ hx)
          change m * ((q.1 : k) * x (Sum.inr 0)) ∈ 𝒪[k]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hint x hx
        have := Submodule.smul_mem (Submodule.span k (L : Set (n → k))) q.inv (Submodule.subset_span hm)
        simpa using this
      | zero => simp
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx => exact Submodule.smul_mem _ a hx
    simpa [inX] using hproj _ hy
  have hglue : IsGlue L (e ∘ Sum.inl) := by
    refine (isGlue_iff q).2 ⟨hfull, fun h => hqi ?_, hqe⟩
    have h3 : (Sum.elim 0 (fun _ => e (Sum.inr 0)) : n ⊕ Fin 1 → k) ∈ Λ := by
      rw [← Λ.add_mem_iff_right (show inX k n 1 (e ∘ Sum.inl) ∈ Λ from h), ← hsplit]
      exact he
    have h4 : q.inv = m * e (Sum.inr 0) := by
      rw [← mul_one q.inv, ← he1, ← mul_assoc, mul_comm q.inv, hq, one_mul]
    rw [h4]
    exact (h1 _).1 h3
  obtain ⟨P, hk, hv⟩ := hglue.exists_pair
  have hd : e ∘ Sum.inl - P.vec ∈ L := hk ▸ Pair.sub_vec_mem hv
  have hvec : ∀ (y : n → k) (s : 𝒪[k]), y - s • (e ∘ Sum.inl) ∈ L ↔ y - s • P.vec ∈ L := fun y s => by
    rw [← L.add_mem_iff_left (L.smul_mem s hd), smul_sub, sub_add_sub_cancel]
  refine ⟨P, fun x => ?_⟩
  rw [GlobalTheory.LevelUnfold.mem_gluedS, hk]
  constructor
  · intro hx
    refine ⟨⟨_, hint x hx⟩, (hvec _ _).1 ((key x _ rfl).1 hx), fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change m * x _ = q.inv * ((q.1 : k) * _)
    rw [← mul_assoc, mul_comm q.inv, hq, one_mul]
  · rintro ⟨s, hs, hs'⟩
    have h3 : m * x (Sum.inr 0) = q.inv * s := (hs' 0).1 rfl
    refine (key x s ?_).2 ((hvec _ _).2 hs)
    rw [h3, ← mul_assoc, hq, one_mul]

section Place

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.CoreGlue

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem pr_cA_sec (c : k) : p.pr (cA D (p.sec c)) = 0 := by
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h0 : p.e * cA D (p.sec c) = 0 := by
    rw [← cA_cA p.e, ← map_mul, ← e_mul_sec p c, ← mul_assoc, cAe_mul_e, zero_mul, map_zero]
  have h1 := congrArg p.pr h0
  rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1

theorem mul_sec_mem_intAt_iff (a : AE D) (t : k) : a * p.sec t ∈ intAt D (· = p.v) ↔ p.pr a * t ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mem_intAt_iff p (sec_mem_idAt p _), pr_cA_sec, p.pr_sec, and_iff_left (zero_mem _), mul_comm]

theorem cA_sec_mul (a : AE D) (t : k) : cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem mul_cA_sec_mem_intAt_iff (a : AE D) (t : k) :
    a * cA D (p.sec t) ∈ intAt D (· = p.v) ↔ p.pr (cA D a) * t ∈ 𝒪[k] := by
  rw [mul_comm, cA_sec_mul, mem_intAt_iff p (csec_mem_idAt _), pr_cA_sec, cA_cA, p.pr_sec, and_iff_right (zero_mem _), mul_comm]

theorem exists_gluedW : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M μ T q hs hM hμ hline hnorm hT
  have hb : p.pr (incA D (star μ)) ≠ 0 := (map_ne_zero (p.pr.comp (incA D))).2 (star_ne_zero.2 hμ)
  refine exists_pair_of_line (latW β₀ hM) ?_ q (p.pr (incA D μ)) (fun t => ?_) (fun s => ?_)
  · obtain ⟨Λ, h1, h2, -⟩ := exists_lat D k p S _ β₀ M hM
    have hlat : (latW β₀ hM).IsLattice k := by
      rwa [show latW β₀ hM = Λ from Submodule.ext fun x => (h2 x).symm]
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := exists_gen (p := p) hM
    rw [eq_top_iff]
    intro x _
    have hexp : x = ∑ l, c l (β₀.b *ᵥ x) • (β₀.b' *ᵥ fun a => p.pr (incA D (s l a))) := by
      have h := congrArg (β₀.b' *ᵥ ·) (hc (β₀.b *ᵥ x))
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul] at h
      rwa [Matrix.mulVec_mulVec, β₀.b'b, Matrix.one_mulVec] at h
    rw [hexp]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change (fun i => p.sec ((β₀.b *ᵥ (β₀.b' *ᵥ fun a => p.pr (incA D (s l a)))) i)) ∈ latV S M (· = p.v)
    rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    exact sec_inc_mem (hs l)
  · refine Iff.trans ?_ ((hline _ (sec_mem_idAt p t)).trans (mul_sec_mem_intAt_iff p _ t))
    have h2 : (fun i => p.sec ((β₀.b *ᵥ (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k)) i)) = p.sec t • ratV (vecB o ζ) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, sec_mul_right, hs]
      congr 1
      simp [mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
    rw [← h2]
    rfl
  · obtain ⟨s', rfl⟩ : ∃ s', s = p.pr (incA D (star μ)) * s' := ⟨_, (mul_inv_cancel_left₀ hb s).symm⟩
    refine Iff.trans ?_ ((hline _ (csec_mem_idAt (p := p) s')).trans (mul_cA_sec_mem_intAt_iff p _ s'))
    have h2 : cA D (p.sec s') • ratV (vecB o ζ) =
        fun i => cA D (p.sec (s' * p.pr (incA D (star (vecB o ζ i))))) := funext fun i => cA_sec_mul p _ s'
    rw [h2]
    refine Iff.trans ?_ (csec_mem_iff hM _).symm
    have h3 : ∀ x : n ⊕ Fin 1 → k, s' * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) ∈ 𝒪[k] ↔
        p.pr (incA D (star μ)) * s' * ((q.1 : k) * (p.pr (incA D μ) * x (Sum.inr 0))) ∈ 𝒪[k] := fun x => by
      rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hnorm, RingHom.map_neg, RingHom.map_neg, RingHom.map_mul,
        RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
      generalize p.pr (incA D (T : D.host.E)) = a at hT
      generalize p.pr (incA D μ) = b
      generalize p.pr (incA D (star μ)) = c
      have h4 : valuation k (s' * (-(b * c * a) * x (Sum.inr 0))) =
          valuation k (c * s' * ((q.1 : k) * (b * x (Sum.inr 0)))) := by
        simp only [Valuation.map_mul, Valuation.map_neg, hT]
        ac_rfl
      rw [h4]
    constructor
    · intro h x hx
      have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
      rw [hx'] at hx ⊢
      rw [pair_sumFrame o ζ hs, h3]
      exact h _ hx
    · intro h x hx
      rw [← h3, ← pair_sumFrame o ζ hs]
      exact h _ hx

end Place

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitStabConj

theorem eq_idempotent_mul_add_of_mul_sub_eq {R : Type*} [CommRing R] (ε m o : R) (h : ε * (m - o) = m - o) : m = ε * m + (1 - ε) * o := by
  linear_combination -h

theorem suppAt_conj {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (h : Formalism.L2.Theta.SuppAt e V g) (b : GA D V) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hmul : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    simp [Formalism.L2.Theta.mt, map_mul]
  have hAB : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hmul, inv_mul_cancel]; simp [Formalism.L2.Theta.mt]
  have hm : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hmul, hmul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  have hg : Formalism.L2.Theta.mt V g - 1 = (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) := by
    ext i j; exact (h i j).symm
  intro i j
  rw [hm]
  conv_rhs => rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  rfl

end GlobalTheory.SplitStabConj


set_option maxHeartbeats 1000000 in
open GlobalTheory.SplitStabConj in
theorem GlobalTheory.splitStab_conj_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → b⁻¹ * g * b ∈ GfC V ∧ (Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β ↔ gk ∈ KO k Y) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V (b⁻¹ * g * b)) = 1 := by
  intro D k _ _ _ _ q PP he V β Λ N hSD Y _ _ F σ b hM g gk hL
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N hSD
  obtain ⟨c, hfr, -⟩ := hSD
  have hsg : Formalism.L2.Theta.SuppAt q.e V g := hL.1
  have hsκ : Formalism.L2.Theta.SuppAt q.e V (b⁻¹ * g * b) := suppAt_conj hsg b
  refine ⟨?_, ?_, ?_⟩
  · have hg := GlobalTheory.SplitHecke.Stab.mem_GfC q.split hsg
    rw [GfC, MonoidHom.mem_ker] at hg ⊢
    rw [map_mul, map_mul, hg, mul_one, ← map_mul, inv_mul_cancel, map_one]
  · obtain ⟨hX, hXi⟩ := _root_.GlobalTheory.Lev.conj_frame_matrix q he V β F σ b hM g gk hL
    obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
    rw [GlobalTheory.LocGl.mem_KO_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hyX : Formalism.L2.DIV.intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β := by
        rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · obtain ⟨i, rfl⟩ := σ.surjective a
        obtain ⟨j, rfl⟩ := σ.surjective a'
        rw [← hX i j, q.prF_mem_iff he, ← hyX]
        exact mul_mem hint (y.val i j).2
      · obtain ⟨i, rfl⟩ := σ.surjective a
        obtain ⟨j, rfl⟩ := σ.surjective a'
        rw [← hXi i j, q.prF_mem_iff he, ← hyX, ← map_inv]
        exact mul_mem hint ((y⁻¹).val i j).2
    · rintro ⟨h1, h2⟩
      have hA : IsIntM (toEAf D q.e • (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).1) := fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, ← q.prF_mem_iff he, hX]; exact h1 _ _
      have hB : IsIntM (toEAf D q.e • ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, ← q.prF_mem_iff he, hXi]; exact h2 _ _
      obtain ⟨hC, hD⟩ := _root_.GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ β hsd hfr _ (GlobalTheory.LevSplit.finE_mem_UA V (b⁻¹ * g * b)) _ rfl q.e hA hB
      have hsum : IsIdemSum q.e {PP} := ⟨⟨fun _ => q.e, by simpa using he, by simp⟩, q.split.2.1⟩
      have hmt : Formalism.L2.Theta.mt V (b⁻¹ * g * b) = (q.e + cA D q.e) • Formalism.L2.Theta.mt V (b⁻¹ * g * b) +
          (1 - (q.e + cA D q.e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
        ext i j
        have := hsκ i j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
        exact eq_idempotent_mul_add_of_mul_sub_eq _ _ _ this
      have hy := _root_.GlobalTheory.FineCut.finE_cut V β (b⁻¹ * g * b) (b⁻¹ * g * b) (q.e + cA D q.e) hmt
      exact (_root_.GlobalTheory.FrameIdem.cut_mem_St_red V.rank β _ _ {PP} q.e hsum hA hB hC hD hy).1
  · intro PP' hne hS
    exact _root_.GlobalTheory.SplitOffRed.redFn_eq_one_off q he V β _ hsκ hS PP' hne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepLocalIteratedIntegralProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ValOneAt

theorem val_translate {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Θ₁ : WO S.B.V S.J.W → ℂ) (Θ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    S.val c₁ c₂ Θ₁ Θ₂ φ f g h₁ h₂ = S.val c₁ c₂ (S.s₁.om (g, h₁) Θ₁) (S.s₂.om (h₁, h₂) Θ₂) φ (rTrans h₂ f) 1 1 1 := by
  unfold Dbl2.val Dbl2.con
  have e3 : rTrans (1 : GA D S.B'.V) (rTrans h₂ f) = rTrans h₂ f := by funext x; simp [rTrans]
  rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
    map_one, map_one, e3]
  rfl

theorem sum_rTrans_trc {D : D7} {V : HSp D} {G : Type} [Monoid G] (gl : G →* GA D V) (h₂ : GA D V)
    (cm : ∀ b, gl b * h₂ = h₂ * gl b) (e : G →₀ ℂ) (f : GA D V → ℂ) :
    (e.sum fun b a => a • rTrans (gl b) (rTrans h₂ f)) = rTrans h₂ (trc (e.mapDomain gl) f) := by
  have e1 : trc (e.mapDomain gl) f = (e.mapDomain gl).sum fun b a => a • rTrans b f := rfl
  rw [e1, Finsupp.sum_mapDomain_index (h := fun b a => a • rTrans b f) (fun _ => zero_smul ℂ _)
    (fun _ _ _ => add_smul _ _ _)]
  funext w
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rTrans, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, cm b, ← mul_assoc]

theorem comb_lin {G A : Type} [AddCommGroup A] [Module ℂ A] [Monoid G] (τ : Representation ℂ G A) (l : A →ₗ[ℂ] ℂ)
    (e : G →₀ ℂ) (F : A) : GlobalTheory.PosOne.comb e (fun b => l (τ b F)) = l (e.sum fun b a => a • τ b F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.PosOne.comb, Finsupp.sum, map_sum, map_smul, smul_eq_mul]

theorem coe_sum_sub {G X : Type} [AddCommGroup X] [Module ℂ X] {A : Submodule ℂ X} (e : G →₀ ℂ) (v : G → A) :
    (((e.sum fun b a => a • v b : A)) : X) = e.sum fun b a => a • (v b : X) := by
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]


set_option maxHeartbeats 4000000 in
theorem valOne_all : ∀ D : D7, ValOne D := by
  intro D ψ hψ σ S Q G₁ G₂ hG₁ hG₂ hK₁ hK₂ c₁ c₂ hc₁ hc₂ f₁ f₂ hvac φ f hφ hf hTy g hg h₁ hh₁ h₂ hh₂
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hvac
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := _root_.GlobalTheory.hasConductor_one_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨-, -, -, cm₀, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B.V _ Q.F.G₀ Q.gl₀ Q.loc₀
  obtain ⟨-, -, -, cm₁, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.J.W _ Q.F.G₁ Q.gl₁ Q.loc₁
  obtain ⟨-, -, -, cm₂, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂
  have hT₁' := _root_.GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁ T₁ hT₁ g hg h₁ hh₁
  have hT₂' := _root_.GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂ T₂ hT₂ h₁ hh₁ h₂ hh₂
  have hf' : IsContAut S.B'.V (rTrans h₂ f) :=
    ⟨fun γ hγ x => by simp only [rTrans, mul_assoc]; exact hf.1 γ hγ _, hf.2.comp (continuous_mul_const h₂)⟩
  have hTy' : Q.Typed (rTrans h₂ f) := fun j => by
    funext x
    have := congrFun (hTy j) (x * h₂)
    simp only [rTrans, Pi.smul_apply] at this ⊢
    rw [mul_assoc, cm₂ j h₂ hh₂, ← mul_assoc, this]
  obtain ⟨A, τ, T, hsm, hτ, hmem, htri, hval, hlast⟩ :=
    _root_.GlobalTheory.TriStep.tri D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ _ _ hT₁' hT₂' φ hφ
  set F : A := ⟨rTrans h₂ f, hmem _ hf' hTy'⟩ with hFdef
  let Φa : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k → GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
    fun a x => ⟨om Q.μ₁ a x Q.Φ₁.1, _root_.GlobalTheory.SplitWeil.ValOne.om_val_mem_SB Q.k _ _ Q.μ₁ a x Q.Φ₁⟩
  let Φb : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →
      SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x y => ⟨om Q.μ₂ x y Q.Φ₂.1, _root_.GlobalTheory.SplitWeil.ValOne.om_val_mem_SB Q.k _ _ Q.μ₂ x y Q.Φ₂⟩
  obtain ⟨v, hv⟩ : ∃ v : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k → GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ, ∀ a x y,
      v a x y = S.val c₁ c₂ ((S.s₁.om (g, h₁) ∘ₗ T₁) (Φa a x)) ((S.s₂.om (h₁, h₂) ∘ₗ T₂) (Φb x y)) φ (τ y F).1 1 1 1 :=
    ⟨_, fun _ _ _ => rfl⟩
  have d1 : comb ψ _ _ Q.D₁ (T₁ O₁) = T₁ Q.Φ₁ := (Q.dat₁.2 T₁ hT₁ O₁ Q.Φ₁ hO₁ rfl).symm
  have d2 : comb ψ _ _ Q.D₂ (T₂ O₂) = T₂ Q.Φ₂ := (Q.dat₂.2 T₂ hT₂ O₂ Q.Φ₂ hO₂ rfl).symm
  have KEY : ∀ a x y, S.val c₁ c₂ (comb ψ _ _ Q.D₁ (T₁ O₁)) (comb ψ _ _ Q.D₂ (T₂ O₂)) φ f (g * Q.gl₀ a)
      (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) = v a x y := by
    intro a x y
    rw [hv, d1, d2, val_translate]
    have m1 : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (Q.gl₀ a, Q.gl₁ x) * S.s₁.om (g, h₁) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₀ a g hg, cm₁ x h₁ hh₁]
    have m2 : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (Q.gl₁ x, Q.gl₂ y) * S.s₂.om (h₁, h₂) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₁ x h₁ hh₁, cm₂ y h₂ hh₂]
    have r : rTrans (h₂ * Q.gl₂ y) f = (τ y F).1 := by
      rw [hτ]; funext z; simp only [rTrans, hFdef]; rw [mul_assoc z (Q.gl₂ y) h₂, cm₂ y h₂ hh₂]
    rw [m1, m2, r, Module.End.mul_apply, Module.End.mul_apply]
    exact _root_.GlobalTheory.QPl.LineCancel.val_om_loc D ψ hψ σ S Q _ _ hT₁' hT₂' c₁ c₂ φ _ a x y Q.Φ₁ (Φa a x) Q.Φ₂ (Φb x y) rfl rfl
  haveI i1 : Q.m₁.IsHaarMeasure := Q.haar₁
  haveI i2 : Q.m₂.IsHaarMeasure := Q.haar₂
  have t1 : Q.m₁.IsHaarMeasure := inferInstance
  have t2 := @_root_.GlobalTheory.PosOne.symDbl_existsUnique Q.k _ _ _ _ _ _ Q.n₀ Q.n₁ Q.n₂ _ _ _ _ _ _ (Q.c+1) (σ+1) hcQ Q.ψk hψc hψ1 Q.ν hsd Q.μ₁ Q.μ₂ Q.open₁ Q.open₂ Q.m₁ Q.haar₁
  haveI := hG₁
  haveI := hG₂
  have ex := fun a => @t2 G₁ hG₁ Q.m₂ Q.haar₂ G₂ hG₂ A _ _ τ hsm T htri F (Φa a 1) Q.Φ₂
  choose z hz _ using ex
  obtain ⟨u, hu1, hu2⟩ := _root_.GlobalTheory.PosOne.SymComb.symDbl_comb Q.k Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.ψk hψc hψ1 Q.ν hsd Q.μ₁ Q.μ₂ Q.m₁ G₁ Q.m₂ G₂
    Q.haar₁ hG₁ Q.haar₂ hG₂ A τ hsm T htri F Q.Φ₁ Q.Φ₂ Q.e₀ z v (fun a _ => hz a)
    (fun a _ x y => by rw [hv]; exact hval (Φa a x) (Φb x y) (τ y F))
  refine ⟨u, fun x => by simpa only [KEY] using hu1 x, ?_⟩

  classical
  let e₂' : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →₀ ℂ) :=
    fun β => if h : β ∈ Q.A₂ then Q.e₂ ⟨β, h⟩ else 0
  have he₂ : ∀ β ∈ Q.A₂, IsOneComb Q.ψk Q.ν (σ + 1) Q.L₂ β (e₂' β) := by
    intro β hβ; simp only [e₂', dif_pos hβ]; exact Q.one₂ ⟨β, hβ⟩
  have hFty : ∀ j : Q.L₂.J, τ (j : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) F = (Q.L₂.lam j : ℂ) • F := by
    intro j; apply Subtype.ext; rw [hτ, Submodule.coe_smul]; exact hTy' j
  have R := _root_.GlobalTheory.PosOne.comb_eq_sum_cells Q.k Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.ψk hψc Q.cond Q.ν Q.unitVol Q.μ₁ Q.μ₂ Q.open₁ Q.open₂
    Q.m₁ G₁ Q.m₂ G₂ Q.haar₁ hG₁ Q.haar₂ hG₂ hK₁ hK₂ Q.L₀ Q.L₁ Q.L₂ Q.co₁ Q.co₂ Q.le₁ Q.le₂ A τ hsm T htri F hFty
    Q.Φ₁ Q.Φ₂ Q.ty₁ Q.ty₂ Q.α Q.A₁ Q.A₂ Q.cov₁ Q.cov₂ Q.e₀ Q.one₀ e₂' he₂ z (fun a _ => hz a)
  have FIN : ∀ (γ : Q.A₁) (β : Q.A₂), comb (Q.e₂ β) (fun b => app (app T (xi Q.ψk Q.ν Q.μ₁ Q.Φ₁.1 Q.L₁.J 1 Q.α γ.1))
      (xi Q.ψk Q.ν Q.μ₂ Q.Φ₂.1 Q.L₂.J 1 γ.1 β.1) (τ b F)) =
      S.val (aconv [c₁, Q.d₁ γ]) (aconv [c₂, Q.d₂ γ β]) (T₁ O₁) (T₂ O₂) φ (trc ((Q.e₂ β).mapDomain Q.gl₂) f) g h₁ h₂ := by
    intro γ β
    have s1 := _root_.GlobalTheory.StepData.xi_mem_SB Q.k Q.n₁ Q.n₀ (Q.c + 1 + 1) Q.ψk hψc Q.ν Q.unitVol.1 Q.μ₁ Q.Φ₁ Q.L₁.J 1 Q.α γ.1
    have s2 := _root_.GlobalTheory.StepData.xi_mem_SB Q.k Q.n₂ Q.n₁ (Q.c + 1) Q.ψk hψc Q.ν Q.unitVol.1 Q.μ₂ Q.Φ₂ Q.L₂.J 1 γ.1 β.1
    rw [show xi Q.ψk Q.ν Q.μ₁ Q.Φ₁.1 Q.L₁.J 1 Q.α γ.1 = ((⟨_, s1⟩ : SB _) : _ → ℂ) from rfl, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe,
      show xi Q.ψk Q.ν Q.μ₂ Q.Φ₂.1 Q.L₂.J 1 γ.1 β.1 = ((⟨_, s2⟩ : SB _) : _ → ℂ) from rfl, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
    have hl := hlast ⟨_, s1⟩ ⟨_, s2⟩ (Q.d₁ γ) (Q.d₂ γ β) (Q.ent₁ γ) (Q.ent₂ γ β) O₁ O₂ hO₁ hO₂
      ((Q.e₂ β).sum fun b a => a • τ b F)
    have hsum : (((Q.e₂ β).sum fun b a => a • τ b F : A) : GA D S.B'.V → ℂ) =
        rTrans h₂ (trc ((Q.e₂ β).mapDomain Q.gl₂) f) := by
      rw [coe_sum_sub, ← sum_rTrans_trc Q.gl₂ h₂ (fun b => cm₂ b h₂ hh₂)]
      simp only [hτ, hFdef]
    rw [comb_lin τ (T ⟨_, s1⟩ ⟨_, s2⟩) (Q.e₂ β) F, hl, hsum,
      val_translate S _ _ (T₁ O₁) (T₂ O₂) φ _ g h₁ h₂, LinearMap.comp_apply, LinearMap.comp_apply]
  convert hu2 using 1
  rw [R]
  unfold QStep.volJ
  congr 1
  rw [← Finset.sum_coe_sort Q.A₁]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.sum_coe_sort Q.A₂]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [e₂', dif_pos β.2, Subtype.coe_eta]
  rw [← FIN γ β]
  simp only [QStep.w₁, QStep.w₂]
  push_cast
  ring

end GlobalTheory.ValOneAt
end
end

