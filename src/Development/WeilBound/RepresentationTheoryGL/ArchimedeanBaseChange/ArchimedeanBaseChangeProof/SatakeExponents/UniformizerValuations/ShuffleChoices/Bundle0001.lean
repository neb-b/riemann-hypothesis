module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ChoiceTOf
section
noncomputable section

open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail

namespace PositivityTheory.Rg.BcB.F.Choice

theorem choiceTOf : ChoiceTOf := by
  intro hP hC _hG E _ _ _ n w ι _ s Z α hZ
  have hfin : (⋃ i, (fun p : (Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ) => chiOf w (s i) p.1 p.2) '' Z i).Finite :=
    Set.finite_iUnion (fun i => (hZ i).image _)
  obtain ⟨c, hc, h1, h0⟩ := hP n 2 α (hfin.toFinset.erase α) (by simp)
  refine ⟨c, hc, h1, ?_⟩
  intro i p hp hne
  by_contra hneq
  apply hne
  have key : (c.sum fun x a => a * ↑(∏ k : Fin n, (s i).eps k ^ x k) * ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x))
      = evalGL c (chiOf w (s i) p.1 p.2) := by
    unfold evalGL
    refine Finsupp.sum_congr (fun x _ => ?_)
    rw [mul_assoc, hC E n w (s i) p.1 p.2 x]
  rw [key]
  apply h0
  simp only [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_image]
  exact ⟨hneq, i, p, hp, rfl⟩

end PositivityTheory.Rg.BcB.F.Choice

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.FixedEquiv
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hk_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W} (φ : ρ.Equiv σ)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (v : V) :
    φ.toLinearEquiv (hk ρ K e v) = hk σ K e (φ.toLinearEquiv v) := by
  unfold hk
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)).trans
    (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (e q.out • ρ q.out v) = e q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

theorem fixed_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W} (φ : ρ.Equiv σ)
    (K : Subgroup (GL ι F)) (v : V) (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : GL ι F) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

end SlopeTestRemainingChoices

theorem choiceS_of
    (hI : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.IsolateAt (w.adicCompletion E) (Fin n))
    (hF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.FinSubq (w.adicCompletion E) (Fin n))
    (hP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.ProdFinLen (w.adicCompletion E) (Fin n)) : ChoiceS := by
  intro E _ _ _ n w K' hKo hKc P hP0 k D
  have hs : ∀ j, IsSmooth (prodAt (D j) w) := fun j => GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : ∀ j, GlobalTheory.SmGL.HasFiniteLength (prodAt (D j) w) := fun j =>
    hP E n w (Fin (D j).c) (fun i => Fin ((D j).N i)) (GlobalTheory.SmGL.stdBlocks (D j).N (D j).h)
      (fun i => ((D j).σ i w).V) (fun i => ((D j).σ i w).ρ) (fun i => ((D j).σ i w).smooth)
      (fun i => ((D j).σ i w).irred)
  choose J hJ W hW1 hW2 τ hτ hcov using fun j => hF E n w _ (prodAt (D j) w) (hs j) (hfl j)
  let _ : ∀ j, Fintype (J j) := hJ
  let _ : ∀ j i, AddCommGroup (W j i) := hW1
  let _ : ∀ j i, Module ℂ (W j i) := hW2
  let I : Type := Σ j : Fin k, {i : J j // IsEmpty ((τ j i).Equiv P.ρ)}
  obtain ⟨e, hIk, v₀, hv₀, l, hl1, hl, hkill⟩ :=
    hI E n w K' hKo hKc P.V P.ρ P.smooth P.irred hP0 I (fun x => W x.1 x.2.1) (fun x => τ x.1 x.2.1)
      (fun x => (hτ x.1 x.2.1).1) (fun x => (hτ x.1 x.2.1).2.1) (fun x => x.2.2)
  refine ⟨e, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, ?_⟩
  intro j τ' hsub hne v hv
  obtain ⟨i, ⟨φ⟩⟩ := hcov j τ'.V τ'.ρ τ'.irred hsub
  have hi : IsEmpty ((τ j i).Equiv P.ρ) := ⟨fun ψ => hne.false (φ.trans ψ)⟩
  apply φ.toLinearEquiv.injective
  rw [hk_equiv, map_zero]
  exact hkill ⟨j, i, hi⟩ _ (fixed_equiv φ K' v hv)

end PositivityTheory.Rg.BcB.F.Choice

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.UnitPowerEqResiduePower
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

theorem qh_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  have hq : qV E w ≠ 0 := by
    unfold qV
    exact (Ideal.absNorm_eq_zero_iff).not.2 w.ne_bot
  have hpos : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hpos)

theorem unit_power_eq_residue_power {E : Type} [Field E] [NumberField E] (w : Pl E) (k : ℤ) :
    qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k := by
  unfold qU
  rw [dite_eq_left (qh_ne_zero' w)]

theorem zpow_finsum' {ι : Type} (u : ℂˣ) (s : Finset ι) (f : ι → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, _root_.zpow_add, ih]

theorem dl_mul_pw {E : Type} [Field E] [NumberField E] (w : Pl E) {m : ℕ} (ξ : Fin m → ℂˣ) (y : Fin m → ℤ) :
    dl w y * pw ξ y = ((∏ i, (ξ i * qU w ((m : ℤ) - 1 - 2 * (i : ℕ))) ^ y i : ℂˣ) : ℂ) := by
  have hU : ∀ k, qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k := unit_power_eq_residue_power w
  have hdl : dl w y = ((Units.mk0 (qh w) (qh_ne_zero' w) ^
      (∑ i : Fin m, ((m : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * y i) : ℂˣ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hpw : pw ξ y = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) := by
    unfold pw
    rw [Units.coe_prod]
  rw [hdl, hpw, ← Units.val_mul]
  congr 1
  simp only [hU, mul_zpow, Finset.prod_mul_distrib, ← _root_.zpow_mul]
  rw [← zpow_finsum', mul_comm]

theorem chiEval : ChiEval := by
  intro E _ _ _ n w s ξa ξb x
  unfold ev2
  rw [dl_mul_pw, dl_mul_pw, ← Units.val_mul, ← Units.val_mul]
  congr 1
  unfold chiOf
  simp only [mul_zpow, Finset.prod_mul_distrib]
  congr 1
  have h := Equiv.prod_comp s.e (fun k => (Sum.elim (fun i : Fin s.a => ξa i * qU w ((s.a : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)))
    (fun j : Fin s.b => ξb j * qU w ((s.b : ℤ) - 1 - 2 * ((j : ℕ) : ℤ))) (s.e.symm k)) ^ x k)
  rw [← h, Fintype.prod_sum_type]
  simp [resL, resR]
  simp only [mul_zpow, Finset.prod_mul_distrib]

theorem gapRes : GapRes := by
  intro n s x hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  refine ⟨?_, ?_⟩
  · unfold Gap
    intro i j hij
    have := hx' _ _ (s.monoL hij)
    dsimp only at this
    simp only [resL]
    omega
  · unfold Gap
    intro i j hij
    have := hx' _ _ (s.monoR hij)
    dsimp only at this
    simp only [resR]
    omega

end PositivityTheory.Rg.BcB.F.Choice

end
end

