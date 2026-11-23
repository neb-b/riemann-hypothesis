module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.Bundle0001
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ChoiceT
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.ShufStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.HkConstMul
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hk_const_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (c : ℂ) (e : GL ι F → ℂ) (v : V) :
    PositivityTheory.Rg.BcN.F2.hk ρ K (fun g => c * e g) v = c • PositivityTheory.Rg.BcN.F2.hk ρ K e v := by
  unfold PositivityTheory.Rg.BcN.F2.hk
  rw [smul_finsum]
  exact finsum_congr fun q => mul_smul _ _ _

theorem UpperTheory.HeckeLevelFrameExistence.locE :
    UpperTheory.HeckeLevelFrameExistence.LocE := by
  intro E _ _ _ n w hw K' hKo hKle hlev σ hσ k D
  have hUL : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hmap : (K'.subgroupOf (UL n w)).map (UL n w).subtype = K' := by
    rw [Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]
  have hKc : IsCompact (K' : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K' hKo) hKle
  obtain ⟨P, T, hT, hcomp, hdict⟩ := GlobalTheory.CompanionTheory.SplitPlace.splitDict E n w hw σ
  have hd := hdict (K'.subgroupOf (UL n w)) hlev
  rw [hmap] at hd
  obtain ⟨y₀, hy₀, hy₀0⟩ := (Submodule.ne_bot_iff _).1 hσ
  have hz : PositivityTheory.Rg.BcN.F2.IsHk K' (0 : GLw n w → ℂ) :=
    ⟨hKo, hKc, HasCompactSupport.zero, fun _ _ _ _ _ => rfl⟩
  have hP0 : ∃ v ∈ fixed P.ρ K', v ≠ 0 :=
    ⟨T y₀, ((hd 0 hz).2 y₀ hy₀).1, fun h => hy₀0 (T.map_eq_zero_iff.1 h)⟩
  have hchoice : PositivityTheory.Rg.BcB.F.Choice.ChoiceS :=
    PositivityTheory.Rg.BcB.F.Choice.choiceS_of
      (fun E _ _ _ n w => _root_.GlobalTheory.CompanionTheory.Isolate.isolateAt (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => _root_.GlobalTheory.CompanionTheory.RepFinSubq.finSubq (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => _root_.GlobalTheory.CompanionTheory.ProdLen.prodFinLen (w.adicCompletion E) (Fin n))
  obtain ⟨e₀, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, hkill⟩ :=
    hchoice E n w K' hKo hKc P hP0 k D
  set r : ℂ := (((K'.subgroupOf (UL n w)).relIndex (KL n w) : ℕ) : ℂ) with hr
  have hIk' : PositivityTheory.Rg.BcN.F2.IsHk K' (fun g => r * e₀ g) :=
    ⟨hIk.1, hIk.2.1, hIk.2.2.1.mul_left, fun k₁ h₁ k₂ h₂ g => by
      simp only [hIk.2.2.2 k₁ h₁ k₂ h₂ g]⟩
  have hH := (hd _ hIk').1
  refine ⟨fun g => r * e₀ g, P, hIk', hH, hcomp, ?_, ?_⟩
  · have hy : T.symm v₀ ∈ fixed σ.ρ (K'.subgroupOf (UL n w)) := by
      rintro ⟨x, hx⟩
      apply T.injective
      have h1 := hv₀ ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩
      rw [map_smul, hT, T.apply_symm_apply]
      simpa using h1
    refine ⟨⟨T.symm v₀, hy⟩, fun h => ?_, ?_⟩
    · have h0 : T.symm v₀ = 0 := congrArg Subtype.val h
      have h1 : v₀ = 0 := T.symm.map_eq_zero_iff.1 h0
      rw [h1, map_zero] at hl1
      exact zero_ne_one hl1
    · apply Subtype.ext
      rw [(GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ _ hlev _ _ hH hH).2.1]
      apply T.injective
      have h2 := ((hd e₀ hIk).2 _ hy).2
      rw [T.apply_symm_apply, hl v₀ hv₀, hl1, one_smul] at h2
      rw [h2, T.apply_symm_apply]
  · intro j τ hs hne v hv
    rw [hk_const_mul, hkill j τ hs hne v hv, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MapSplit
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_ex (hE : ShufEx) (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) :
    ∃ e : Fin a ⊕ Fin (n - a) ≃ Fin n,
      (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j := by
  obtain ⟨hdisj, hcov⟩ := hE n a s h
  let f : Fin a ⊕ Fin (n - a) → Fin n :=
    Sum.elim ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2)
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        exact congrArg Sum.inl (((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1).injective hij)
      · exfalso
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 i)
          (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 j)
      · exfalso
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact Finset.disjoint_left.1 hdisj (Finset.orderEmbOfFin_mem _ h.2.1 j)
          (hij ▸ Finset.orderEmbOfFin_mem _ h.2.2 i)
      · simp only [f, Sum.elim_inr] at hij
        exact congrArg Sum.inr (((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2).injective hij)
    · intro k
      have hk : k ∈ symIdx n (a % 2 = 1) s ∪ symIdx n ((n - a) % 2 = 1) sᶜ := hcov ▸ Finset.mem_univ k
      rcases Finset.mem_union.1 hk with hk | hk
      · have hr : k ∈ Set.range ((symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1) := by
          rw [Finset.range_orderEmbOfFin]
          exact hk
        obtain ⟨i, hi⟩ := hr
        exact ⟨.inl i, hi⟩
      · have hr : k ∈ Set.range ((symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2) := by
          rw [Finset.range_orderEmbOfFin]
          exact hk
        obtain ⟨j, hj⟩ := hr
        exact ⟨.inr j, hj⟩
  exact ⟨Equiv.ofBijective f hf, fun i => rfl, fun j => rfl⟩

private theorem map_split {α β : Type} [Fintype α] [Fintype β] {n : ℕ} (e : α ⊕ β ≃ Fin n) (f : Fin n → ℂˣ) :
    Finset.univ.val.map (fun i => f (e (.inl i))) + Finset.univ.val.map (fun j => f (e (.inr j))) =
      Finset.univ.val.map f := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map, ← Finset.univ_disjSum_univ]
  simp [Finset.disjSum, Multiset.disjSum, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def]

private theorem finish (hT : TargetAlg) (hM : MonoRes) {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E)
    (n a : ℕ) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) (e : Fin a ⊕ Fin (n - a) ≃ Fin n)
    (he : (∀ i, e (.inl i) = (symIdx n (a % 2 = 1) s).orderEmbOfFin h.2.1 i) ∧
      ∀ j, e (.inr j) = (symIdx n ((n - a) % 2 = 1) sᶜ).orderEmbOfFin h.2.2 j)
    (ξ : Fin n → ℂˣ) (ξa : Fin a → ℂˣ) (ξb : Fin (n - a) → ℂˣ) (hmono : PositivityTheory.Rg.BcB.N3.Mono ξ)
    (hstd : IsStd w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a))
      (fun k => Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k)))
    (hchi : chiOf w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) ξa ξb = chiN w ξ) :
    PositivityTheory.Rg.BcB.N3.Mono ξa ∧ PositivityTheory.Rg.BcB.N3.Mono ξb ∧
      (Finset.univ.val.map ξa).map (· * (-1 : ℂˣ) ^ (n - a)) + (Finset.univ.val.map ξb).map (· * (-1 : ℂˣ) ^ a) =
        Finset.univ.val.map ξ := by
  obtain ⟨hA, hB⟩ := hT E n w (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ ξa ξb hstd hchi
  have hnorm : ∀ k : Fin n,
      ‖((Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    cases e.symm k <;> simp
  obtain ⟨mA, mB⟩ := hM n (shufOf w n a s h e he ((-1) ^ (n - a)) ((-1) ^ a)) _ ξ hmono hnorm
  have e1 : ξa = fun i => _ := funext hA
  have e2 : ξb = fun j => _ := funext hB
  refine ⟨by rw [e1]; exact mA, by rw [e2]; exact mB, ?_⟩
  rw [Multiset.map_map, Multiset.map_map, ← map_split e ξ]
  congr 1
  · congr 1
    funext i
    rw [Function.comp_apply, hA i]
    show ξ (e (.inl i)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inl i))))⁻¹ *
      (-1) ^ (n - a) = ξ (e (.inl i))
    rw [Equiv.symm_apply_apply, Sum.elim_inl, inv_mul_cancel_right]
  · congr 1
    funext j
    rw [Function.comp_apply, hB j]
    show ξ (e (.inr j)) * (Sum.elim (fun _ => ((-1) ^ (n - a) : ℂˣ)) (fun _ => (-1) ^ a) (e.symm (e (.inr j))))⁻¹ *
      (-1) ^ a = ξ (e (.inr j))
    rw [Equiv.symm_apply_apply, Sum.elim_inr, inv_mul_cancel_right]

theorem UpperTheory.HeckeLevelFrameExistence.locC :
    PositivityTheory.Rg.BcB.F.Choice.ShufEx → PositivityTheory.Rg.BcB.F.Choice.VResStd → PositivityTheory.Rg.BcB.F.Choice.ShufStd → PositivityTheory.Rg.BcB.F.Tail.TargetAlg → PositivityTheory.Rg.BcB.F.Tail.MonoRes → UpperTheory.HeckeLevelFrameExistence.LocC := by
  intro hE hV hS hT hM E _ _ _ n w ι _ a Z ξ ha hZ hmono
  let J := Σ i : ι, {s : Finset (Fin (n / 2)) // LocData.admitted n (a i) s}
  let ee : (j : J) → Fin (a j.1) ⊕ Fin (n - a j.1) ≃ Fin n :=
    fun j => Classical.choose (exists_ex hE n (a j.1) j.2.1 j.2.2)
  have hee := fun j : J => Classical.choose_spec (exists_ex hE n (a j.1) j.2.1 j.2.2)
  let S : J → Shuf n := fun j =>
    shufOf w n (a j.1) j.2.1 j.2.2 (ee j) (hee j) ((-1) ^ (n - a j.1)) ((-1) ^ a j.1)
  let Z' : (j : J) → Set ((Fin (S j).a → ℂˣ) × (Fin (S j).b → ℂˣ)) := fun j => Z j.1
  obtain ⟨c, hc1, hc2, hc3⟩ := choiceT E n w J S Z' (chiN w ξ) (fun j => hZ j.1)
  refine ⟨c, hc1, hc2, ?_⟩
  intro i s h ξa ξb hmem hne
  let j : J := ⟨i, s, h⟩
  have hchi : chiOf w (S j) ξa ξb = chiN w ξ := by
    refine hc3 j (ξa, ξb) hmem ?_
    convert hne using 1
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun x hx => ?_)
    obtain ⟨h1, h2, h3⟩ := hV E w n (a i) s h (ee j) (hee j) x (hc1 hx)
    dsimp only
    rw [h1, h2, h3]
    rfl
  exact finish hT hM w n (a i) s h (ee j) (hee j) ξ ξa ξb hmono (hS E w n (a i) s h (ee j) (hee j)) hchi
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MuVal
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.HeckeLevelFrameExistence.muVal :
    UpperTheory.HeckeLevelFrameExistence.MuVal := by
  intro E _ _ _ μ e hμ w hw k
  have h1 : μ.val w = -1 := by
    show μ.loc w (GlobalTheory.Mem.Chr.atFin w (GlobalTheory.Mem.Chr.unif w)) = -1
    rw [hμ.2.2.1 w hw, GlobalTheory.SmGL.unrChar_apply,
      GlobalTheory.SmGL.ord_eq_one (GlobalTheory.MuInert.valuation_eq_uniformizer w (GlobalTheory.Mem.Chr.unif_spec w)), zpow_one]
  induction k with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih, h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEig
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.HeckeLevelFrameExistence.powEig :
    UpperTheory.HeckeLevelFrameExistence.PowEig := by
  intro E _ _ _ n w σ K' hlev g hg y hy m
  have key : ∀ k : ℕ, IsHecke K' (U.lpow K' g k) ∧ locOp σ K' (U.lpow K' g k) y = y := by
    intro k
    induction k with
    | zero =>
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g g hg hg
      refine ⟨h1, ?_⟩
      show locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) y = y
      rw [h2]
      rfl
    | succ k ih =>
      obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g _ hg ih.1
      refine ⟨h3, ?_⟩
      show locOp σ K' (lconv g (U.lpow K' g k)) y = y
      rw [h5, Module.End.mul_apply, ih.2, hy]
  exact (key m).2
end

