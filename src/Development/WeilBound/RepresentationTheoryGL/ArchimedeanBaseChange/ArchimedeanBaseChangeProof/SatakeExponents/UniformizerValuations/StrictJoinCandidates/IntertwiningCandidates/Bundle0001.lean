module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinIso
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.AdmProd
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

theorem AdmProd_holds : AdmProd := by
  intro E _ _ _ n P w K hKo hKle
  have hadm := GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr (w.adicCompletion E) P.N P.h (fun i => P.σ i w)
  have hKc : IsCompact (K : Set (GLw n w)) :=
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n).of_isClosed_subset (K.isClosed_of_isOpen hKo) hKle
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.CandParts
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem allLeaves_iff (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves Q ↔ ∀ x ∈ t.leafList, Q x.1 x.2
  | _, .leaf V z => by simp [Tr.AllLeaves, Tr.leafList]
  | _, .node t₁ t₂ => by
    rw [Tr.AllLeaves, Tr.leafList, allLeaves_iff Q t₁, allLeaves_iff Q t₂]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h₁, h₂⟩ x (hx | hx)
      · exact h₁ x hx
      · exact h₂ x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

theorem parts_of_leaves {N : ℕ} (t : Tr E N) (P : Pre E N) (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop)
    (ht : TreeParts t P) (hl : t.AllLeaves fun M V => M = 0 ∨ Q M V) : ∀ j, Q (P.N j) (P.V j) := by
  intro j
  have hmem : (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ t.leafList.filter fun x => 0 < x.1 := by
    rw [← ht]
    exact List.mem_ofFn.2 ⟨j, rfl⟩
  rw [List.mem_filter] at hmem
  obtain ⟨hx, hpos⟩ := hmem
  have h := (allLeaves_iff _ t).1 hl _ hx
  rcases h with h0 | hQ
  · simp only [decide_eq_true_eq] at hpos
    exact absurd h0 (Nat.pos_iff_ne_zero.1 hpos)
  · exact hQ

end PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem CandParts_holds : CandParts := by
  intro hR E _ _ _ n π S F₀ d i s₁ s₂ Pa Pb D hC
  exact ⟨CandidateLeafDecomposition.parts_of_leaves s₁ Pa _ hC.ctx.t₁ hC.leaves₁,
    CandidateLeafDecomposition.parts_of_leaves s₂ Pb _ hC.ctx.t₂ hC.leaves₂⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinReps
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.He2

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem fin_reps {X : Type} {α : Type 1} [Finite X] (Q : X → α → Prop) :
    ∃ (k : ℕ) (Dl : Fin k → α), ∀ x D, Q x D → ∃ j, Q x (Dl j) := by
  obtain ⟨k, ⟨ε⟩⟩ := Finite.exists_equiv_fin {x // ∃ D, Q x D}
  refine ⟨k, fun j => (ε.symm j).2.choose, fun x D h => ⟨ε ⟨x, D, h⟩, ?_⟩⟩
  have := (ε.symm (ε ⟨x, D, h⟩)).2.choose_spec
  simp only [Equiv.symm_apply_apply] at this ⊢
  exact this


set_option maxHeartbeats 4000000 in
def ClauseB {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (Dl j) w)) ∧
        Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) = Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)) ∧
        FiniteDimensional ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))


set_option maxHeartbeats 4000000 in
theorem candB (hEq : StrictEqv) (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ClauseB F₀ d := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := fin_reps (X := Σ i : F₀.C.ι, Fin (kA i) × Fin (kB i)) (α := Pre E n) fun x D =>
    ∃ Pa Pb, IsJoin (F₀.μ ^ (n - F₀.C.a x.1)) (F₀.μ ^ F₀.C.a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨⟨ja, ha⟩, ⟨jb, hb⟩⟩ := hcls i s₁ s₂ Pa Pb D hc
  obtain ⟨j, Pa', Pb', hj, ha', hb'⟩ := hD ⟨i, ja, jb⟩ D ⟨Pa, Pb, hc.ctx.join, ha, hb⟩
  have hs : Strict D (Dl j) := hSJ E n _ _ _ _ Pa Pa' Pb Pb' D _ hc.ctx.join hj
    ((hEq E _ Pa _ Pa').2 ha ((hEq E _ Pa' _ Pa').1 ha')) ((hEq E _ Pb _ Pb').2 hb ((hEq E _ Pb' _ Pb').1 hb'))
  have hI := hII _ _ _ (prodAt D w) (prodAt (Dl j) w) (hSPr E n D (Dl j) hs w) (F₀.d₀.K' w)
  exact ⟨j, fun τ => hI.1 τ.V τ.ρ, hI.2.1, hAd E n (Dl j) w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1⟩

end PositivityTheory.Rg.BcB.F.FX.Bo.He2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinStrictHolds
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.FiniteStrictOrder

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (H : ∀ i, R (f i) (g (Fin.cast h i))) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  subst h
  induction c with
  | zero => simp
  | succ c ih =>
    simp only [List.ofFn_succ]
    exact List.Forall₂.cons (by simpa using H 0) (ih _ _ fun i => by simpa using H i.succ)

theorem siso_trans {x y z : Σ M : ℕ, Submodule ℂ (Sm E M)} (hy : _root_.GlobalTheory.CuspRep.IsStable y.2) (hx : SIso x z) (hyz : SIso y z) :
    SIso x y := by
  obtain ⟨M, Vx⟩ := x
  obtain ⟨M', Vy⟩ := y
  obtain ⟨Mz, Vz⟩ := z
  obtain ⟨h1, h1'⟩ := hx
  obtain ⟨h2, h2'⟩ := hyz
  simp only at h1 h2
  subst h1
  subst h2
  exact ⟨rfl, PositivityTheory.Rg.BcB.F.F5.Bo.isoV_trans' h1' (PositivityTheory.Rg.BcB.F.F5.Bo.isoV_symm' hy h2')⟩

theorem c_le {a : ℕ} (P : Pre E a) : P.c ≤ a := by
  calc P.c = ∑ _i : Fin P.c, 1 := by simp
    _ ≤ ∑ i, P.N i := Finset.sum_le_sum fun i _ => P.pos i
    _ = a := P.h

theorem N_le {a : ℕ} (P : Pre E a) (j : Fin P.c) : P.N j ≤ a := by
  calc P.N j ≤ ∑ i, P.N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = a := P.h

theorem m_le {a : ℕ} (P : Pre E a) (m₀ : (E →+* ℂ) → Multiset ℂ) (hm : ∀ τ, ∑ j, P.m j τ = m₀ τ) (j : Fin P.c)
    (τ : E →+* ℂ) : P.m j τ ≤ m₀ τ := by
  rw [← hm τ]
  exact Finset.single_le_sum (f := fun j => P.m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ j)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.FiniteStrictOrder

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo FiniteStrictOrder

theorem FinStrict_holds : FinStrict := by
  intro E _ _ _ a Θ Ω hΘ hΩ m₀

  have hF := fun (M : ℕ) (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ))
    (m' : (E →+* ℂ) → Multiset ℂ) (hK : IsOpen (K' : Set (GL (Fin M) (Af E)))) (hW : FiniteDimensional ℂ W') =>
    Bo.FinIso_holds E M K' W' m' hK hW
  choose V0 _hV0 hV0 using hF

  let Ms : Set ((E →+* ℂ) → Multiset ℂ) := Set.pi Set.univ fun τ => {s | s ≤ m₀ τ}
  have hMs : Ms.Finite := by
    refine Set.Finite.pi fun τ => ?_
    refine (Multiset.toFinset (Multiset.powerset (m₀ τ))).finite_toSet.subset fun s hs => ?_
    simpa [Multiset.mem_powerset] using hs

  let Reps : Set (Σ M : ℕ, Submodule ℂ (Sm E M)) :=
    ⋃ M ∈ Set.Iic a, ⋃ K' ∈ Θ M, ⋃ W' ∈ Ω M, ⋃ m' ∈ Ms,
      ⋃ (hK : IsOpen (K' : Set (GL (Fin M) (Af E)))), ⋃ (hW : FiniteDimensional ℂ W'),
        (Sigma.mk M) '' (V0 M K' W' m' hK hW : Set (Submodule ℂ (Sm E M)))
  have hReps : Reps.Finite :=
    (Set.finite_Iic a).biUnion fun M _ => (hΘ M).1.biUnion fun K' _ => (hΩ M).1.biUnion fun W' _ =>
      hMs.biUnion fun m' _ => Set.finite_iUnion fun hK => Set.finite_iUnion fun hW => (Finset.finite_toSet _).image _
  have := hReps.to_subtype
  have := hMs.to_subtype
  let Good : Pre E a → Prop := fun P =>
    (∀ j, ∃ K' ∈ Θ (P.N j), ∃ W' ∈ Ω (P.N j), HasType K' W' (P.V j)) ∧ (∀ τ, ∑ j, P.m j τ = m₀ τ)

  have hrep : ∀ P : Pre E a, Good P → ∀ j, ∃ z ∈ Reps, SIso ⟨P.N j, P.V j⟩ z := by
    intro P hP j
    obtain ⟨K', hK', W', hW', ht⟩ := hP.1 j
    have hKo := (hΘ _).2 K' hK'
    have hWf := (hΩ _).2 W' hW'
    obtain ⟨V', hV'm, hiso⟩ := hV0 _ K' W' (P.m j) hKo hWf (P.V j) (P.discrete j) ht (P.inf j)
    refine ⟨⟨P.N j, V'⟩, ?_, rfl, hiso⟩
    simp only [Reps, Set.mem_iUnion, Set.mem_image]
    exact ⟨P.N j, N_le P j, K', hK', W', hW', P.m j, fun τ _ => m_le P m₀ hP.2 j τ, hKo, hWf, V', hV'm, rfl⟩
  have hmem : ∀ P : Pre E a, Good P → ∀ j, P.m j ∈ Ms := fun P hP j τ _ => m_le P m₀ hP.2 j τ

  let part : Pre E a → ℕ → Option (Reps × Ms) := fun P i =>
    if h : i < P.c then
      (if h' : (∃ z ∈ Reps, SIso ⟨P.N ⟨i, h⟩, P.V ⟨i, h⟩⟩ z) ∧ P.m ⟨i, h⟩ ∈ Ms then
        some (⟨Classical.choose h'.1, (Classical.choose_spec h'.1).1⟩, ⟨P.m ⟨i, h⟩, h'.2⟩) else none)
    else none
  let key : Pre E a → Fin (a + 1) × (Fin a → Option (Reps × Ms)) := fun P =>
    (⟨min P.c a, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun i => part P i.1)

  have hkey : ∀ P Q : Pre E a, Good P → Good Q → key P = key Q → Strict P Q := by
    intro P Q hP hQ hPQ
    have hc : P.c = Q.c := by
      have := congrArg (fun x => (x.1 : ℕ)) (congrArg Prod.fst hPQ)
      simpa [key, min_eq_left (c_le P), min_eq_left (c_le Q)] using this
    have hpart : ∀ j : Fin P.c, part P j.1 = part Q j.1 := fun j =>
      congrFun (congrArg Prod.snd hPQ) ⟨j.1, lt_of_lt_of_le j.2 (c_le P)⟩
    have hsome : ∀ (R : Pre E a) (hR : Good R) (j : Fin R.c), ∃ z : Reps, SIso ⟨R.N j, R.V j⟩ z.1 ∧
        part R j.1 = some (z, ⟨R.m j, hmem R hR j⟩) := by
      intro R hR j
      have h' : (∃ z ∈ Reps, SIso ⟨R.N ⟨j.1, j.2⟩, R.V ⟨j.1, j.2⟩⟩ z) ∧ R.m ⟨j.1, j.2⟩ ∈ Ms := ⟨hrep R hR j, hmem R hR j⟩
      refine ⟨⟨Classical.choose h'.1, (Classical.choose_spec h'.1).1⟩, (Classical.choose_spec h'.1).2, ?_⟩
      simp only [part, dif_pos j.2, dif_pos h']
    refine ⟨forall₂_ofFn SIso hc _ _ fun j => ?_, hc, fun j => ?_⟩
    · obtain ⟨z, hz, hPz⟩ := hsome P hP j
      obtain ⟨z', hz', hQz⟩ := hsome Q hQ (Fin.cast hc j)
      have e := (hpart j).trans (hQz : part Q j.1 = _)
      rw [hPz] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1] at hz'
      exact siso_trans (Q.discrete _).stable hz hz'
    · obtain ⟨z, hz, hPz⟩ := hsome P hP j
      obtain ⟨z', hz', hQz⟩ := hsome Q hQ (Fin.cast hc j)
      have e := (hpart j).trans (hQz : part Q j.1 = _)
      rw [hPz] at e
      simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at e
      exact e.2

  let Im : Set (Fin (a + 1) × (Fin a → Option (Reps × Ms))) := key '' {P | Good P}
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin Im
  have hpre : ∀ i : Fin k, ∃ P, Good P ∧ key P = (e.symm i).1 := fun i => (e.symm i).2
  choose Pl hPl hkPl using hpre
  refine ⟨k, Pl, fun P h1 h2 => ?_⟩
  have hP : Good P := ⟨h1, h2⟩
  refine ⟨e ⟨key P, P, hP, rfl⟩, hkey P _ hP (hPl _) ?_⟩
  rw [hkPl, Equiv.symm_apply_apply]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.InfsEqOfStrict
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isoV_map_mulChi {N : ℕ} {V V' : Submodule ℂ (Sm E N)} (χ : HChar E) (h : IsoV V V') :
    IsoV (V.map (mulChi N χ).toLinearMap) (V'.map (mulChi N χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := h
  let S : V ≃ₗ[ℂ] V.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V
  let S' : V' ≃ₗ[ℂ] V'.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V'
  refine ⟨(S.symm.trans T).trans S', fun o φ ψ hψ => ?_⟩
  obtain ⟨φ, rfl⟩ := S.surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective ψ
  have h1 : ψ.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 + opAdd χ o • φ.1 := by
    apply (mulChi N χ).injective
    rw [← act_mulChi]
    exact hψ
  have hm : act o φ.1 ∈ V := by
    have h2 : ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 ∈ V := by
      have h3 := V.sub_mem ψ.2 (V.smul_mem (opAdd χ o) φ.2)
      rwa [h1, add_sub_cancel_right] at h3
    exact (Submodule.smul_mem_iff _ (Units.ne_zero _)).1 h2
  let φo : V := ⟨act o φ.1, hm⟩
  have hψ' : ψ = ((opMul χ o : ℂˣ) : ℂ) • φo + opAdd χ o • φ := Subtype.ext h1
  rw [hψ']
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add (f := _), map_smul]
  change ((opMul χ o : ℂˣ) : ℂ) • mulChi N χ (T φo).1 + opAdd χ o • mulChi N χ (T φ).1 = act o (mulChi N χ (T φ).1)
  rw [act_mulChi, ← hT o φ φo rfl, map_add (f := _), map_smul, map_smul]

theorem sIso_twPart (χ : HChar E) {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨M, V⟩ := x
  obtain ⟨M', V'⟩ := y
  obtain ⟨h1, h2⟩ := h
  cases h1
  exact ⟨rfl, isoV_map_mulChi χ h2⟩

def R (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ) : Prop :=
  HasInfCharGL x.2 τ m ∧ x.2 ≠ ⊥

def infs {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List (Multiset ℂ) := List.ofFn fun i => P.m i τ

theorem forall₂_R {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List.Forall₂ (R τ) (parts P) (infs P τ) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [parts, infs], fun i h₁ h₂ => ?_⟩
  have hi : i < P.c := by simpa [infs] using h₂
  have key : ∀ (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ), x = ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ →
      m = P.m ⟨i, hi⟩ τ → R τ x m := by
    rintro x m rfl rfl
    exact ⟨P.inf _ τ, (P.discrete _).ne_bot⟩
  exact key _ _ (by simp [parts]) (by simp [infs])

theorem R_twPart (χ : HChar E) {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {m : Multiset ℂ} (h : R τ x m) :
    R τ (twPart χ x) (m.map (· + expo χ τ)) := by
  obtain ⟨M, V⟩ := x
  refine ⟨GlobalTheory.BCT.TwistDisc.hasInfCharGL_map h.1 χ, fun h0 => h.2 ?_⟩
  exact (Submodule.map_eq_bot_iff (e := mulChi M χ)).1 h0

theorem eq_of_forall₂ {τ : E →+* ℂ} : ∀ {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l₁ l₂ : List (Multiset ℂ)},
    List.Forall₂ (R τ) l l₁ → List.Forall₂ (R τ) l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [LemDd.InfUniq_holds E _ _ τ _ _ h₁.2 h₁.1 h₂.1, eq_of_forall₂ t₁ t₂]

theorem infs_eq_of_strict {n : ℕ} {P P' : Pre E n} (h : Strict P P') (τ : E →+* ℂ) : infs P τ = infs P' τ := by
  obtain ⟨-, hc, hm⟩ := h
  unfold infs
  rw [List.ofFn_congr hc]
  congr 1
  funext i
  rw [hm]
  rfl

end PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  have hF : List.Forall₂ SIso (parts D) (parts D') := by
    rw [hJ, hJ']
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_twPart χ₂ h))
  have hc : D.c = D'.c := by
    have := hF.length_eq
    simpa [parts] using this
  refine ⟨hF, hc, fun i => ?_⟩
  funext τ
  have hI : ∀ {Q : Pre E a} {S : Pre E b} {Z : Pre E n}, IsJoin χ₁ χ₂ Q S Z →
      infs Z τ = (infs Q τ).map (fun m => m.map (· + expo χ₁ τ)) ++ (infs S τ).map (fun m => m.map (· + expo χ₂ τ)) := by
    intro Q S Z hZ
    refine eq_of_forall₂ (forall₂_R Z τ) ?_
    rw [hZ]
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R Q τ).imp fun _ _ h => R_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R S τ).imp fun _ _ h => R_twPart χ₂ h))
  have e : infs D τ = infs D' τ := by
    rw [hI hJ, hI hJ', infs_eq_of_strict ha, infs_eq_of_strict hb]
  unfold infs at e
  rw [List.ofFn_congr hc.symm (fun j => D'.m j τ)] at e
  have := congrFun (List.ofFn_injective e) i
  simpa using this

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictPre
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictPreorder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (hR : List.Forall₂ R (List.ofFn f) (List.ofFn g)) (i : Fin c) : R (f i) (g (Fin.cast h i)) := by
  subst h
  have := hR.get (i := i.1) (by simp) (by simp)
  simpa using this

theorem cls_eq (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hxy : SIso x y) (hy : IsDiscrete y.2)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (hσ : IsLocCompGL x.2 w σ) (hσ' : IsLocCompGL y.2 w σ') :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := hxy
  simp only at h
  subst h
  exact F5.Bo.LocUniq_holds E x1 y2 hy w σ σ' (F5.Bo.LocIso_holds E x1 x2 y2 hI w σ hσ) hσ'

end StrictPreorder

theorem StrictPre_holds : StrictPre := by
  intro E _ _ _ n P P' hS
  obtain ⟨hF, hc, hm⟩ := hS
  refine ⟨finCongr hc, fun i w => ?_, fun i τ => congrFun (hm i) τ⟩
  have hI : SIso ⟨P.N i, P.V i⟩ ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ :=
    StrictPreorder.forall₂_ofFn hc (fun j => (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)))
      (fun j => (⟨P'.N j, P'.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) hF i
  exact StrictPreorder.cls_eq _ _ hI (P'.discrete _) w (P.σ i w) (P'.σ _ w) (P.loc i w) (P'.loc _ w)

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

