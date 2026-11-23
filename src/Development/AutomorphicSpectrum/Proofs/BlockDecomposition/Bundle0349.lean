module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CosocleContra

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isIrreducible_quot_of_isCoatom {L : Subrepresentation π} (hL : IsCoatom L) :
    (ProjLine.quot L).IsIrreducible := by
  have h1 : L.toSubmodule ≠ ⊤ := fun e => hL.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (ProjLine.quot L)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π :=
    ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hLT : L ≤ T' := fun v hv => by
    have h0 : L.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
    show L.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [h0]
    exact zero_mem _
  rcases eq_or_lt_of_le hLT with e | e
  · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := hy
    rw [← e] at hv
    exact (Submodule.Quotient.mk_eq_zero _).2 hv
  · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := (hL.2 _ e) ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    exact hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullContra (S : Subrepresentation π) : (contra (ProjLine.quot S)).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show (ProjLine.quot S).dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v =>
          LinearMap.congr_fun (show (ProjLine.quot S).dual g l.1 = l.1 from hg) (S.toSubmodule.mkQ v))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem pullContra_injective (S : Subrepresentation π) : Function.Injective (pullContra S) := fun a b h =>
  Subtype.ext (LinearMap.ext fun y => by
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem pullContra_apply_eq_zero (S : Subrepresentation π) (l : smoothPart (ProjLine.quot S).dual) {v : V}
    (hv : v ∈ S) : (pullContra S l).1 v = 0 := by
  have h0 : S.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
  show l.1 (S.toSubmodule.mkQ v) = 0
  rw [h0, map_zero]

theorem eq_of_isCoatom_of_mem_range {S S' : Subrepresentation π} (hS : IsCoatom S) (hS' : IsCoatom S')
    {w : smoothPart π.dual} (hw : w ≠ 0) (h : w ∈ (pullContra S).range) (h' : w ∈ (pullContra S').range) :
    S = S' := by
  by_contra hne
  have top := hS.sup_eq_top_of_ne hS' hne
  obtain ⟨l, rfl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  refine hw (Subtype.ext (LinearMap.ext fun v => ?_))
  have hv : v ∈ (S ⊔ S').toSubmodule := by
    rw [top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have h1 := pullContra_apply_eq_zero S l ha
  have h2 := pullContra_apply_eq_zero S' l' hb
  have h3 : (pullContra S l).1 b = 0 := (congrArg (fun y : smoothPart π.dual => y.1 b) hl').symm.trans h2
  show (pullContra S l).1 (a + b) = 0
  rw [map_add (f := _), h1, h3, add_zero]

end General

theorem isCosocle_of_isSocle_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  intro k _ _ _ _ hA N V _ _ π hπ hfl τ' hτ
  obtain ⟨hi, f, hf, hat⟩ := hτ
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis (k := k) N
  have hat0 : IsAtom f.range := isAtom_range hi f hf
  have hsm : ∀ S : Subrepresentation π, IsSmooth (ProjLine.quot S) := fun S =>
    (IsSubquotient.of_surjective (ProjLine.quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, IsCoatom S → (pullContra S).range = f.range := fun S hS => by
    have hirr := isIrreducible_quot_of_isCoatom hS
    exact hat _ (isAtom_range (GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (hsm S) hirr) hirr) _
      (pullContra_injective S))
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    refine hat0.1 (eq_bot_iff.2 ?_)
    rintro _ ⟨x, rfl⟩
    exact (h x).symm ▸ zero_mem (⊥ : Subrepresentation (contra π)).toSubmodule
  haveI : WellFoundedGT (Subrepresentation π) := ((hasFiniteLength_iff_wellFounded π).1 hfl).1
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := fun e => hx (Subtype.ext (LinearMap.ext fun v => by
    have hv : v ∈ (⊥ : Subrepresentation π) := e ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
    rw [hv0, map_zero]
    rfl))
  obtain ⟨L, hL, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation π)).resolve_left hbt
  have huniq : ∀ S : Subrepresentation π, IsCoatom S → S = L := fun S hS =>
    eq_of_isCoatom_of_mem_range hS hL hx ((key S hS).symm ▸ ⟨x, rfl⟩) ((key L hL).symm ▸ ⟨x, rfl⟩)
  have hall : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤ := fun S => by
    rcases eq_top_or_exists_le_coatom S with h | ⟨M, hM, hSM⟩
    · exact Or.inr h
    · exact Or.inl (huniq M hM ▸ hSM)
  have hc := ProjLine.isCosocle_quot hL.1 hall
  exact ⟨⟨_, ProjLine.quot L, hsm L, hc.1⟩, hc⟩

end GlobalTheory.CompanionTheory.CosocleContra

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTop
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

section Groups

variable {k : Type} [Field k]

theorem blk_stdBlocks_two {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (i : Fin N) :
    blk (stdBlocks ![n, N - n] h) i = if (i : ℕ) < n then 0 else 1 := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks ![n, N - n] h).surjective i
  rw [blk_apply]
  have := stdBlocks_val ![n, N - n] h c i'
  fin_cases c
  · have hi := i'.2
    simp at this hi ⊢
    omega
  · have hi := i'.2
    simp at this hi ⊢
    omega

theorem mem_unipRad_two_iff {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks ![n, N - n] h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_stdBlocks_two, blk_stdBlocks_two]
  have : ((if (i : ℕ) < n then (0 : Fin 2) else 1) < if (j : ℕ) < n then 0 else 1) ↔
      ((i : ℕ) < n ∧ n ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;> simp [hi, hj] <;> omega
  rw [this]

theorem unipRad_two_le_derUnip {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) :
    unipRad k (stdBlocks ![n, N - n] h) ≤ derUnip k N n := by
  intro g hg
  have hE := (mem_unipRad_two_iff h).1 hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · intro i hi
    ext r
    have hc : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hc, hE r i (by omega)]
    by_cases hri : r = i
    · subst hri; simp
    · rw [one_apply_ne hri, Pi.single_apply, if_neg hri]

theorem unipRad_two_ne_bot {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (h1 : 1 ≤ n) (h2 : n < N) :
    unipRad k (stdBlocks ![n, N - n] h) ≠ ⊥ := by
  set i : Fin N := ⟨0, by omega⟩
  set j : Fin N := ⟨n, h2⟩
  have hne : i ≠ j := by
    intro e
    have := congrArg Fin.val e
    simp [i, j] at this
    omega
  let t : GL (Fin N) k := ⟨transvection i j 1, transvection i j (-1),
    by rw [transvection_mul_transvection_same i j hne]; simp,
    by rw [transvection_mul_transvection_same i j hne]; simp⟩
  have ht : t ∈ unipRad k (stdBlocks ![n, N - n] h) := by
    refine (mem_unipRad_two_iff h).2 fun r s hrs => ?_
    show transvection i j (1 : k) r s = _
    have : ¬ (r = i ∧ s = j) := by
      rintro ⟨rfl, rfl⟩
      exact hrs ⟨by simp [i]; omega, le_refl _⟩
    simp only [transvection, Matrix.add_apply]
    rw [Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact this ⟨rfl, rfl⟩
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ht
  simp [t, transvection, one_apply_ne hne] at this

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derChar_eq_one_of_mem_unipRad_two {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    (u : derUnip k N n) (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks ![n, N - n] h)) :
    derChar k ψ N n u = 1 := by
  have hE := (mem_unipRad_two_iff h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem twKer_unipRad_two_le {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 ≤ twKer π (derUnip k N n) (derChar k ψ N n) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_two_le_derUnip h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad_two ψ h _ u.2]
  simp

end Chars

theorem twKer_derUnip_eq_top_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  intro k _ _ _ _ ψ N n V _ _ π hπ h1 h2
  have h : ∑ c, ![n, N - n] c = N := by
    simp [Fin.sum_univ_two]
    omega
  have hs := hπ.2 2 ![n, N - n] (stdBlocks ![n, N - n] h) (unipRad_two_ne_bot h h1 h2)
  have htop : twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hs
  exact eq_top_iff.2 (htop ▸ twKer_unipRad_two_le ψ h π)

end GlobalTheory.CompanionTheory.BZMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCoweightAntitonePairingSum
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamGap

theorem sum_lt_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if (i : ℕ) < m then 1 else 0) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.card_range, Nat.cast_id]

theorem sum_ge_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if m ≤ (i : ℕ) then 1 else 0) = N - m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if m ≤ i then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => m ≤ i) = Finset.Ico m N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, Nat.cast_id]

theorem lamOf_sub {N : ℕ} (g : Fin (N - 1) → ℕ) (i i' : Fin N) (h : i < i') :
    (Zls.lamOf g i - Zls.lamOf g i').toNat
      = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
  have hii : (i : ℕ) < (i' : ℕ) := h
  have key : Zls.lamOf g i - Zls.lamOf g i'
      = ((∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 : ℕ) : ℤ) := by
    simp only [Zls.lamOf]
    rw [← Finset.sum_sub_distrib, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp_all <;> omega
  rw [key, Int.toNat_natCast]

theorem gap_count (N : ℕ) (c j : ℕ) (hj : j + 1 ≤ N) :
    (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = c * ((j + 1) * (N - (j + 1))) := by
  calc (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = ∑ i : Fin N, ∑ i' : Fin N,
          c * ((if (i : ℕ) < j + 1 then 1 else 0) * (if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        have a1 : ((i : ℕ) < j + 1) ↔ (i : ℕ) ≤ j := by omega
        have a2 : (j + 1 ≤ (i' : ℕ)) ↔ j < (i' : ℕ) := by omega
        simp only [a1, a2]
        split_ifs <;> simp_all
    _ = c * ((∑ i : Fin N, if (i : ℕ) < j + 1 then 1 else 0) *
          (∑ i' : Fin N, if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = c * ((j + 1) * (N - (j + 1))) := by
        rw [sum_lt_indicator N (j + 1) hj, sum_ge_indicator N (j + 1) hj]

theorem lamOf_antitone_gap_sum (N : ℕ) (g : Fin (N - 1) → ℕ) :
    Antitone (Zls.lamOf g) ∧
      (∑ i : Fin N, ∑ i' : Fin N,
          if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [Zls.lamOf]
    refine Finset.sum_le_sum fun j _ => ?_
    have hab' : (a : ℕ) ≤ (b : ℕ) := hab
    split_ifs <;> omega
  · have step : ∀ i i' : Fin N,
        (if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
          = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
      intro i i'
      split_ifs with hlt
      · exact lamOf_sub g i i' hlt
      · symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have hn : ¬ ((i : ℕ) < (i' : ℕ)) := hlt
        rw [if_neg]
        rintro ⟨h1, h2⟩
        omega
    calc (∑ i : Fin N, ∑ i' : Fin N,
            if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ i : Fin N, ∑ i' : Fin N, ∑ j : Fin (N - 1),
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => step i i'
      _ = ∑ i : Fin N, ∑ j : Fin (N - 1), ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j : Fin (N - 1), ∑ i : Fin N, ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_comm
      _ = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact gap_count N (g j) j (by have := j.isLt; omega)

end GlobalTheory.CompanionTheory.LamGap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.DualCusp

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem isSupercuspidal_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (hs : IsSupercuspidal π) :
    IsSupercuspidal (contra π) := by
  refine ⟨isSmooth_contra π, fun l Λ hΛ => ?_⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.ContraRefl.evMap_bijective hG hπ).2 ⟨Λ, hΛ⟩
  have hev : ∀ m : smoothPart π.dual, Λ m = (m : Module.Dual ℂ V) u := fun m =>
    (LinearMap.congr_fun (congrArg Subtype.val hu) m).symm
  obtain ⟨C, hC, hsupp⟩ := hs.2 u l l.2
  open scoped Pointwise in
    refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
    rw [hev, contra_apply] at hg
    obtain ⟨z, hz, c, hc, e⟩ := hsupp g⁻¹ hg
    refine ⟨z⁻¹, inv_mem hz, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
    have h1 : g = (z * c)⁻¹ := by rw [← e, inv_inv]
    rw [h1, mul_inv_rev]
    exact (Subgroup.mem_center_iff.1 (inv_mem hz) c⁻¹)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_isCusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) :
    (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  have hadm : IsAdmissible x.rep := hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k x.1
  have hirr : (contra x.rep).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG hadm x.2.rep.irr
  have hd : dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) hirr := dif_pos hirr
  rw [hd]
  refine ⟨IrrGL.isCusp_of.2 ⟨hx.1, ?_⟩, rfl⟩
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k x.1 _ _
    (isSupercuspidal_contra hG hadm (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k x.1 _ _ hx.2))

end GlobalTheory.CompanionTheory.DualCusp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.Zcore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) : IsAdmissible x.rep := by
  exact hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr

theorem isIrreducible_contra_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x) x.2.rep.irr

theorem dualCl_eq_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra_rep hA x)]

private theorem dualCl_eq_of_eq_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL (k := k))
    (hy : y = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x)) :
    dualCl y = x := by
  subst hy
  rw [dualCl_eq_of hA]
  conv_rhs => rw [← IrrGL.of_rep x]
  exact IrrGL.of_eq_of.mpr ⟨(GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf (contra x.rep) _ _)).trans
    (GlobalTheory.ContraRefl.evEquiv (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x)).symm⟩

theorem dualCl_dualCl : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)),
    dualCl (dualCl x) = x := by
  intro k _ _ _ _ hA x
  exact dualCl_eq_of_eq_contra hA x _ (dualCl_eq_of hA x)

end GlobalTheory.CompanionTheory.Zcore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_length_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_one | exact GlobalTheory.CompanionTheory.SegFine.fineJac_one | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzeroStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_reciprocity_nonzero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ) (f : (jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep)) (hf : ∃ v, f v ≠ 0), ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr | exact GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr | (intros; apply GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr <;> assumption)
end

