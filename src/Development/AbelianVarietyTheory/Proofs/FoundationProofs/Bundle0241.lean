module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TwistedSelmerCompare

theorem isSSRep_map_iff {Γ K L : Type} [Group Γ] [Field K] [Field L] [CharZero K] [CharZero L] (f : K →+* L)
    {a : ℕ} (ρ : Γ →* GL (Fin a) K) : IsSSRep (mapRep f ρ) ↔ IsSSRep ρ :=
  ⟨fun h => _root_.GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate Γ K a ρ ((_root_.GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff Γ K L f a ρ).1 (_root_.GlobalTheory.isSSRep_trace_nondegenerate Γ L a _ h)),
    fun h => _root_.GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate Γ L a _ ((_root_.GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff Γ K L f a ρ).2 (_root_.GlobalTheory.isSSRep_trace_nondegenerate Γ K a ρ h))⟩

section Param

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem speh_twist (p : Part A.CG) (χ : A.CG 1) (w : PlE H) (c : ℂ) (hp : A.unr (A.locG p.π w))
    (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (spehLoc N A p w) ∧ A.unr (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) ∧
      A.frobEig (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) = (A.frobEig (spehLoc N A p w)).map (· * c) := by
  have hd := A.locG_dim χ w
  have hp' : A.unr (A.locG (A.tw p.π χ) w) := by rw [A.locG_tw]; exact A.unr_char _ _ hd hp hχ
  have he : A.frobEig (A.locG (A.tw p.π χ) w) = (A.frobEig (A.locG p.π w)).map (· * c) := by
    rw [A.locG_tw]; exact A.frobEig_char _ _ c hp hχ hd hc
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp, i1⟩, (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp', i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp') i2, A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp) i1, i3,
      A.frobEig_tw _ _ hp, A.frobEig_tw _ _ hp', he, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 2
    funext x
    simp only [Function.comp_apply]
    ring

theorem iso_twist (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) (c : ℂ)
    (hS : ∀ p ∈ S, A.unr (A.locG p.π w)) (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (isoLoc N A S w) ∧ A.unr (isoLoc N A (twistIso N A S χ) w) ∧
      A.frobEig (isoLoc N A (twistIso N A S χ) w) = (A.frobEig (isoLoc N A S w)).map (· * c) := by
  induction S with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [isoLoc, twistIso, A.frobEig_zero]⟩
  | cons p S ih =>
    obtain ⟨i1, i2, i3⟩ := ih fun q hq => hS q (List.mem_cons_of_mem _ hq)
    obtain ⟨j1, j2, j3⟩ := speh_twist N A p χ w c (hS p List.mem_cons_self) hχ hc
    change A.unr (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) ∧
      A.unr (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) ∧
      A.frobEig (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) =
        (A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A S w))).map (· * c)
    refine ⟨(A.unr_sum _ _).2 ⟨j1, i1⟩, (A.unr_sum _ _).2 ⟨j2, i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ j2 i2, A.frobEig_sum _ _ j1 i1, i3, j3, Multiset.map_add (f := _)]

theorem galPol_twist (S : List (Part A.CG)) (t : ℝ) : ∀ᶠ w in Filter.cofinite,
    galPol A (A.lpTw (A.lpChar (isoLoc N A S w) (A.locG A.etaTinv w)) t) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A S A.etaTinv) w) t) := by
  have h : ∀ᶠ w in Filter.cofinite, ∀ p ∈ {p | p ∈ S}, A.unr (A.locG p.π w) :=
    (Filter.eventually_all_finite (List.finite_toSet S)).2 fun p _ => A.locG_unr_ae p.π
  filter_upwards [h] with w hw
  have hχ := (A.etaTinv_def w).1
  have hd := A.locG_dim A.etaTinv w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((A.frobEig_card _ hχ).trans hd)
  obtain ⟨i1, i2, i3⟩ := iso_twist N A S _ w c hw hχ hc
  unfold galPol
  rw [A.frobEig_tw _ _ i2, A.frobEig_tw _ _ (A.unr_char _ _ hd i1 hχ), i3, A.frobEig_char _ _ c i1 hχ hd hc]

theorem splitOut_ae (a : N.Loc) : ∀ᶠ w in Filter.cofinite, (SplitOut N a w ↔ IsSplitPl H w) := by
  have h1 : (placesOver H.E (N.l a)).Finite := by
    have h0 : Ideal.span {((N.l a : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (N.lPrime a).out.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    simpa [Ideal.dvd_span_singleton, placesOver] using hv
  filter_upwards [h1.compl_mem_cofinite, (N.S a).eventually_cofinite_notMem,
    (N.Q a).eventually_cofinite_notMem] with w a1 a2 a3
  exact ⟨fun h => h.1, fun h => ⟨h, a1, a2, a3⟩⟩

end Param

variable (D : D7)

theorem triple_iff (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG))
    (h : HasParamW D.nd D.naut a σ Sg) (s : TwistedTriples.Trip D a) : TwistedTriples.IsTripleOf D a σ s ↔ IsTriple D a s Sg := by
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    rw [← isSSRep_map_iff (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a))]
    have : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    rw [this]
  · refine Filter.eventually_congr ?_
    filter_upwards [galPol_twist D.nd D.naut Sg ((1 - (D.R.nV : ℝ)) / 2), splitOut_ae D.nd a] with w h1 h2
    rw [h2]
    refine forall_congr' fun hw => forall_congr' fun B => forall_congr' fun g => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [← h1, h.2.2 w hw, ← Polynomial.map_map, ← Matrix.charpoly_map _ (D.ntw.twist₂ a)]
    rfl

theorem allTriples_of_tripAll (h : TwistedTriples.TripAll D) : AllTriples D := fun a σ Sg hg hp =>
  (h a σ hg.symm).imp fun s hs => (triple_iff D a σ Sg hp s).1 hs

end GlobalTheory.TwistedSelmerCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInCone
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestCone

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma mem_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

lemma mem_hw {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ v ∈ wtSub act μ ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, Submodule.mem_iInf]

lemma Eab_mul (a b c d : Ix p q) :
    (Eab a b : Mat p q) * Eab c d = (if b = c then (1 : ℂ) else 0) • Eab a d := by
  split_ifs with h
  · subst h; simp [Eab]
  · simp [Eab, Matrix.single_mul_single_of_ne, h]

lemma lie_Eab {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b c d : Ix p q) (y : V) :
    act (Eab a b) (act (Eab c d) y) = act (Eab c d) (act (Eab a b) y) +
      ((if b = c then (1 : ℂ) else 0) • act (Eab a d) y -
        (if d = a then (1 : ℂ) else 0) • act (Eab c b) y) := by
  have := congrArg (fun f => f y) (hL (Eab a b) (Eab c d))
  simp only [Eab_mul, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at this
  rw [this]; abel

lemma wt_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b : Ix p q)
    {ν : Ix p q → ℚ} {y : V} (hy : y ∈ wtSub act ν) :
    act (Eab a b) y ∈ wtSub act
      (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wt] at hy ⊢
  intro c
  rw [lie_Eab hL, hy, map_smul]
  by_cases h1 : c = a <;> by_cases h2 : c = b
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]
  · subst h2; simp [h1, sub_eq_add_neg, add_smul]
  · simp [h1, h2, Ne.symm h2]

def InCone (ν μ : Ix p q → ℚ) : Prop :=
  ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧
    μ = fun c => ν c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

lemma inCone_self (μ : Ix p q → ℚ) : InCone μ μ :=
  ⟨fun _ _ => 0, by simp, by simp⟩

lemma inCone_step {ν μ : Ix p q → ℚ} (h : InCone ν μ) (i : Fin p) (j : Fin q) :
    InCone (fun c => ν c + ((if c = Sum.inr j then 1 else 0) - (if c = Sum.inl i then 1 else 0))) μ := by
  obtain ⟨m, hm, rfl⟩ := h
  refine ⟨fun a b => m a b + if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0, ?_, ?_⟩
  · intro a b hab
    by_cases h0 : m a b = 0
    · by_cases h1 : a = Sum.inl i
      · by_cases h2 : b = Sum.inr j
        · exact ⟨i, j, h1, h2⟩
        · simp [h0, h2] at hab
      · simp [h0, h1] at hab
    · exact hm a b h0
  · funext c
    have key : ∑ a : Ix p q, ∑ b : Ix p q,
        (((if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0 : ℕ)) : ℚ) *
          ((if c = a then 1 else 0) - (if c = b then 1 else 0)) =
        (if c = Sum.inl i then 1 else 0) - (if c = Sum.inr j then 1 else 0) := by
      rw [Finset.sum_eq_single (Sum.inl i), Finset.sum_eq_single (Sum.inr j)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, key]
    ring

lemma act_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, act (Eab a b) y ∈ N) (Z : Mat p q) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b)

lemma exists_down {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub act μ) : ∃ D : Submodule ℂ V, v ∈ D ∧
      (∀ i j, ∀ x ∈ D, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ D) ∧
      (∀ a b, posC a b → ∀ x ∈ D, act (Eab a b) x ∈ D) ∧
      D ≤ ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1 := by
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ i j, ∀ x ∈ N, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b y (Submodule.mem_sInf.1 hy M hM)
  refine ⟨sInf S, hG.1, hG.2, fun a b hab x hx => ?_, sInf_le ⟨?_, fun i j x hx => ?_⟩⟩
  · have hG' : (sInf S ⊓ (sInf S).comap (act (Eab a b))) ∈ S := by
      refine ⟨⟨hG.1, ?_⟩, fun i j y hy => ⟨hG.2 i j y hy.1, ?_⟩⟩
      · show act (Eab a b) v ∈ sInf S
        rw [hv.2 a b hab]; exact Submodule.zero_mem _
      · show act (Eab a b) (act _ y) ∈ sInf S
        rw [lie_Eab hL]
        refine Submodule.add_mem _ (hG.2 i j _ hy.2) ?_
        rcases a with a | a <;> rcases b with b | b
        · refine Submodule.sub_mem _ (by simp) (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1))
        · exact absurd hab (by simp [posC])
        · exact absurd hab (by simp [posC])
        · refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1)) (by simp)
    exact (sInf_le hG' hx).2
  · exact Submodule.mem_iSup_of_mem (⟨μ, inCone_self μ⟩ : {ν // InCone ν μ}) hv.1
  · refine Submodule.iSup_induction _ (motive := fun x => act (Eab (Sum.inr j) (Sum.inl i)) x ∈
      ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1) hx ?_ (by simp) ?_
    · intro ν y hy
      exact Submodule.mem_iSup_of_mem (⟨_, inCone_step ν.2 i j⟩ : {ν // InCone ν μ})
        (wt_shift hL _ _ hy)
    · intro y z hy hz
      rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

lemma wt_orth {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H)
    (hadj : ∀ Z x y, inner ℂ (E (act Z x)) (E y) = inner ℂ (E x) (E (act (adjZ Z) y)))
    {ν Λ : Ix p q → ℚ} (hne : ν ≠ Λ) {x e : V} (hx : x ∈ wtSub act ν) (he : e ∈ wtSub act Λ) :
    inner ℂ (E x) (E e) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hne
  have h := hadj (Eab c c) x e
  rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul, mem_wt.1 hx, mem_wt.1 he,
    map_smul, map_smul, inner_smul_left, inner_smul_right, map_ratCast, ← sub_eq_zero,
    ← sub_mul] at h
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hc ?_
  exact_mod_cast sub_eq_zero.1 h0

theorem cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro p q M H _ _ E hE hadj Λ e he hlow hgen μ v hv
  by_contra hcone
  change ¬ InCone Λ μ at hcone
  obtain ⟨D, hvD, hDm, hDp, hDle⟩ := exists_down M.lie hv.2
  rw [mem_hw] at he
  let C : Submodule ℂ M.V := ((D.map E)ᗮ).comap E
  have hC : ∀ x, x ∈ C ↔ ∀ d ∈ D, inner ℂ (E d) (E x) = 0 := by
    intro x
    simp only [C, Submodule.mem_comap, Submodule.mem_orthogonal]
    constructor
    · intro h d hd; exact h _ ⟨d, hd, rfl⟩
    · rintro h _ ⟨d, hd, rfl⟩; exact h d hd
  have hstab : ∀ a b, (∀ d ∈ D, M.act (Eab a b) d ∈ D) → ∀ x ∈ C, M.act (Eab b a) x ∈ C := by
    intro a b h x hx
    rw [hC] at hx ⊢
    intro d hd
    have := hadj (adjZ (Eab b a)) d x
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at this
    rw [← this, GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact hx _ (D.smul_mem _ (h d hd))
  have heC : e ∈ C := by
    rw [hC]
    intro d hd
    refine Submodule.iSup_induction _ (motive := fun x => inner ℂ (E x) (E e) = 0) (hDle hd) ?_
      (by simp) ?_
    · intro ν y hy
      exact wt_orth E hadj (fun h : ν.1 = Λ => hcone (h ▸ ν.2)) hy he.1
    · intro y z hy hz
      rw [map_add (f := _), inner_add_left, hy, hz, add_zero]
  let r : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.1)
  have hr : Function.Injective r := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · congr 1; ext; omega
    · have := b.2; omega
    · have := a.2; omega
    · congr 1; ext; omega
  have hcase : ∀ a b, r a < r b → posC a b ∨ ∃ i j, a = Sum.inr j ∧ b = Sum.inl i := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · left; show a < b; rw [Fin.lt_def]; omega
    · have := b.2; omega
    · exact Or.inr ⟨_, _, rfl, rfl⟩
    · left; exact h
  obtain ⟨U, heU, hU, hUmin, -⟩ := GlobalTheory.ExtremalGen.exists_generated p q M.V M.act M.lie (fun _ _ => True)
    ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ r hr Λ e he.1 (by
      intro a b _ h
      rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
      · exact he.2 a b h
      · exact hlow i j)
  have hUC : U ≤ C := hUmin C heC (by
    intro a b _ h
    refine hstab a b ?_
    rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
    · exact hDp a b h
    · exact hDm i j)
  have hgU : genSub M.act {e} ≤ U :=
    sInf_le ⟨by simpa using heU, fun Z y hy => act_mem U y (fun a b => hU a b trivial y hy) Z⟩
  have hvC : v ∈ C := hUC (hgU (hgen ▸ Submodule.mem_top))
  have h0 := (hC v).1 hvC v hvD
  rw [inner_self_eq_zero] at h0
  exact hv.1 (hE (by rw [h0, map_zero]))

end GlobalTheory.LowestCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaHalfPeriodValueIsIntegral
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Topology
open Filter

namespace GlobalTheory.HalfPeriodValue

lemma second_order {f f' a s b : ℂ → ℂ} {c : ℂ} (hf : ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt f (f' z) z)
    (hf' : HasDerivAt f' c 0) (h0 : f 0 = 0) (h0' : f' 0 = 0) (ha : Differentiable ℂ a)
    (hs : Differentiable ℂ s) (hb : Differentiable ℂ b) (hs0 : s 0 = 0) (hs1 : deriv s 0 = 1)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), f z * a z = s z ^ 2 * b z) : c * a 0 = 2 * b 0 := by
  have d : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → Differentiable ℂ (deriv g) := fun hg =>
    differentiableOn_univ.1 (hg.differentiableOn.deriv isOpen_univ)
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), f' z * a z + f z * deriv a z =
      (2 * s z * deriv s z) * b z + (s z * s z) * deriv b z := by
    filter_upwards [hf, h.eventually_nhds] with z hz hz'
    have e1 := hz.mul (ha z).hasDerivAt
    have e2 := ((hs z).hasDerivAt.mul (hs z).hasDerivAt).mul (hb z).hasDerivAt
    have e3 := e1.unique (e2.congr_of_eventuallyEq (by
      filter_upwards [hz'] with w hw
      simpa [sq] using hw))
    simp only [Pi.mul_apply] at e3
    linear_combination e3
  have e1 := (hf'.mul (ha 0).hasDerivAt).add (hf.self_of_nhds.mul (d ha 0).hasDerivAt)
  have e2 := ((((hs 0).hasDerivAt.const_mul 2).mul (d hs 0).hasDerivAt).mul (hb 0).hasDerivAt).add
    (((hs 0).hasDerivAt.mul (hs 0).hasDerivAt).mul (d hb 0).hasDerivAt)
  have e3 := e1.unique (e2.congr_of_eventuallyEq (by
      filter_upwards [h1] with w hw
      simpa using hw))
  simp only [Pi.mul_apply, h0, h0', hs0, hs1] at e3
  linear_combination e3

lemma isIntegral_of_eq {u j : ℂ} (hj : IsIntegral ℤ j) (h : (u ^ 12 + 16) ^ 3 = j * u ^ 12) :
    IsIntegral ℤ u := by
  refine IsIntegral.of_pow (n := 12) (by norm_num) ?_
  let R := integralClosure ℤ ℂ
  refine isIntegral_trans (A := R) _ ?_
  refine ⟨(Polynomial.X + 16) ^ 3 - Polynomial.C (⟨j, hj⟩ : R) * Polynomial.X, by monicity!, ?_⟩
  rw [← Polynomial.aeval_def]
  simp only [map_sub, map_pow, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat]
  exact sub_eq_zero.2 h

theorem value_half_period : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → IsIntegral ℤ (1728 * g2 Λ ^ 3) → ∀ t, 2 * t ∈ Λ → t ∉ Λ → U1 Λ t (sgStar Λ) 0 ≠ 0 ∧ IsIntegral ℤ (U1 Λ t (sgStar Λ) 0) ∧ U1 Λ t (sgStar Λ) 0 ^ 8 = 16 * (g2 Λ - 3 * wpF Λ t ^ 2) ∧ 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
  intro Λ hΛ hΔ hj t h2 ht
  obtain ⟨⟨hd, hd1, hodd, hU⟩, hzero, -, hwp, -⟩ := _root_.GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hli, hΛ⟩ := hΛ
  let L : PeriodPair := ⟨w₁, w₂, hli⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by
    rw [hΛ, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp [L]
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := _root_.GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hP' : L.derivWeierstrassP t = 0 := by
    have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, (hL _).1 h2⟩
    rw [L.derivWeierstrassP_neg] at e1
    have : -t + 2 * t = t := by ring
    simp only [this] at e1
    linear_combination e1 / 2
  have hcub : 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
    rw [(hw t ht).1, hg2, hg3, ← L.derivWeierstrassP_sq t htL, hP']
    simp
  set k : ℂ := (Real.pi : ℂ) * (starRingEnd ℂ) t / (area Λ : ℂ) with hk
  have hsys := GlobalTheory.weierstrass_system_add_const L t (z := 0) (by simpa using htL)
  have key := second_order (f := fun z => L.weierstrassP (z + t) - L.weierstrassP t)
    (f' := fun z => L.derivWeierstrassP (z + t))
    (a := fun z => sgStar Λ (z + t) ^ 2 * sgStar Λ t ^ 2) (s := sgStar Λ)
    (b := fun z => Complex.exp (2 * k * z + 2 * k * t))
    (hsys.mono fun z hz => hz.1.sub_const _) hsys.self_of_nhds.2 (by simp) (by simpa using hP')
    (by fun_prop) hd (by fun_prop) ((hzero 0).2 Λ.zero_mem) hd1 (by
      filter_upwards [(continuous_add_const t).continuousAt.eventually
        (GlobalTheory.eventually_notMem_periodLattice L (z := 0 + t) (by simpa using htL))] with z hz
      have hz' : z + t ∉ Λ := fun h => hz ((hL _).1 h)
      have e1 := hwp (z + t) t hz' ht
      rw [(hw _ hz').1, (hw t ht).1] at e1
      have e2 := hU (2 * t) h2 z
      rw [if_neg (by simpa using ht)] at e2
      have e3 : -(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
          (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)) =
          -(2 * k * z + 2 * k * t) := by
        rw [hk, map_mul, map_ofNat]; ring
      simp only [U1] at e2
      rw [e3, Complex.exp_neg] at e2
      have e4 : z + t + t = z + 2 * t := by ring
      rw [e1, e4, add_sub_cancel_right]
      have e5 := Complex.exp_ne_zero (2 * k * z + 2 * k * t)
      rw [mul_inv_eq_iff_eq_mul₀ e5] at e2
      rw [e2]; ring)
  simp only [zero_add, mul_zero] at key
  rw [← (hw t ht).1, ← hg2] at key
  have hu : U1 Λ t (sgStar Λ) 0 ^ 4 * Complex.exp (2 * k * t) = sgStar Λ t ^ 4 := by
    simp only [U1, zero_add]
    rw [mul_pow, mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : ((4 : ℕ) : ℂ) * (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / (area Λ : ℂ) -
      (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) + 2 * k * t = 0 := by
      rw [hk]; push_cast; ring
    rw [this, Complex.exp_zero, mul_one]
  set u := U1 Λ t (sgStar Λ) 0
  set e := wpF Λ t
  have h4 : (12 * e ^ 2 - g2 Λ) * u ^ 4 = 4 := by
    apply mul_right_cancel₀ (Complex.exp_ne_zero (2 * k * t))
    linear_combination 2 * key + (12 * e ^ 2 - g2 Λ) * hu
  have hD : (12 * e ^ 2 - g2 Λ) ^ 2 * (g2 Λ - 3 * e ^ 2) = 1 := by
    have h3 : g3 Λ = 4 * e ^ 3 - g2 Λ * e := by linear_combination -hcub
    rw [← hΔ, TaylorLogMetric.discr, h3]; ring
  have h8 : u ^ 8 = 16 * (g2 Λ - 3 * e ^ 2) := by
    linear_combination (-u ^ 8) * hD +
      (g2 Λ - 3 * e ^ 2) * ((12 * e ^ 2 - g2 Λ) * u ^ 4 + 4) * h4
  refine ⟨fun h => by simp [h] at h4, isIntegral_of_eq hj ?_, h8, hcub⟩
  have h5 : u ^ 12 + 16 = 12 * g2 Λ * u ^ 4 := by
    linear_combination u ^ 4 * h8 - 4 * h4
  rw [h5]; ring

end GlobalTheory.HalfPeriodValue
end

