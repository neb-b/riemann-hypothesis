module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0017

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicComponentLeLowerWeights
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_WS (E : GLOps n K V) (S : Set (Fin n → ℤ)) : Submodule K V := ⨆ ν ∈ S, weightSp E ν

theorem cr_WS_mono (E : GLOps n K V) {S S' : Set (Fin n → ℤ)} (h : S ⊆ S') : cr_WS E S ≤ cr_WS E S' := by
  unfold cr_WS
  exact biSup_mono fun i hi => h hi

theorem cr_WS_of_mem (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν : Fin n → ℤ} (h : ν ∈ S) :
    weightSp E ν ≤ cr_WS E S := by
  unfold cr_WS
  exact le_iSup₂ (f := fun ν (_ : ν ∈ S) => weightSp E ν) ν h

theorem cr_wt_disj [CharZero K] (E : GLOps n K V) {ν ν' : Fin n → ℤ} (hne : ν ≠ ν') {x : V}
    (h1 : x ∈ weightSp E ν) (h2 : x ∈ weightSp E ν') : x = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have e1 := (v2rep_mem_weightSp E ν x).1 h1 a
  have e2 := (v2rep_mem_weightSp E ν' x).1 h2 a
  have e3 : ((ν a : K) - (ν' a : K)) • x = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
  rcases smul_eq_zero.1 e3 with h | h
  · exact absurd (Int.cast_injective (sub_eq_zero.1 h)) ha
  · exact h

theorem cr_wt_diag_stable (E : GLOps n K V) (ν : Fin n → ℤ) (a : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    E a a x ∈ weightSp E ν := by
  rw [(v2rep_mem_weightSp E ν x).1 hx a]
  exact Submodule.smul_mem _ _ hx

theorem cr_WS_mem [CharZero K] (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν0 : Fin n → ℤ} {z : V}
    (hz : z ∈ cr_WS E S) (hz0 : z ∈ weightSp E ν0) (hne : z ≠ 0) : ν0 ∈ S := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hz
  have hf' : ∀ ν, f ν ∈ weightSp E ν := fun ν => (iSup_le fun _ => le_rfl : (⨆ (_ : ν ∈ S), weightSp E ν) ≤ _) (hf ν)
  have h := v2rep_comp_mem E (weightSp E ν0) (fun a x hx => cr_wt_diag_stable E ν0 a x hx) f.support
    (fun ν => f ν) (fun ν _ => hf' ν) hz0
  have hsupp : ∀ ν ∈ f.support, ν = ν0 := by
    intro ν hν
    by_contra hh
    exact (Finsupp.mem_support_iff.1 hν) (cr_wt_disj E hh (hf' ν) (h ν hν))
  by_contra hS
  have h0 : f ν0 = 0 := by
    have := hf ν0
    simpa [hS] using this
  apply hne
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [hsupp ν hν]
  exact h0

def cr_Low (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n ∧ 0 < weightHeight' (lam - ν)}

def weightsBelow (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n}

theorem cr_Low_sub (lam : Fin n → ℤ) : cr_Low lam ⊆ weightsBelow lam := fun _ hν => hν.1

theorem cr_lower (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    cr_WS E (weightsBelow lam) ≤ (cr_WS E (cr_Low lam)).comap (E a b) := by
  refine iSup₂_le fun ν hν x hx => ?_
  show E a b x ∈ cr_WS E (cr_Low lam)
  refine cr_WS_of_mem E ?_ (v2rep_shift E hR a b ν x hx)
  have e : lam - (ν + rootW a b) = (lam - ν) + rootW b a := by
    ext c; simp only [rootW, Pi.sub_apply, Pi.add_apply]; ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact add_mem hν (cr_root_mem b a h)
  · rw [e, cr_ht_add]
    have h1 := cr_Pos_ht hν
    have h2 := cr_ht_root b a h
    omega

theorem cr_Y_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) (k : ℕ) :
    cyclicLevelSubmodule E v k ≤ Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) := by
  have hv0 : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ cr_WS E (weightsBelow lam) := by
    refine sup_le ?_ (cr_WS_mono E (cr_Low_sub lam))
    rw [Submodule.span_singleton_le_iff_mem]
    refine cr_WS_of_mem E ?_ hv.2.1
    show lam - lam ∈ cr_Pos n
    rw [sub_self]; exact zero_mem _
  induction k with
  | zero => exact le_sup_left
  | succ k ih =>
    refine sup_le ih ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    refine (ih.trans hv0).trans ((cr_lower E hR lam ab.1 ab.2 hab).trans ?_)
    exact Submodule.comap_mono le_sup_right

theorem cr_isoIn_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u, hu, v, hvW, hv, rfl⟩
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR lam v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  have hle : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
    refine sup_le_sup_right ?_ _
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨hvW, hv.2.1⟩
  exact hle (cr_Y_le E hR lam v hv k hk)

theorem isotypic_component_le_lower_weights (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ cr_WS E (weightsBelow lam) := by
  refine (cr_isoIn_le E hR Wx lam).trans (sup_le ?_ (cr_WS_mono E (cr_Low_sub lam)))
  refine inf_le_right.trans (cr_WS_of_mem E ?_)
  show lam - lam ∈ cr_Pos n
  rw [sub_self]; exact zero_mem _

theorem cr_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hne : v ≠ 0) (hv : v ∈ weightSp E mu) (a b : Fin n) (hab : a ≠ b) (he : E a b v = 0) : mu b ≤ mu a := by
  have hba : b ≠ a := hab.symm
  have hef : E a b * E b a - E b a * E a b = E a a - E b b := by
    have := rel a b b a
    simpa using this
  have h1 : E a a * E a b - E a b * E a a = E a b := by
    have := rel a a a b
    simpa [hba] using this
  have h2 : E b b * E a b - E a b * E b b = - E a b := by
    have := rel b b a b
    simpa [hba] using this
  have h3 : E a a * E b a - E b a * E a a = - E b a := by
    have := rel a a b a
    simpa [hab] using this
  have h4 : E b b * E b a - E b a * E b b = E b a := by
    have := rel b b b a
    simpa [hab] using this
  have hva : E a a v = (mu a : K) • v := (v2rep_mem_weightSp E mu v).1 hv a
  have hvb : E b b v = (mu b : K) • v := (v2rep_mem_weightSp E mu v).1 hv b
  have hhf : (E a a - E b b) * E b a - E b a * (E a a - E b b) = -(2 • E b a) := by
    have : (E a a - E b b) * E b a - E b a * (E a a - E b b) =
        (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
    rw [this, h3, h4, two_smul]; abel
  have hhe : (E a a - E b b) * E a b - E a b * (E a a - E b b) = 2 • E a b := by
    have : (E a a - E b b) * E a b - E a b * (E a a - E b b) =
        (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
    rw [this, h1, h2, two_smul]; abel
  have hhv : (E a a - E b b) v = ((mu a : K) - (mu b : K)) • v := by
    rw [LinearMap.sub_apply, hva, hvb, sub_smul]
  by_cases hh0 : E a a - E b b = 0
  · rw [hh0, LinearMap.zero_apply] at hhv
    rcases smul_eq_zero.1 hhv.symm with h | h
    · exact (Int.cast_injective (sub_eq_zero.1 h)).ge
    · exact absurd h hne
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
    { h_ne_zero := hh0
      lie_e_f := by rw [Ring.lie_def]; exact hef
      lie_h_e_nsmul := by rw [Ring.lie_def]; exact hhe
      lie_h_f_nsmul := by rw [Ring.lie_def]; exact hhf }
  have P : t.HasPrimitiveVectorWith v ((mu a : K) - (mu b : K)) :=
    { ne_zero := hne
      lie_h := by rw [Module.End.lie_apply]; exact hhv
      lie_e := by rw [Module.End.lie_apply]; exact he }
  obtain ⟨m, hm⟩ := P.exists_nat
  have : ((mu a - mu b : ℤ) : K) = ((m : ℤ) : K) := by push_cast; exact hm
  have := Int.cast_injective this
  omega

theorem cr_hwv_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hv : IsHWV E mu v) : Dominant mu := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · exact cr_dom E rel hv.1 hv.2.1 a b h.ne (hv.2.2 a b h)
  · rw [h]

theorem cr_isoIn_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) (Wx : Submodule K V)
    {mu : Fin n → ℤ} {x : V} (hx : x ∈ isotypicPartIn E Wx mu) (hne : x ≠ 0) : Dominant mu := by
  by_contra hd
  apply hne
  have : isotypicPartIn E Wx mu = ⊥ := by
    rw [isotypicPartIn, Submodule.span_eq_bot]
    rintro y ⟨u, _, v, _, hv, rfl⟩
    exact absurd (cr_hwv_dom E rel hv) hd
  rw [this] at hx
  exact (Submodule.mem_bot K).1 hx

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.MultidegreePartFinitelyGenerated
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def fockLattice {p : ℕ} (hV : ValuationProperties p O) (σ : Type) : Submodule O (MvPolynomial σ (KK O)) where
  carrier := {F | InBB (O := O) p F}
  zero_mem' := fock_lattice_zero_mem hV
  add_mem' := fun hF hG => fock_lattice_add_mem hV hF hG
  smul_mem' := fun o _ hF => fock_lattice_smul_mem hV o hF

theorem multidegree_monomials_finite {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) :
    {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin n => d x.1))).subset ?_
  intro m hm
  rw [Set.mem_Iic, Finsupp.le_def]
  rintro ⟨i, c⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← hm i]
  exact Finset.single_le_sum (f := fun c' => m (i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem multidegree_part_finitely_generated {p : ℕ} (hp0 : (p : KK O) ≠ 0) {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) (N : ℕ)
    (h : ∀ F ∈ L, ∀ m, (∀ i, multideg m i = d i) → ∃ o : O, (p : KK O) ^ N * F.coeff m = algebraMap O (KK O) o) :
    (latticeMultidegreePart L d).FG := by
  classical
  set S := (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset with hS
  let f : ↥(Pol (KK O) n d) →ₗ[O] (S → KK O) :=
    { toFun := fun F s => (p : KK O) ^ N * (F : MvPolynomial (ι × Fin n) (KK O)).coeff s.1
      map_add' := fun F G => by
        funext s
        simp [mul_add]
      map_smul' := fun o F => by
        funext s
        simp [MvPolynomial.coeff_smul, mul_smul_comm] }
  let g : (S → O) →ₗ[O] (S → KK O) :=
    LinearMap.pi (fun s => (Algebra.linearMap O (KK O)).comp (LinearMap.proj s))
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    apply Subtype.ext
    ext m
    simp only [Submodule.coe_zero, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ S
    · have h0 := congrFun hF ⟨m, hm⟩
      change (p : KK O) ^ N * (F : MvPolynomial _ (KK O)).coeff m = 0 at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp0)
    · by_contra hne
      apply hm
      have hF2 : (F : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := F.2
      have hsupp : m ∈ (F : MvPolynomial _ (KK O)).support := MvPolynomial.mem_support_iff.2 hne
      exact (Set.Finite.mem_toFinset _).2 (((MvPolynomial.mem_restrictSupport_iff _).1 hF2) (Finset.mem_coe.2 hsupp))
  have hle : (latticeMultidegreePart L d).map f ≤ LinearMap.range g := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : MvPolynomial (ι × Fin n) (KK O)) ∈ L := hx
    choose o ho using fun s : S => h _ hx' s.1 ((Set.Finite.mem_toFinset _).1 s.2)
    refine ⟨o, ?_⟩
    funext s
    exact (ho s).symm
  have hW : (LinearMap.range g).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map g
  haveI : IsNoetherian O (LinearMap.range g) := isNoetherian_of_fg_of_noetherian _ hW
  have h1 : (((latticeMultidegreePart L d).map f).comap (LinearMap.range g).subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map (LinearMap.range g).subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
  exact Submodule.fg_of_fg_map_injective f hinj h2

theorem multidegree_part_spans {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ)
    (h : ∀ m, monomial m (1 : KK O) ∈ L) : MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
      MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := x.2
  have key : ∀ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support,
      monomial m (1 : KK O) ∈ Pol (KK O) n d := by
    intro m hm
    show monomial m (1 : KK O) ∈ MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i}
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_coe] at hm'
    have hm'' := MvPolynomial.support_monomial_subset hm'
    rw [Finset.mem_singleton] at hm''
    subst hm''
    exact ((MvPolynomial.mem_restrictSupport_iff _).1 hx) (Finset.mem_coe.2 hm)
  have hx2 : x = ∑ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support.attach,
      (x : MvPolynomial (ι × Fin n) (KK O)).coeff m.1 •
        (⟨monomial m.1 1, key m.1 m.2⟩ : Pol (KK O) n d) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [Finset.sum_attach _ (fun m => monomial m ((x : MvPolynomial (ι × Fin n) (KK O)).coeff m))]
    exact (x : MvPolynomial (ι × Fin n) (KK O)).as_sum
  rw [hx2]
  show _ ∈ Submodule.span (KK O) _
  refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact h m.1

theorem fock_lattice_finite_spanning_holds {p : ℕ} (hp : p.Prime) (S0 : UniformizedDVR p O) (hV : ValuationProperties p O) : FockLatticeFiniteSpanning p O := by
  intro n ι _
  have hp0 : (p : KK O) ≠ 0 := by
    intro h0
    have h1 := hV.2.2.2.1 p hp.ne_zero
    rw [h0, hV.1] at h1
    exact WithTop.top_ne_coe h1
  have hv1 : vK p (1 : KK O) = 0 := by
    have h1 := hV.2.2.2.1 1 one_ne_zero
    rw [Nat.cast_one, Nat.padicValNat_def, multiplicity_one_right] at h1
    simpa using h1
  have key : ∀ (x : WithTop ℚ) (a b : ℚ), 0 ≤ x + (a : WithTop ℚ) → a ≤ b → 0 ≤ (b : WithTop ℚ) + x := by
    intro x a b hx hab
    induction x using WithTop.recTopCoe with
    | top => simp
    | coe q =>
      rw [← WithTop.coe_add] at hx ⊢
      rw [WithTop.coe_nonneg] at hx ⊢
      linarith
  have hmono : ∀ m : ι × Fin n →₀ ℕ, monomial m (1 : KK O) ∈ fockLattice hV (ι × Fin n) := by
    intro m
    show InBB (O := O) p (monomial m (1 : KK O))
    rw [fock_lattice_monomial_iff hV, hv1, zero_add]
    unfold halfFactorialValuation
    exact WithTop.coe_nonneg.2 (by positivity)
  refine ⟨fockLattice hV (ι × Fin n), fun F => Iff.rfl, fun d => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact multidegree_part_finitely_generated hp0 _ d 0 (fun F hF m _ => by simpa using (mem_integral_poly_iff_coeff F).1 hF m)
  · exact multidegree_part_spans _ d (fun m => by simpa using integer_monomial_mem_integral (O := O) m 1)
  · refine multidegree_part_finitely_generated hp0 _ d
      (∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m)) ?_
    intro F hF m hm
    have hF' : InBB (O := O) p F := hF
    have h0 := (mem_fock_lattice_iff_coeff hV F).1 hF' m
    unfold halfFactorialValuation at h0
    apply (hV.2.2.2.2.2 _).1
    haveI := Fact.mk hp
    rw [hV.2.1, ← Nat.cast_pow, hV.2.2.2.1 _ (pow_ne_zero _ hp.ne_zero), Nat.padicValNat_def, Nat.multiplicity_prime_pow]
    refine key _ _ _ h0 ?_
    have hmS : m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset := (Set.Finite.mem_toFinset _).2 hm
    have hle := Finset.single_le_sum (f := fun m => padicValNat p (expFact m)) (fun _ _ => Nat.zero_le _) hmS
    have hle' : (padicValNat p (expFact m) : ℚ) ≤
        ((∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m) : ℕ) : ℚ) := by
      exact_mod_cast hle
    have hnn : (0 : ℚ) ≤ padicValNat p (expFact m) := by positivity
    linarith
  · exact multidegree_part_spans _ d hmono

end Formalism.MainNotions.G.GLWeightTheory
end
end

