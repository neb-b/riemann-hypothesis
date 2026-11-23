module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSatakeIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernFaith
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

private theorem anti_of_gap {n : ℕ} {c : Fin n → ℤ} {N : ℕ} (h : ∀ i j, i < j → c j + N ≤ c i) : Antitone c := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have := h i j hlt
    omega

private theorem gap_add {n : ℕ} {c : Fin n → ℤ} (a : Fin n →₀ ℕ) {N : ℕ}
    (h : ∀ i j, i < j → c j + ((a.degree + N : ℕ) : ℤ) ≤ c i) :
    ∀ i j, i < j → (c + fun i => (a i : ℤ)) j + N ≤ (c + fun i => (a i : ℤ)) i := by
  intro i j hij
  have h1 := h i j hij
  have h2 : a j ≤ a.degree := Finsupp.le_degree j a
  simp only [Pi.add_apply]
  push_cast at h1
  omega

private theorem anti_fund (n m : ℕ) : Antitone (fund n m) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [fund]
  split_ifs <;> omega

private theorem abs_mono {n : ℕ} {A H : Type} [CommRing A] [Ring H] [Algebra A H] (q : A)
    (T : (Fin n → ℤ) → H) (th : MvPolynomial (Fin n) A →ₐ[A] H)
    (hmul : ∀ c d, Antitone c → Antitone d → T c * T d = T (c + d))
    (hu : ∀ c, Antitone c → IsUnit (T c))
    (hX : ∀ i : Fin n, th (MvPolynomial.X i) * T (fund n i) = (q ^ (i : ℕ)) • T (fund n ((i : ℕ) + 1)))
    (a : Fin n →₀ ℕ) : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (a.degree : ℤ) ≤ c i) →
      ∃ m : ℕ, T c * th (MvPolynomial.monomial a 1) = q ^ m • T (c + fun i => (a i : ℤ)) := by
  have hadd : ∀ a b : Fin n →₀ ℕ,
      (∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (a.degree : ℤ) ≤ c i) →
        ∃ m : ℕ, T c * th (MvPolynomial.monomial a 1) = q ^ m • T (c + fun i => (a i : ℤ))) →
      (∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (b.degree : ℤ) ≤ c i) →
        ∃ m : ℕ, T c * th (MvPolynomial.monomial b 1) = q ^ m • T (c + fun i => (b i : ℤ))) →
      ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + ((a + b).degree : ℤ) ≤ c i) →
        ∃ m : ℕ, T c * th (MvPolynomial.monomial (a + b) 1) = q ^ m • T (c + fun i => ((a + b) i : ℤ)) := by
    intro a b ha hb c hc
    rw [map_add (f := _)] at hc
    obtain ⟨m, hm⟩ := ha c fun i j hij => by
      have := hc i j hij
      push_cast at this
      omega
    obtain ⟨m', hm'⟩ := hb _ (gap_add a hc)
    refine ⟨m + m', ?_⟩
    have e : (MvPolynomial.monomial (a + b) (1 : A)) = MvPolynomial.monomial a 1 * MvPolynomial.monomial b 1 := by
      rw [MvPolynomial.monomial_mul, one_mul]
    rw [e, map_mul, ← mul_assoc, hm, smul_mul_assoc, hm', smul_smul, pow_add]
    congr 2
    ext i
    simp [add_assoc]
  have h0 : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + ((0 : Fin n →₀ ℕ).degree : ℤ) ≤ c i) →
      ∃ m : ℕ, T c * th (MvPolynomial.monomial 0 1) = q ^ m • T (c + fun i => ((0 : Fin n →₀ ℕ) i : ℤ)) := by
    intro c _
    refine ⟨0, ?_⟩
    have : (c + fun i => ((0 : Fin n →₀ ℕ) i : ℤ)) = c := by ext i; simp
    rw [this]
    simp
  have h1 : ∀ l : Fin n, ∀ c : Fin n → ℤ, (∀ i j, i < j → c j + (((Finsupp.single l 1 : Fin n →₀ ℕ).degree : ℕ) : ℤ) ≤ c i) →
      ∃ m : ℕ, T c * th (MvPolynomial.monomial (Finsupp.single l 1) 1) =
        q ^ m • T (c + fun i => ((Finsupp.single l 1 : Fin n →₀ ℕ) i : ℤ)) := by
    intro l c hc
    refine ⟨l, ?_⟩
    have hc' : Antitone (c + fun i => ((Finsupp.single l 1 : Fin n →₀ ℕ) i : ℤ)) :=
      anti_of_gap (N := 0) (gap_add _ (by simpa using hc))
    apply (hu _ (anti_fund n l)).mul_right_cancel
    change T c * th (MvPolynomial.X l) * _ = _
    rw [mul_assoc, hX, mul_smul_comm, smul_mul_assoc, hmul _ _ (anti_of_gap hc) (anti_fund _ _),
      hmul _ _ hc' (anti_fund _ _)]
    congr 2
    ext i
    simp only [Pi.add_apply, fund, Finsupp.single_apply, Fin.ext_iff]
    split_ifs <;> push_cast <;> omega
  induction a using Finsupp.induction_linear with
  | zero => exact h0
  | add a b ha hb => exact hadd a b ha hb
  | single l m =>
    induction m with
    | zero => rw [Finsupp.single_zero]; exact h0
    | succ m ih => rw [Finsupp.single_add]; exact hadd _ _ ih (h1 l)

private theorem abs_faith {n : ℕ} {A H : Type} [CommRing A] [Ring H] [Algebra A H] (q : A) (hq : IsUnit q)
    (T : (Fin n → ℤ) → H) (th : MvPolynomial (Fin n) A →ₐ[A] H) (e : H)
    (hmul : ∀ c d, Antitone c → Antitone d → T c * T d = T (c + d))
    (hu : ∀ c, Antitone c → IsUnit (T c))
    (hX : ∀ i : Fin n, th (MvPolynomial.X i) * T (fund n i) = (q ^ (i : ℕ)) • T (fund n ((i : ℕ) + 1)))
    (hli : LinearIndependent A fun a : {a : Fin n → ℤ // Antitone a} => T a.1 * e)
    (p : MvPolynomial (Fin n) A) (hp : th p * e = 0) : p = 0 := by
  classical
  set N : ℕ := p.support.sup Finsupp.degree with hN
  let c : Fin n → ℤ := fun i => -((i : ℕ) : ℤ) * N
  have hc : ∀ a : p.support, ∀ i j, i < j → c j + (a.1.degree : ℤ) ≤ c i := by
    intro a i j hij
    have h1 : a.1.degree ≤ N := Finset.le_sup (f := Finsupp.degree) a.2
    have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
    have h3 : (a.1.degree : ℤ) ≤ N := by exact_mod_cast h1
    have h4 : (0 : ℤ) ≤ N := Int.natCast_nonneg _
    simp only [c]
    nlinarith
  choose m hm using fun a : p.support => abs_mono q T th hmul hu hX a.1 c (hc a)
  let f : p.support → {a : Fin n → ℤ // Antitone a} := fun a =>
    ⟨c + fun i => (a.1 i : ℤ), anti_of_gap (N := 0) (gap_add _ (by simpa using hc a))⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, add_right_inj] at this
    ext i
    exact_mod_cast congrFun this i
  have hli' := Fintype.linearIndependent_iff.1 (hli.comp f hf) (fun a => p.coeff a.1 * q ^ m a) (by
    have h0 : T c * (th p * e) = 0 := by rw [hp, mul_zero]
    rw [← h0]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [p.as_sum, ← Finset.sum_coe_sort, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : MvPolynomial.monomial a.1 (p.coeff a.1) = p.coeff a.1 • MvPolynomial.monomial a.1 (1 : A) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_mul_assoc, mul_smul_comm, ← mul_assoc, hm, smul_mul_assoc, smul_smul]
    rfl)
  ext a
  by_contra ha
  have ha' : a ∈ p.support := by simpa using ha
  have := hli' ⟨a, ha'⟩
  exact ha (by simpa using ((hq.pow _).mul_left_eq_zero).1 this)

private theorem dom_pw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {x : kˣ} (hx : IsUnif x) {c : Fin n → ℤ} (hc : Antitone c) : Dom fun i => x ^ c i := by
  obtain ⟨p, -, hp⟩ := hx
  intro i j hij
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  have h0 : 0 < valuation k (x : k) := by simp [zero_lt_iff]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hc hij)

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.bernFaith :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A] (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤)), (∀ w, b.T w = hT A (iwC k n ⊤) (pm k n w)) → (∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) → b.Faithful := by
  intro k _ _ _ _ n A _ x hx hq b hT' hX p hp
  refine abs_faith (resCard k : A) hq (fun c => hT A (iwC k n ⊤) (pw x c)) b.th b.one ?_ ?_ hX ?_ p hp
  · intro c d hc hd
    apply Subtype.ext
    have := (domMul k n ⊤ A _ (permRep A (iwC k n ⊤))).1 _ _ (dom_pw hx hc) (dom_pw hx hd)
    refine this.trans ?_
    have e : ((fun i => x ^ c i) * fun i => x ^ d i) = fun i => x ^ (c + d) i := by
      ext1 i
      simp [_root_.zpow_add]
    rw [e]
    rfl
  · intro c hc
    exact (unitHk k n A hq).2 _ (dom_pw hx hc)
  · have := satakeIndep k n A x hx
    simpa only [Hk.Bern.one, hT'] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernRel
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem group_identity_commuting {G : Type*} [Group G] (s a u v : G) (h : s⁻¹ * (a * u) * (s⁻¹ * (a * u)) = a * (a * u * v))
    (hs : Commute s a) (hv : Commute (a * u) v) : u = s * v * s := by
  rw [hv.eq, ← mul_assoc, ← mul_assoc a v] at h
  have h1 := mul_right_cancel h
  rw [← mul_assoc, hs.inv_left.eq, mul_assoc a, mul_assoc a] at h1
  have h2 := mul_left_cancel h1
  rw [← h2]; group

private theorem fund_succ {k : Type} [Field k] {n : ℕ} (x : kˣ) (l : Fin n) :
    (fun m => x ^ fund n ((l : ℕ) + 1) m) = (fun m => x ^ fund n (l : ℕ) m) * Pi.mulSingle l x := by
  funext m
  simp only [fund, Pi.mul_apply]
  by_cases h : m = l
  · subst h; simp
  · have h' : (m : ℕ) ≠ l := fun e => h (Fin.ext e)
    rw [Pi.mulSingle_eq_of_ne h, mul_one]
    congr 1
    by_cases h2 : (m : ℕ) < l
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

private theorem dom_fund {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {x : kˣ} (hx : IsUnif x) (m : ℕ) :
    Dom (fun l => x ^ fund n m l) := by
  obtain ⟨p, -, hp⟩ := hx
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  simp only [fund]
  by_cases hb : (b : ℕ) < m
  · rw [if_pos hb, if_pos (by omega)]
  · rw [if_neg hb]
    by_cases ha : (a : ℕ) < m
    · rw [if_pos ha]; simpa using h1
    · rw [if_neg ha]

theorem UpperTheory.V.AlgebraTools.bernRel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n ⊤)))ˣ, (∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (diagT k (Fin n) t)) → ∀ (i j : Fin n), (j : ℕ) = i + 1 → (θ (Pi.mulSingle i x) : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) * (θ (Pi.mulSingle j x) : Module.End A (fixd ρ (iwC k n ⊤))) * hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) ∧ ∀ l : Fin n, l ≠ i → l ≠ j → Commute (hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j))) (θ (Pi.mulSingle l x) : Module.End A (fixd ρ (iwC k n ⊤))) := by
  intro k _ _ _ _ n A M _ _ _ ρ x hx hq θ hθ i j hij
  obtain ⟨hc, y, hy1, hy2⟩ := bernDom k n A M ρ x hx i j hij
  obtain ⟨s, hs⟩ := (simpleQuad k n ⊤ A M ρ i j hij).1 hq
  rw [← hs] at hc hy1 ⊢
  set f : ℕ → Fin n → kˣ := fun m l => x ^ fund n m l with hf
  have hT : ∀ m, hk ρ (iwC k n ⊤) (pw x (fund n m)) = (θ (f m) : Module.End A (fixd ρ (iwC k n ⊤))) :=
    fun m => (hθ _ (dom_fund hx m)).symm
  have hS : ∀ l : Fin n, θ (f ((l : ℕ) + 1)) = θ (f l) * θ (Pi.mulSingle l x) := fun l => by
    rw [← map_mul]; exact congrArg θ (fund_succ x l)
  have hcm : ∀ m : ℕ, m ≠ j → Commute s (θ (f m)) := fun m hm => by
    have h := hc (f m) (dom_fund hx m) (by
      simp only [hf, fund]
      by_cases h2 : (j : ℕ) < m
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)])
    rw [← hθ _ (dom_fund hx m)] at h
    exact Commute.units_of_val h
  rw [hT] at hy1
  rw [hT, hT] at hy2
  refine ⟨?_, fun l hi hj => ?_⟩
  · have hj : θ (f j) = θ (f i) * θ (Pi.mulSingle i x) := by rw [hij]; exact hS i
    have hy : y = ((s⁻¹ * θ (f j) : (Module.End A (fixd ρ (iwC k n ⊤)))ˣ) : Module.End A (fixd ρ (iwC k n ⊤))) := by
      rw [Units.val_mul, hy1, Units.inv_mul_cancel_left]
    rw [hy, ← Units.val_mul, ← Units.val_mul] at hy2
    have h3 := Units.val_injective hy2
    rw [hS j, hj] at h3
    have h4 := group_identity_commuting s _ _ _ h3 (hcm i (by omega)) (by
      rw [← map_mul]; exact (Commute.all _ _).map θ)
    rw [h4, Units.val_mul, Units.val_mul]
  · have hi' : (l : ℕ) ≠ i := fun e => hi (Fin.ext e)
    have hj' : (l : ℕ) ≠ j := fun e => hj (Fin.ext e)
    have h1 := hcm l hj'
    have h2 := hcm ((l : ℕ) + 1) (by omega)
    have h3 : θ (Pi.mulSingle l x) = (θ (f l))⁻¹ * θ (f ((l : ℕ) + 1)) := by
      rw [hS, inv_mul_cancel_left]
    have h4 : Commute s (θ (Pi.mulSingle l x)) := by
      rw [h3]; exact h1.inv_right.mul_right h2
    exact h4.units_val
end

