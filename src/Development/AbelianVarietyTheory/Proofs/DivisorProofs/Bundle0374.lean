module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthRestrictColumns
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem coeff_subst_extend_zero {σ τ : Type} [Finite σ] {j : τ → σ} (hj : Function.Injective j)
    (g : MvPowerSeries σ C) (α : τ →₀ ℕ) :
    coeff α (subst (Function.extend j (X : τ → MvPowerSeries τ C) 0) g) =
      coeff (Finsupp.mapDomain j α) g := by
  classical
  have hc : ∀ s, constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro s
    rw [Function.extend_def]
    split_ifs <;> simp
  have ha := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha, finsum_eq_single _ (Finsupp.mapDomain j α)]
  · rw [Finsupp.prod_mapDomain_index_inj hj]
    simp only [hj.extend_apply]
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro D hD
    by_cases hsupp : ↑D.support ⊆ Set.range j
    · obtain ⟨β, rfl⟩ : ∃ β, Finsupp.mapDomain j β = D :=
        ⟨_, Finsupp.mapDomain_comapDomain j hj D hsupp⟩
      rw [Finsupp.prod_mapDomain_index_inj hj]
      simp only [hj.extend_apply]
      rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne, smul_zero]
      rintro rfl
      exact hD rfl
    · obtain ⟨s, hs, hsr⟩ := Set.not_subset.mp hsupp
      have hz : Function.extend j (X : τ → MvPowerSeries τ C) 0 s = 0 :=
        Function.extend_apply' _ _ _ (fun h => hsr h)
      have hs' : D s ≠ 0 := Finsupp.mem_support_iff.mp hs
      rw [Finsupp.prod, Finset.prod_eq_zero hs (by simp [hz, hs']), map_zero, smul_zero]

theorem subst_zero_of_constantCoeff {σ τ : Type} [Finite σ] (h : MvPowerSeries σ C)
    (h0 : constantCoeff h = 0) : subst (0 : σ → MvPowerSeries τ C) h = 0 := by
  exact subst_zero_of_constantCoeff_zero h0

theorem subst_sum_smul_X {σ τ ι : Type} [Fintype ι] {s : σ → MvPowerSeries τ C} (hs : HasSubst s)
    (c : ι → C) (k : ι → σ) :
    subst s (∑ a, c a • (X (k a) : MvPowerSeries σ C)) = ∑ a, c a • s (k a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hs, map_sum]
  simp only [map_smul, substAlgHom_X]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)}

theorem constantCoeff_expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (x : Σ b, Fin (d b)) :
    constantCoeff (expAlong G u x) = 0 := by
  have hE := (_root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v (d x.1) (G x.1)).1
  unfold IsExp at hE
  simp only [expAlong]
  refine constantCoeff_subst_eq_zero ?_ ?_ (hE.1 x.2)
  · exact hasSubst_of_constantCoeff_zero (fun e => by simp [MvPowerSeries.smul_eq_C_mul])
  · intro e
    simp [MvPowerSeries.smul_eq_C_mul]

theorem depth_rename (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ)
    (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ)
    (P : MvPolynomial (Σ b : κ', ι (e b)) C) :
    depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) =
      depth (fun b => G (e b)) (fun b => u (e b)) P := by
  have hinj : ∀ (β : κ → Type),
      Function.Injective (fun x : (Σ b : κ', β (e b)) => (⟨e x.1, x.2⟩ : Σ b, β b)) := by
    intro β
    rintro ⟨a, x⟩ ⟨c, y⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := e.injective h1
    rw [heq_eq_eq] at h2
    rw [h2]
  have hjt : Function.Injective (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) := hinj ι
  have hjv : Function.Injective (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) := hinj (fun b => Fin (d b))
  have hcc : ∀ {σ τ : Type} (j : τ → σ) (s : σ),
      constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro σ τ j s
    classical
    rw [Function.extend_def]
    split_ifs <;> simp
  have hE : ∀ b (k : Fin (d b)), constantCoeff (expOf (G b) k) = 0 := by
    intro b k
    have h := (_root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v (d b) (G b)).1
    unfold IsExp at h
    exact h.1 k
  have hA : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have hA' : HasSubst (expAlong (fun b => G (e b)) (fun b => u (e b))) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_expAlong _ _)
  have hRt : HasSubst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hRv : HasSubst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hin : ∀ b, HasSubst (fun e' : Fin (d b) =>
      ∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b =>
    hasSubst_of_constantCoeff_zero (fun e' => by simp [MvPowerSeries.smul_eq_C_mul])

  have K1 : ∀ F : MvPowerSeries (Σ b, ι b) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) F =
        derivAt0 P (subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) F) := by
    intro F
    unfold derivAt0
    rw [MvPolynomial.support_rename_of_injective hjt,
      Finset.sum_image (Finsupp.mapDomain_injective hjt).injOn]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hm : (mfact (Finsupp.mapDomain (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) α) : C) = mfact α := by
      unfold mfact
      exact Finsupp.prod_mapDomain_index_inj hjt
    rw [MvPolynomial.coeff_rename_mapDomain _ hjt, coeff_subst_extend_zero hjt, hm]

  have K2 : ∀ x : Σ b, Fin (d b),
      subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) (expAlong G u x) =
        subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 x) := by
    rintro ⟨b, k⟩
    by_cases hb : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := hb
      have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨e b', k⟩ = X ⟨b', k⟩ := hjv.extend_apply _ _ ⟨b', k⟩
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨e b', a⟩ = X ⟨b', a⟩ :=
        fun a => hjt.extend_apply _ _ ⟨b', a⟩
      rw [h1, subst_X hA']
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin (e b')) hRt]
      congr 1
      funext e'
      rw [subst_sum_smul_X hRt]
      simp only [h2]
    · have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨b, k⟩ = 0 :=
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', k'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨b, a⟩ = 0 := fun a =>
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', a'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      rw [h1, ← coe_substAlgHom hA', map_zero]
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin b) hRt]
      have h3 : (fun e' : Fin (d b) => subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0)
          (∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C))) = 0 := by
        funext e'
        rw [subst_sum_smul_X hRt]
        simp [h2]
      rw [h3]
      exact subst_zero_of_constantCoeff _ (hE b k)
  have K : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) (subst (expAlong G u) f) =
        derivAt0 P (subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f)) := by
    intro f
    rw [K1, subst_comp_subst_apply hA hRt, subst_comp_subst_apply hRv hA']
    exact congrArg (fun F => derivAt0 P (subst F f)) (funext K2)

  have Rint : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C, MvIsInt v f →
      MvIsInt v (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f) := by
    intro f hf α
    rw [coeff_subst_extend_zero hjv]
    exact hf _
  have Rsec : ∀ g : MvPowerSeries (Σ b : κ', Fin (d (e b))) C, MvIsInt v g →
      ∃ f, MvIsInt v f ∧ subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f = g := by
    intro g hg
    classical
    refine ⟨@id (MvPowerSeries (Σ b, Fin (d b)) C)
      (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0), ?_, ?_⟩
    · intro β
      show IsIntV v (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0 β)
      rw [Function.extend_def]
      split_ifs with h
      · exact hg _
      · simp [IsIntV]
    · ext α
      rw [coeff_subst_extend_zero hjv]
      exact (Finsupp.mapDomain_injective hjv).extend_apply _ _ α
  unfold depth
  apply le_antisymm
  · refine le_iInf fun g => ?_
    obtain ⟨f, hf, hfg⟩ := Rsec g.1 g.2
    refine (iInf_le _ ⟨f, hf⟩).trans_eq ?_
    dsimp only
    rw [K f, hfg]
  · refine le_iInf fun f => ?_
    refine (iInf_le _ ⟨subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f.1, Rint f.1 f.2⟩).trans_eq ?_
    dsimp only
    rw [K f.1]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem depth_restrict : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  intro C _ _ v κ _ _ d G ι _ _ u κ' _ _ e P
  exact depth_rename κ d G ι u κ' e P

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBounds
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowContent

theorem rpow_digitSum_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (p : ℝ) ^ ((((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1)) ≤ (n : ℝ) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdig : ∀ d : ℕ, d < p → (p : ℝ) ^ ((d : ℝ) / ((p : ℝ) - 1)) ≤ (d : ℝ) + 1 := by
    intro d hd
    have hd' : (d : ℝ) ≤ (p : ℝ) - 1 := by
      have h1 : d + 1 ≤ p := hd
      have h2 : (d : ℝ) + 1 ≤ p := by exact_mod_cast h1
      linarith
    have ht0 : 0 ≤ (d : ℝ) / ((p : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hpos.le
    have ht1 : (d : ℝ) / ((p : ℝ) - 1) ≤ 1 := (div_le_one hpos).mpr hd'
    have h := Real.geom_mean_le_arith_mean2_weighted ht0 (sub_nonneg.mpr ht1)
      (by linarith : (0 : ℝ) ≤ p) zero_le_one (add_sub_cancel _ _)
    rw [Real.one_rpow, mul_one] at h
    have e : (d : ℝ) / ((p : ℝ) - 1) * p + (1 - (d : ℝ) / ((p : ℝ) - 1)) * 1 = (d : ℝ) + 1 := by
      field_simp
      ring
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' (by omega) hn, List.sum_cons, Nat.cast_add, add_div,
        Real.rpow_add (by linarith)]
      have h1 := ih (n / p) (Nat.div_lt_self hn (by omega))
      have h2 := hdig (n % p) (Nat.mod_lt _ (by omega))
      have hmod : ((n % p : ℕ) : ℝ) + (p : ℝ) * ((n / p : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mod_add_div n p
      have hlt : ((n % p : ℕ) : ℝ) + 1 ≤ p := by
        exact_mod_cast (Nat.mod_lt n (by omega : 0 < p))
      have hm0 : (0 : ℝ) ≤ ((n / p : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (p : ℝ) ^ (((n % p : ℕ) : ℝ) / ((p : ℝ) - 1)) *
            (p : ℝ) ^ ((((Nat.digits p (n / p)).sum : ℕ) : ℝ) / ((p : ℝ) - 1))
          ≤ (((n % p : ℕ) : ℝ) + 1) * (((n / p : ℕ) : ℝ) + 1) :=
            mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith) _) (by positivity)
        _ ≤ (n : ℝ) + 1 := by nlinarith

theorem digitSum_le_logb (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((n : ℝ) + 1) :=
    (Real.le_logb_iff_rpow_le hp1 (by positivity)).mpr (rpow_digitSum_le p hp n)
  rw [div_le_iff₀ hpos] at h2
  linarith [mul_comm (Real.logb p ((n : ℝ) + 1)) ((p : ℝ) - 1)]

theorem padicValNat_factorial_ge (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (N : ℝ) / ((p : ℝ) - 1) - Real.logb p ((N : ℝ) + 1) ≤ (padicValNat p N.factorial : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h := digitSum_le_logb p hp.two_le N
  have h3 : (((Nat.digits p N).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((N : ℝ) + 1) := by
    rw [div_le_iff₀ hpos]
    linarith [mul_comm (Real.logb p ((N : ℝ) + 1)) ((p : ℝ) - 1)]
  rw [GlobalTheory.LegendreBounds.legendre_real p hp N, sub_div]
  linarith

theorem toE_coe (r : ℝ) : toE (r : WithTop ℝ) = (r : EReal) := rfl

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := by
  unfold toE
  exact WithBot.coe_le_coe.mpr h

theorem val_mfact {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) = 1) {σ : Type} [Fintype σ] (α : σ →₀ ℕ) :
    v (mfact α : C) = ((∑ k, (padicValNat p (α k).factorial : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hne : (∏ k, (α k).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.factorial_ne_zero _)
  have e : (mfact α : C) = ((∏ k, (α k).factorial : ℕ) : C) := by
    unfold mfact
    rw [Finsupp.prod_fintype _ _ (fun k => by simp), Nat.cast_prod]
  rw [e, ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hp hv hne, Nat.factorization_def _ hp, ← Nat.padicValNat_def,
    GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp Finset.univ α]

theorem content_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  intro C _ _ v p hp hv i c
  classical
  obtain ⟨-, hint, hdiag, hrows⟩ := _root_.GlobalTheory.DetPowShape.detPow_shape C i c
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : ∀ α ∈ (detPow C i c).support,
      (∑ k, ((α k : ℕ) : ℝ)) = (i : ℝ) * c ∧ ∀ k, α k ≤ c := by
    intro α hα
    obtain ⟨-, hb⟩ := hrows α hα
    refine ⟨?_, ?_⟩
    · rw [Fintype.sum_sigma]
      have hb' : ∀ b : Fin i, (∑ a : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := by
        intro b
        exact_mod_cast hb b
      simp only [hb', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rintro ⟨b, a⟩
      rw [← hb b]
      exact Finset.single_le_sum (f := fun a' => α ⟨b, a'⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
  have upS : ∀ α ∈ (detPow C i c).support,
      (∑ k, (padicValNat p (α k).factorial : ℝ)) ≤ (i * c : ℝ) / (p - 1) := by
    intro α hα
    calc (∑ k, (padicValNat p (α k).factorial : ℝ))
        ≤ ∑ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_le_sum (fun k _ => GlobalTheory.LegendreBounds.upper p hp (α k))
      _ = (i * c : ℝ) / (p - 1) := by rw [← Finset.sum_div, (key α hα).1]
  have loS : ∀ α ∈ (detPow C i c).support,
      (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := by
    intro α hα
    obtain ⟨hsum, hle⟩ := key α hα
    have h1 : ∀ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)
        ≤ (padicValNat p (α k).factorial : ℝ) := by
      intro k
      have hl : Real.logb p (((α k : ℕ) : ℝ) + 1) ≤ Real.logb p ((c : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by exact_mod_cast Nat.add_le_add_right (hle k) 1)
      have := padicValNat_factorial_ge p hp (α k)
      linarith
    calc (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        = ∑ k, (((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sigma, Fintype.card_fin,
            smul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := Finset.sum_le_sum (fun k _ => h1 k)
  constructor
  · set α0 : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα0
    have hmem : α0 ∈ (detPow C i c).support := by
      rw [MvPolynomial.mem_support_iff, hdiag]
      exact one_ne_zero
    calc content v (detPow C i c) ≤ toE (v ((detPow C i c).coeff α0 * mfact α0)) := by
          unfold content
          exact iInf₂_le α0 hmem
      _ = (((∑ k, (padicValNat p (α0 k).factorial : ℝ)) : ℝ) : EReal) := by
          rw [hdiag, one_mul, val_mfact v hp hv α0, toE_coe]
      _ ≤ _ := EReal.coe_le_coe_iff.mpr (upS α0 hmem)
  · unfold content
    refine le_iInf₂ (fun α hα => ?_)
    obtain ⟨n, hn⟩ := hint α
    rw [← toE_coe]
    apply toE_mono
    rw [AddValuation.map_mul, val_mfact v hp hv α, hn]
    exact le_trans (WithTop.coe_le_coe.mpr (loS α hα))
      (le_add_of_nonneg_left (ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v n))

end GlobalTheory.DetPowContent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

open GlobalTheory.EtC.LerayOne in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (x : H R (sch.obj X) F 1),
      pull R (sch.map f) F 1 x = 0 →
        ∃ s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F,
          cobd (R := R) (E := cech f) (n := 1) s = 0 ∧
            IsCls (R := R) s (pull R (cechAug f) F 1 x) := by
  intro R _ F Y X f x hx
  obtain ⟨-, hneg, hmono, ⟨w0, hex⟩, -, -⟩ := _root_.GlobalTheory.EtC.res_basic R F
  obtain ⟨z, hz⟩ := (pull R (cechAug f) F 1 x).mk_surjective
  have h0 : pull R (diag f) F 1 (CohomologyClass.mk z) = 0 := by
    rw [hz, ← pull_comp, diag_aug, hx]
  have h0' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (diag f))) z (zero_add 1)) = 0 := h0
  rw [CohomologyClass.mk_eq_zero_iff] at h0'
  obtain ⟨m, hm, w, hw⟩ := h0'
  obtain rfl : m = 0 := by omega

  have hw01 : ((chains R).map (diag f)).f 0 ≫ z.1.v 0 1 (zero_add 1) =
      w.v 0 0 (add_zero 0) ≫ (res R F).d 0 1 := by
    have := Cochain.congr_v hw 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) w 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (sch.obj Y) 1 one_pos).eq_of_tgt (((chains R).obj (sch.obj Y)).d 0 1) 0,
      zero_comp, smul_zero, add_zero] at this
    rw [this]
    change _ = ((Cochain.ofHom ((chains R).map (diag f))).comp z.1 (zero_add 1)).v 0 1 (zero_add 1)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have cm0 : (chainsXIso R (sch.obj Y) 0).inv ≫ ((chains R).map (diag f)).f 0 =
      (free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv := CupSpec.chains_map (diag f) 0
  let r : (cech f).obj (op ⦋0⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) := WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0
  have hr : r ≫ (diag f).app (op ⦋0⦌) = 𝟙 _ := diag_zero f
  let y0 : (free R).obj ((cech f).obj (op ⦋0⦌)) ⟶ (res R F).X 0 :=
    (free R).map r ≫ (chainsXIso R (sch.obj Y) 0).inv ≫ w.v 0 0 (add_zero 0)
  have hA0 : (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1) = y0 ≫ (res R F).d 0 1 := by
    calc (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1)
        = (free R).map r ≫ ((free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv) ≫
            z.1.v 0 1 (zero_add 1) := by
          rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hr, CategoryTheory.Functor.map_id, Category.id_comp]
      _ = y0 ≫ (res R F).d 0 1 := by
          rw [← cm0, Category.assoc, hw01]
          simp only [y0, Category.assoc]
  let c : Cochain ((chains R).obj (cech f)) (res R F) 0 :=
    Cochain.single (p := 0) (q := 0) ((chainsXIso R (cech f) 0).hom ≫ y0) 0
  let b : Cocycle ((chains R).obj (cech f)) (res R F) 1 := Cocycle.mk (δ 0 1 c) 2 (by norm_num) (δ_δ 0 1 2 c)
  have hb : CohomologyClass.mk b = 0 := (CohomologyClass.mk_eq_zero_iff b).2 ⟨0, zero_add 1, c, rfl⟩
  let ζ := z - b
  have hζ : CohomologyClass.mk ζ = pull R (cechAug f) F 1 x := by
    rw [CohomologyClass.mk_sub, hb, sub_zero, hz]
  have hζv : ∀ p q hpq, ζ.1.v p q hpq = z.1.v p q hpq - (δ 0 1 c).v p q hpq := fun p q hpq => by
    simp only [ζ, b, Cocycle.coe_sub, Cochain.sub_v]
    rfl
  have hζ01 : ζ.1.v 0 1 (zero_add 1) = 0 := by
    rw [hζv, δ_v 0 1 (zero_add 1) c 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (cech f) 1 one_pos).eq_of_tgt (((chains R).obj (cech f)).d 0 1) 0,
      zero_comp, smul_zero, add_zero, Cochain.single_v]
    rw [← cancel_epi (chainsXIso R (cech f) 0).inv, Preadditive.comp_sub, hA0, comp_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, sub_self]
  have hδζ : δ 1 2 ζ.1 = 0 := Cocycle.δ_eq_zero ζ 2
  have hB : ζ.1.v (-1) 0 (by norm_num) ≫ (res R F).d 0 1 = 0 := by
    have := Cochain.congr_v hδζ (-1) 1 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-1) 1 (by norm_num) 0 0 (by norm_num) (by norm_num), hζ01, comp_zero,
      smul_zero, add_zero, Cochain.zero_v] at this
    exact this
  let B : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ (res R F).X 0 :=
    (chainsXIso R (cech f) 1).inv ≫ ζ.1.v (-1) 0 (by norm_num)
  have hBd : B ≫ (res R F).d 0 1 = 0 := by simp only [B, Category.assoc, hB, comp_zero]
  let s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F := hex.lift B hBd
  have hs : s ≫ resι R F = B := hex.lift_f B hBd
  refine ⟨s, ?_, ζ, hζ, ?_⟩
  · have h20 := Cochain.congr_v hδζ (-2) 0 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-2) 0 (by norm_num) (-1) (-1) (by norm_num) (by norm_num),
      (hneg (-1) (by norm_num)).eq_of_tgt (ζ.1.v (-2) (-1) (by norm_num)) 0, zero_comp, zero_add, Cochain.zero_v] at h20
    have h2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
    rw [h2, one_smul] at h20
    have hd : (chainsXIso R (cech f) 2).inv ≫ ((chains R).obj (cech f)).d (-2) (-1) =
        (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (free R).map ((cech f).δ i)) ≫ (chainsXIso R (cech f) 1).inv :=
      CupSpec.chains_d (cech f) 1
    have h3 := congrArg ((chainsXIso R (cech f) 2).inv ≫ ·) h20
    simp only [comp_zero] at h3
    rw [← Category.assoc, hd, Category.assoc] at h3
    apply (cancel_mono (resι R F)).1
    rw [zero_comp, cobd, Preadditive.sum_comp]
    rw [Preadditive.sum_comp] at h3
    refine Eq.trans ?_ h3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Preadditive.zsmul_comp, Category.assoc, hs, B]
  · apply Cochain.ext
    intro p q hpq
    by_cases hp1 : p = -((1 : ℕ) : ℤ)
    · subst hp1
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hs]
      change _ = (chainsXIso R (cech f) 1).hom ≫ (chainsXIso R (cech f) 1).inv ≫ ζ.1.v _ 0 hpq
      rw [Iso.hom_inv_id_assoc]
    · rw [Cochain.single_v_eq_zero _ _ _ _ _ hp1]
      by_cases hp0 : p = 0
      · subst hp0
        obtain rfl : q = 1 := by omega
        exact hζ01
      · by_cases hpos : 0 < p
        · exact (CupSpec.isZero_chains (cech f) p hpos).eq_of_src _ _
        · exact (hneg q (by omega)).eq_of_tgt _ _
end

