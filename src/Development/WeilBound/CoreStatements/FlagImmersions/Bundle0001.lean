module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Formalism.DegreeFormula.FlagDegFormula
public import Development.WeilBound.CoreStatements.FlagImmersions.MapProdLinear

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.DegFlSymmetryInvariance
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_relabel_injective {Ψ : Type} {N : ℕ} (σ : Equiv.Perm Ψ) :
    Function.Injective (fun x : Ψ × Fin N => (σ x.1, x.2)) := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (σ.injective hxy.1) hxy.2

theorem pa_degFl_relabel {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (σ : Equiv.Perm Ψ) (F : RP Ψ N) :
    degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F := by
  have hinj := pa_relabel_injective (N := N) σ
  have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
      Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (permExp (fun t => ρ (σ t))) := by
    intro ρ
    ext ⟨t, i⟩
    have ht : ((t, i) : Ψ × Fin N) = (fun x : Ψ × Fin N => (σ x.1, x.2)) (σ.symm t, i) := by simp
    rw [ht, Finsupp.mapDomain_apply_of_injective hinj]
    simp [permExp]
  unfold degFl
  congr 1
  have hterm : ∀ ρ : Ψ → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) *
          (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F).coeff (permExp ρ) =
        (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
          (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ')) (fun t => ρ (σ t)) := by
    intro ρ
    rw [hexp ρ, coeff_rename_mapDomain _ hinj]
    congr 1
    exact (Equiv.prod_comp σ (fun τ => ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ))).symm
  rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ)]
  exact Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Equiv.Perm (Fin N))))
    (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
      (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ'))

theorem degFl_symmetry_invariance : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F := by
  intro Ψ _ _ N
  refine ⟨?_, ?_⟩
  · intro τ a b F hab
    have hinv : ∀ x : Ψ × Fin N,
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          ((fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) x) = x := by
      rintro ⟨t, i⟩
      by_cases ht : t = τ <;> simp [ht]
    have hinj : Function.Injective
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) := by
      intro x y hxy
      exact (hinv x).symm.trans ((congrArg
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) hxy).trans (hinv y))
    have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
        Finsupp.mapDomain (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          (permExp (ρ * Pi.mulSingle τ (Equiv.swap a b))) := by
      intro ρ
      ext y
      conv_rhs => rw [← hinv y]
      rw [Finsupp.mapDomain_apply_of_injective hinj]
      rcases y with ⟨t, i⟩
      by_cases ht : t = τ
      · subst ht
        simp [permExp]
      · simp [permExp, ht, Pi.mulSingle_apply]
    have hsgn : ∀ ρ : Ψ → Equiv.Perm (Fin N),
        (∏ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ)) =
          -∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) := by
      intro ρ
      have hfac : ∀ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) =
          ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * (if t = τ then -1 else 1) := by
        intro t
        by_cases ht : t = τ
        · subst ht
          simp [Equiv.Perm.sign_swap hab]
        · simp [ht]
      rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib]
      simp
    unfold degFl
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulRight (Pi.mulSingle τ (Equiv.swap a b)))
      (fun ρ => -((∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ)) * F.coeff (permExp ρ)))]
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [Equiv.coe_mulRight]
    rw [hexp ρ, coeff_rename_mapDomain _ hinj, hsgn ρ]
    ring
  · intro σ F
    have hinj := pa_relabel_injective (N := N) σ
    refine ⟨pa_degFl_relabel σ F, fun j τ => ⟨?_, ?_⟩⟩
    · unfold Sh
      conv_rhs => rw [← pa_degFl_relabel σ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F
    · unfold Tot
      conv_rhs => rw [← pa_degFl_relabel σ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.DegLApply
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.Lin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def degL (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : RP Ψ N →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ dimFl Ψ N) •
    ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (permExp σ)

theorem degL_apply (F : RP Ψ N) : degL Ψ N F = degFl F := by
  simp only [degL, degFl, LinearMap.smul_apply, LinearMap.sum_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]

def shL (j : ℕ) (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
    (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem shL_apply (j : ℕ) (τ : Ψ) (F : RP Ψ N) : shL j τ F = Sh j τ F := by
  rw [shL, LinearMap.comp_apply, degL_apply, Sh]
  congr 1
  simp

def totL (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i : Fin N, (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem totL_apply (τ : Ψ) (F : RP Ψ N) : totL τ F = Tot τ F := by
  rw [totL, LinearMap.comp_apply, degL_apply, Tot]
  congr 1
  simp

end RootFieldNumerics.Lin
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ExistsDegreeOneClass
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.L3

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem permExp_apply (σ : Ψ → Equiv.Perm (Fin N)) (x : Ψ × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  simp [permExp]

theorem permExp_injective :
    Function.Injective (permExp : (Ψ → Equiv.Perm (Fin N)) → (Ψ × Fin N) →₀ ℕ) := by
  intro σ σ' h
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, i)
  rw [permExp_apply, permExp_apply] at h1
  have h2 := (σ τ i).2
  have h3 := (σ' τ i).2
  dsimp only at h1
  omega

theorem degree_permExp_one :
    (permExp (1 : Ψ → Equiv.Perm (Fin N))).degree = dimFl Ψ N := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [permExp_apply, Pi.one_apply, Equiv.Perm.one_apply]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl,
    Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]

theorem degFl_monomial_one [DecidableEq Ψ] :
    degFl (monomial (permExp (1 : Ψ → Equiv.Perm (Fin N))) ((-1 : ℝ) ^ dimFl Ψ N)) = 1 := by
  unfold degFl
  rw [Finset.sum_eq_single (1 : Ψ → Equiv.Perm (Fin N))]
  · simp [← mul_pow]
  · intro σ _ hσ
    rw [coeff_monomial, if_neg (fun h => hσ (permExp_injective h).symm), mul_zero]
  · simp

end RootFieldNumerics.L3

theorem RootFieldNumerics.exists_degree_one_class : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  intro Ψ _ _ N j τ h1 hj
  refine ⟨⟨_, isHomogeneous_monomial _ RootFieldNumerics.L3.degree_permExp_one, RootFieldNumerics.L3.degFl_monomial_one⟩, ?_⟩
  let i0 : Fin N := ⟨j - 1, by omega⟩
  let i1 : Fin N := ⟨j, hj⟩
  let m : (Ψ × Fin N) →₀ ℕ := permExp (1 : Ψ → Equiv.Perm (Fin N)) - Finsupp.single (τ, i0) 1
  have hm : Finsupp.single (τ, i0) 1 + m = permExp (1 : Ψ → Equiv.Perm (Fin N)) := by
    apply add_tsub_cancel_of_le
    rw [Finsupp.single_le_iff, RootFieldNumerics.L3.permExp_apply]
    simp only [Pi.one_apply, Equiv.Perm.one_apply, i0]
    omega
  have hdeg : m.degree = dimFl Ψ N - 1 := by
    rw [← RootFieldNumerics.L3.degree_permExp_one, ← hm, map_add (f := _), Finsupp.degree_single]
    omega
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp only [i0, i1] at this
    omega
  have hm0 : m (τ, i0) = N - 1 - j := by
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, Finsupp.single_eq_same, Pi.one_apply,
      Equiv.Perm.one_apply, i0]
    omega
  have hm1 : m (τ, i1) = N - 1 - j := by
    have : (Finsupp.single (τ, i0) 1 : (Ψ × Fin N) →₀ ℕ) (τ, i1) = 0 :=
      Finsupp.single_eq_of_ne' (by simpa using h01)
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, this, Pi.one_apply,
      Equiv.Perm.one_apply, i1]
    omega
  refine ⟨monomial m ((-1 : ℝ) ^ dimFl Ψ N), isHomogeneous_monomial _ hdeg, ?_⟩
  refine Eq.trans ?_ (RootFieldNumerics.L3.degFl_monomial_one (Ψ := Ψ) (N := N))
  unfold degFl
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [pkLow, Finset.sum_mul, coeff_sum, Finset.sum_eq_single i0]
  · rw [X_pow_eq_monomial, monomial_mul, one_mul, hm]
  · intro i hi hi0
    rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, if_neg]
    intro h
    have hi1 : i ≠ i1 := by
      intro h'
      rw [Finset.mem_filter, h'] at hi
      simp [i1] at hi
    have e0 := DFunLike.congr_fun h (τ, i0)
    have e1 := DFunLike.congr_fun h (τ, i1)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi0), hm0,
      RootFieldNumerics.L3.permExp_apply] at e0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi1), hm1,
      RootFieldNumerics.L3.permExp_apply] at e1
    dsimp only at e0 e1
    have h2 := (σ τ i0).2
    have h3 := (σ τ i1).2
    exact h01 ((σ τ).injective (Fin.ext (by omega)))
  · intro h
    exact absurd (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, i0]; omega) h
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.LinearRootPowerLipschitz
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.Pc

theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) (δ : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (h : ∀ i, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hB : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hb i)
    have e : a i * ∏ i ∈ s, a i - b i * ∏ i ∈ s, b i =
        a i * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a i - b i) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a i| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ 1 * (s.card * δ) :=
      mul_le_mul (ha i) ih (abs_nonneg _) zero_le_one
    have h2 : |a i - b i| * |∏ i ∈ s, b i| ≤ δ * 1 :=
      mul_le_mul (h i) hB (abs_nonneg _) ((abs_nonneg _).trans (h i))
    push_cast
    linarith

def linCoef {Ψ : Type} {N : ℕ} (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | none => s
  | some x => -lam x.1 x.2

theorem linA_eq {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (s : ℝ) :
    linA lam s = ∑ j, C (linCoef lam s j) * X j := by
  rw [Fintype.sum_option]
  simp [linA, toA, linRoot, linCoef, add_comm]

theorem map_linA_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ)
    (lam : Wt Ψ N) (s : ℝ) [Fintype (Fin d → Option (Ψ × Fin N))] :
    Φ (linA lam s ^ d) = ∑ w : Fin d → Option (Ψ × Fin N), (∏ k, linCoef lam s (w k)) *
      Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  have := RootFieldNumerics.map_prod_linear (Option (Ψ × Fin N)) d Φ (fun _ => linCoef lam s)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← linA_eq] at this
  convert this

end RootFieldNumerics.Pc

theorem RootFieldNumerics.linear_root_power_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  intro Ψ _ N d
  classical
  refine ⟨fun Φ => ?_, fun lam => by simp [linA], ?_⟩
  · simp only [RootFieldNumerics.Pc.map_linA_pow]
    refine continuous_finsetSum _ fun w _ => Continuous.mul
      (continuous_finsetProd _ fun k _ => ?_) continuous_const
    cases w k with
    | none => exact continuous_snd
    | some x =>
      simp only [RootFieldNumerics.Pc.linCoef]
      fun_prop
  · refine ⟨(Fintype.card (Fin d → Option (Ψ × Fin N)) : ℝ) * d, by positivity, ?_⟩
    intro Φ b hb lam mu s s' hl hm hs hs'
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
    have hent : ∀ (l : Wt Ψ N) τ i, |l τ i| ≤ ‖l‖ := fun l τ i =>
      (norm_le_pi_norm (l τ) i).trans (norm_le_pi_norm l τ)
    have hc : ∀ (l : Wt Ψ N) (t : ℝ), ‖l‖ ≤ 1 → |t| ≤ 1 → ∀ j, |RootFieldNumerics.Pc.linCoef l t j| ≤ 1 := by
      intro l t h1 h2 j
      cases j with
      | none => exact h2
      | some x => simpa [RootFieldNumerics.Pc.linCoef] using (hent l x.1 x.2).trans h1
    have hd : ∀ j, |RootFieldNumerics.Pc.linCoef lam s j - RootFieldNumerics.Pc.linCoef mu s' j| ≤ ‖lam - mu‖ + |s - s'| := by
      intro j
      cases j with
      | none => exact le_add_of_nonneg_left (norm_nonneg _)
      | some x =>
        have h1 := hent (lam - mu) x.1 x.2
        have e : RootFieldNumerics.Pc.linCoef lam s (some x) - RootFieldNumerics.Pc.linCoef mu s' (some x) =
            -((lam - mu) x.1 x.2) := by
          simp only [RootFieldNumerics.Pc.linCoef, Pi.sub_apply]; ring
        rw [e, abs_neg]
        exact h1.trans (le_add_of_nonneg_right (abs_nonneg _))
    rw [RootFieldNumerics.Pc.map_linA_pow, RootFieldNumerics.Pc.map_linA_pow, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (d * (‖lam - mu‖ + |s - s'|) * b) fun w _ => ?_).trans ?_
    · rw [← sub_mul, abs_mul]
      refine mul_le_mul ?_ (hb _) (abs_nonneg _) (by positivity)
      simpa using RootFieldNumerics.Pc.abs_prod_sub_prod_le Finset.univ _ _ _
        (fun k => hc lam s hl hs (w k)) (fun k => hc mu s' hm hs' (w k)) (fun k => hd (w k))
    · rw [Finset.card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.PartialSumOrderedBounds
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.partial_sum_ordered_bounds : ∀ (N j : ℕ) (u : Fin N → ℝ), j ≤ N → 0 < N → (∀ a b : Fin N, a ≤ b → u b ≤ u a) → 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ≤ ∑ i, |u i| ∧ |∑ i, u i| ≤ ∑ i, |u i| := by
  intro N j u hj hN hu
  refine ⟨?_, ?_, Finset.abs_sum_le_sum_abs _ _⟩
  all_goals
    set A := Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) with hA
    set B := Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j) with hB
    have hsplit : ∀ g : Fin N → ℝ, ∑ i, g i = ∑ i ∈ A, g i + ∑ i ∈ B, g i := fun g =>
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  · have hcA : A.card = j := by
      rw [hA, Fin.card_filter_val_lt]; omega
    have hcB : (B.card : ℝ) = N - j := by
      have := hsplit (fun _ => 1)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hcA] at this
      linarith
    have key : ∑ i ∈ A, ∑ k ∈ B, u k ≤ ∑ i ∈ A, ∑ k ∈ B, u i := by
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => hu i k ?_
      rw [hA, Finset.mem_filter] at hi
      rw [hB, Finset.mem_filter] at hk
      rw [Fin.le_def]; omega
    simp only [Finset.sum_const, nsmul_eq_mul, hcA, hcB, ← Finset.mul_sum] at key
    rw [hsplit u, sub_nonneg, ← mul_div_assoc, div_le_iff₀ hNpos]
    nlinarith
  · rw [hsplit u, hsplit (fun i => |u i|)]
    have h1 := (abs_le.mp (Finset.abs_sum_le_sum_abs u A))
    have h2 := (abs_le.mp (Finset.abs_sum_le_sum_abs u B))
    have h3 : 0 ≤ ∑ i ∈ A, |u i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h4 : 0 ≤ ∑ i ∈ B, |u i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have ht0 : 0 ≤ (j : ℝ) / N := div_nonneg hj0 hNpos.le
    have ht1 : (j : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr hjN
    have e : ∀ x : ℝ, (j : ℝ) * (x / N) = (j : ℝ) / N * x := fun x => by ring
    rw [e]
    generalize (j : ℝ) / N = t at *
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h1.2),
      mul_nonneg ht0 (sub_nonneg.mpr h2.1), mul_nonneg ht0 h3, mul_nonneg (sub_nonneg.mpr ht1) h4]
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.PolarizationCoefficientsBound
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_neg_lin_pow {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (c : J → ℝ) :
    ((-∑ x, C (c x) * X x : MvPolynomial J ℝ)) ^ d =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset J) d,
        ((-1) ^ d * (m.multinomial : ℝ) * m.prod (fun r e => c r ^ e)) • monomial m (1 : ℝ) := by
  rw [neg_pow, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  refine Finset.sum_nbij' (fun g => Finsupp.equivFunOnFinite.symm g) (fun m => ⇑m) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_piAntidiag] at hg
    simp only [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    simpa using hg.1
  · intro m hm
    simp only [Finset.mem_finsuppAntidiag] at hm
    simp only [Finset.mem_piAntidiag]
    exact ⟨hm.1, fun i _ => Finset.mem_univ i⟩
  · intro g _
    simp
  · intro m _
    simp
  · intro g _
    set m : J →₀ ℕ := Finsupp.equivFunOnFinite.symm g with hm
    have hg : g = ⇑m := by simp [hm]
    rw [hg, Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
      Finsupp.prod_fintype _ _ (by simp), monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul, map_mul, map_prod, map_pow, map_natCast,
      map_neg, map_one]
    ring

theorem polarization_coefficients_bound : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |Pl.coeff m| := by
  intro J _ _ d Φ
  set S := Finset.finsuppAntidiag (Finset.univ : Finset J) d with hSdef
  have hS : ∀ m : J →₀ ℕ, m ∈ S ↔ m.degree = d := by
    intro m
    simp [hSdef, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  set a : (J →₀ ℕ) → ℝ := fun m => (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1) with ha
  set Pl : MvPolynomial J ℝ := ∑ m ∈ S, monomial m (a m) with hPl
  have hcoeff : ∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = a m := by
    intro m hm
    rw [hPl, coeff_sum, Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, ite_eq_right hb]
    · intro hm'
      exact absurd ((hS m).2 hm) hm'
  refine ⟨Pl, ?_, ?_, hcoeff, ?_⟩
  · apply IsHomogeneous.sum
    intro m hm
    exact isHomogeneous_monomial _ ((hS m).1 hm)
  · intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pa_neg_lin_pow, hPl, map_sum (eval c), map_sum Φ]
    refine Finset.sum_congr hSdef fun m _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, ha]
    ring
  · intro m hm
    rw [hcoeff m hm, ha]
    have hpos : (1 : ℝ) ≤ (m.multinomial : ℝ) := by
      have : 0 < m.multinomial := by
        rw [Finsupp.multinomial_eq]
        exact Nat.multinomial_pos _ _
      exact_mod_cast this
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    nlinarith [abs_nonneg (Φ (monomial m 1))]

end RootFieldNumerics
end

