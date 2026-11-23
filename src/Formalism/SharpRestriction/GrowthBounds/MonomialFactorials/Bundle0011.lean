module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen
public import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMHypOf

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiSmulRight
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem exists_fd_Ljj (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]), FiniteDimensional ℚ_[p] W ∧
      ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  have : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  have : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hsub : ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
    intro x hx
    have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
      unfold Ljj
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, g, hg, rfl⟩
      have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
      have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
        rw [← bY.span_eq] at h3
        have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact h4
      have hg2 := xi_mem_span p G (G.B - jp) g hg
      show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
      have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
          (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
          MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hmul := Submodule.mul_mem_mul hy3 hg2
      rw [Submodule.span_mul_span] at hmul
      refine Submodule.span_mono ?_ hmul
      rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨(a, ⟨m, hm⟩), rfl⟩
    exact hle hx
  exact ⟨W, FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam), hsub⟩

theorem bePhi_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (c • u) v = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [map_smul, fockK_smul_left, mul_div_assoc]

theorem bePhi_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bePhi p (r := r) G j jp (f i) v := by
  unfold bePhi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, fockK_sum_left, Finset.sum_div]

theorem bePhi_smul_right (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp u (c • v) = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [fockK_smul_right, mul_div_assoc]

theorem gcL_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bePhi p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  classical
  obtain ⟨W, hW, hsub⟩ := exists_fd_Ljj p (r := r) G j jp
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hp0 : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hli : LinearIndependent ℚ_[p] (fun i => (⟨x i, hsub _ (hx i)⟩ : W)) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : ∑ k ∈ s, g k • x k = 0 := by
      have := congrArg Subtype.val hs
      simpa using this
    have h1 := congrArg (fun u => bePhi p (r := r) G j jp u (y i)) h0
    simp only [bePhi_sum_left, bePhi_smul_left, hxy] at h1
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (fun h => absurd hi h), if_pos rfl] at h1
    have h2 : bePhi p (r := r) G j jp 0 (y i) = 0 := by
      have := bePhi_smul_left p (r := r) G j jp 0 0 (y i)
      simpa using this
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_right hp0
  have := hli.fintype_card_le_finrank
  simpa using this

theorem xiMons_spec (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c) ∧ (∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) ∧
      (∑ v ∈ m.support, m v = n) := by
  classical
  unfold xiMons at hm
  rw [Finset.mem_image] at hm
  obtain ⟨e, he, rfl⟩ := hm
  have hsum := (CountingStatementReduction.mem_Ev e).1 he
  have happ : ∀ c, (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)) (Formalism.GM.M.xiVar N r G.T.t c) = e c := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj (r := r) G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  refine ⟨fun v hv => ?_, by simp only [happ]; exact hsum, ?_⟩
  · by_contra hne
    push Not at hne
    apply Finsupp.mem_support_iff.1 hv
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hne d h.symm
  · have : (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)).sum (fun _ k => k) = ∑ c, e c := by
      rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
      exact Finset.sum_congr rfl fun d _ => Finsupp.sum_single_index rfl
    rw [← hsum, ← this]
    rfl

theorem card_xiMons_eq (n : ℕ) : (xiMons (r := r) G n).card = dXi r n := by
  classical
  unfold xiMons
  rw [Finset.card_image_of_injective]
  · rw [CountingStatementReduction.card_Ev]
    unfold dXi
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have e1 : r' + 1 + n - 1 = n + r' := by omega
    have e2 : n + (r' + 1) - 1 = n + r' := by omega
    rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]
  · intro e e' h
    funext c
    have := congrArg (fun f : Formalism.GM.M.BVar N r G.T.t →₀ ℕ => f (Formalism.GM.M.xiVar N r G.T.t c)) h
    simp only [Finsupp.finsetSum_apply] at this
    rwa [Finset.sum_eq_single c (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finset.sum_eq_single c
      (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same, Finsupp.single_eq_same] at this

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankSpanImageLe
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Dim

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem xi_span (ι : ℚ_[p] →+* KK O) {N r t b : ℕ} (g : MvPolynomial (BVar N r t) (KK O))
    (hg : g ∈ XiPolZ O N r t b) :
    g ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.XiPolZ p N r t b : Set (MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]))) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hsupp := ((mem_restrictSupport_iff _).1 hg.1) (Finset.mem_coe.2 hμ)
  have h1 : monomial μ (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r t b := by
    refine ⟨?_, ⟨monomial μ 1, by simp⟩⟩
    show monomial μ (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] _
    rw [mem_restrictSupport_iff]
    intro m hm
    have : m = μ := by
      have := support_monomial_subset hm
      simpa using this
    rw [this]
    exact hsupp
  have h2 : monomial μ (g.coeff μ) = g.coeff μ • map ι (monomial μ (1 : ℚ_[p])) := by
    rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1, rfl⟩)

theorem finrank_span_image_le (ι : ℚ_[p] →+* KK O) {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℚ_[p] V₁]
    [AddCommGroup V₂] [Module (KK O) V₂] (f : V₁ → V₂) (hadd : ∀ u v, f (u + v) = f u + f v)
    (hsm : ∀ (c : ℚ_[p]) u, f (c • u) = ι c • f u) (W : Submodule ℚ_[p] V₁) [FiniteDimensional ℚ_[p] W] :
    Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁))) ≤ Module.finrank ℚ_[p] W := by
  classical
  set bW := Module.finBasis ℚ_[p] W
  have h0 : f 0 = 0 := by
    have := hsm 0 0
    rwa [zero_smul, map_zero, zero_smul] at this
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℚ_[p] W))) (c : Fin (Module.finrank ℚ_[p] W) → ℚ_[p]),
      f (∑ i ∈ s, c i • (bW i : V₁)) = ∑ i ∈ s, ι (c i) • f (bW i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]
  have hle : Submodule.span (KK O) (f '' (W : Set V₁)) ≤
      Submodule.span (KK O) (Set.range fun i => f (bW i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (⟨w, hw⟩ : W) = ∑ i, (bW.repr ⟨w, hw⟩ i) • bW i := (bW.sum_repr _).symm
    have hw'' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V₁) := by
      have h3 := congrArg (Submodule.subtype W) hw'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h3
      simpa only [Submodule.subtype_apply, map_smul] using h3
    rw [hw'', hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  calc Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁)))
      ≤ Module.finrank (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℚ_[p] W)) := finrank_range_le_card _
    _ = Module.finrank ℚ_[p] W := Fintype.card_fin _

theorem finrank_biSup_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (U : ι → Submodule K V)
    (s : Finset ι) (hU : ∀ i ∈ s, FiniteDimensional K (U i)) :
    FiniteDimensional K (⨆ i ∈ s, U i : Submodule K V) ∧
      Module.finrank K (⨆ i ∈ s, U i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), U i) = (⊥ : Submodule K V) by simp]
    exact ⟨inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have ha' := hU a (Finset.mem_insert_self a s)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left h2 _)

end Dim

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDecompProved
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G

def cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) : MvPolynomial σ L :=
  ∑ m ∈ y.support, monomial m (f (y.coeff m))

def RestFunY : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (f : KK O →+ ℚ_[p]),
    (∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x) →
    ∀ y ∈ Yjt (KK O) (r := r) LL J M, cmap f y ∈ Formalism.GM.M.Y p (r := r) (Formalism.MainNotions.G.SymmetricFormBlocks.gmL LL) J M

def RestDecomp : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (σ : Type)
    (y : MvPolynomial σ (KK O)),
    ∃ (n : ℕ) (b : Fin n → KK O) (f : Fin n → (KK O →+ ℚ_[p])),
      (∀ k (a : ℚ_[p]) (x : KK O), f k (ι a * x) = a * f k x) ∧
      y = ∑ k, b k • map ι (cmap (f k) y)

def RestClear : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Formalism.GM.M.Letters N) (q : ℕ) (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ), ∀ F ∈ Formalism.GM.M.Y p (r := r) LL J M,
      ∃ e : ℕ, ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.YZ p (r := r) LL J M

theorem restClear_proved : RestClear := by
  intro p _ N r _ LL q J M F hF
  classical
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ m, ‖(p : ℚ_[p]) ^ e * F.coeff m‖ ≤ 1 := by
    set B : ℝ := ∑ m ∈ F.support, ‖F.coeff m‖ with hB
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B hp1
    refine ⟨e, fun m => ?_⟩
    rw [norm_mul, Padic.norm_p_pow]
    have hcm : ‖F.coeff m‖ ≤ B := by
      by_cases hm : m ∈ F.support
      · exact Finset.single_le_sum (f := fun m => ‖F.coeff m‖) (fun _ _ => norm_nonneg _) hm
      · rw [MvPolynomial.notMem_support_iff.1 hm, norm_zero]
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hp0 : (0 : ℝ) < (p : ℝ) ^ e := by positivity
    rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hp0, mul_one]
    linarith
  refine ⟨e, ?_⟩
  have hY : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Y p (r := r) LL J M := Submodule.smul_mem _ _ hF
  have hPol : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Pol p r LL := (Submodule.mem_inf.1 hY).1
  have hInt : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := by
    have hr : ((p : ℚ_[p]) ^ e) • F ∈ Set.range (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨m, -, rfl⟩ : ∃ m ∈ (((p : ℚ_[p]) ^ e) • F).support, c = (((p : ℚ_[p]) ^ e) • F).coeff m := by
        simpa [MvPolynomial.coeffs, eq_comm] using hc
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact ⟨⟨_, he m⟩, rfl⟩
    obtain ⟨G, hG⟩ := hr
    exact ⟨G, hG⟩
  exact Submodule.mem_inf.2 ⟨hY, Submodule.mem_inf.2 ⟨hPol, hInt⟩⟩

theorem restYbc_of (hF : RestFunY) (hD : RestDecomp) (hC : RestClear) : RestYbc := by
  intro O _ _ p _ ι N r _ LL q J M y hy
  have hyK : y ∈ Yjt (KK O) (r := r) LL J M := hy.1
  obtain ⟨n, b, f, hf, hdec⟩ := hD O p ι _ y
  rw [hdec]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have h1 := hF O p ι N r LL q J M (f k) (hf k) y hyK
  obtain ⟨e, he⟩ := hC p N r (gmL LL) q J M _ h1
  have hp0 : ((p : ℚ_[p]) ^ e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have e1 : map ι (cmap (f k) y) = (ι ((p : ℚ_[p]) ^ e))⁻¹ • map ι (((p : ℚ_[p]) ^ e) • cmap (f k) y) := by
    rw [MvPolynomial.smul_eq_C_mul (a := (ι ((p : ℚ_[p]) ^ e))⁻¹), MvPolynomial.smul_eq_C_mul (a := (p : ℚ_[p]) ^ e), map_mul,
      map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ((map_ne_zero ι).2 hp0), C_1, one_mul]
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, he, rfl⟩)

theorem coeff_cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (cmap f y) m = f (y.coeff m) := by
  classical
  unfold cmap
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem restDecomp_proved : RestDecomp := by
  intro O _ _ p _ ι σ y
  classical
  letI : Algebra ℚ_[p] (KK O) := ι.toAlgebra
  let V : Submodule ℚ_[p] (KK O) := Submodule.span ℚ_[p] (y.coeffs : Set (KK O))
  let bV := Module.finBasis ℚ_[p] V
  obtain ⟨rV, hrV⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  refine ⟨Module.finrank ℚ_[p] V, fun k => (bV k : KK O),
    fun k => ((bV.coord k).comp rV).toAddMonoidHom, ?_, ?_⟩
  · intro k a x
    have hx : ι a * x = a • x := by rw [Algebra.smul_def]; rfl
    show ((bV.coord k).comp rV) (ι a * x) = a * ((bV.coord k).comp rV) x
    rw [hx, map_smul, smul_eq_mul]
  · ext m
    have hc : y.coeff m ∈ V := by
      by_cases h0 : y.coeff m = 0
      · rw [h0]; exact V.zero_mem
      · exact Submodule.subset_span (MvPolynomial.coeff_mem_coeffs _ h0)
    have hrc : rV (y.coeff m) = ⟨y.coeff m, hc⟩ := by
      have := LinearMap.congr_fun hrV ⟨y.coeff m, hc⟩
      simpa using this
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_cmap, smul_eq_mul]
    have hsum := congrArg Subtype.val (bV.sum_repr ⟨y.coeff m, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    conv_lhs => rw [← hsum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show (bV.repr ⟨y.coeff m, hc⟩ k) • (bV k : KK O) = (bV k : KK O) * ι ((bV.coord k) (rV (y.coeff m)))
    rw [hrc, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
    rfl

theorem restYbc_of_funY (hF : RestFunY) : RestYbc := restYbc_of hF restDecomp_proved restClear_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMExists
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem restTM_of (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM) (hF : RestFree C0 CE1 CE2 X)
    (hS : RestTMSize C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) : RestTM C0 CE1 CE2 X 1 :=
  restTM_of_rests D hM hF (restTMHyp_of hH hS) hE

theorem restTM_exists : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestFree C0 CE1 CE2 X → RestTMSize C0 CE1 CE2 X →
      RestTMEps C0 CE1 CE2 X CM → RestTM C0 CE1 CE2 X CM := by
  exact ⟨1, le_rfl, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF hS hE =>
    restTM_of C0 CE1 CE2 X hH D (alternative_mean_value_theorem D) hF hS hE⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

