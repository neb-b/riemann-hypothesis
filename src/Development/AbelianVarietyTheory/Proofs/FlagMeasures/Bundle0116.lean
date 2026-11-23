module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0107

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DuWinThreeOfCount
section
open Formalism.BasicNotions GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG.DuWinThree

theorem star_pow {a G : ℝ} (ha : 0 < a) (hG : 0 < G) {n : ℕ} (hn : 0 < n) :
    (a ^ ((1 : ℝ) / n) * G ^ (-(2 : ℝ) / n)) ^ n = a / G ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← Real.rpow_natCast (a ^ _), ← Real.rpow_natCast (G ^ _), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hG.le, div_mul_cancel₀ _ hn', div_mul_cancel₀ _ hn', Real.rpow_one,
    Real.rpow_neg hG.le, div_eq_mul_inv]
  norm_num

theorem window {S T : ℝ} {f k : ℕ} (hS : 0 < S) (hT : 2 ≤ T) (hf : 1 ≤ f) (hfk : f ≤ k)
    (h1 : S ≤ T) (h2 : T ≤ (1 + 1 / ((f * k : ℕ) : ℝ)) * S) :
    S ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f ∧ (T ^ k - 1) ^ f ≤ 3 * S ^ (f * k) := by
  have hk2 : 2 * k ≤ 2 ^ k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ]; omega
  have hTk : (2 * f : ℝ) ≤ T ^ k := by
    calc (2 * f : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (by omega : 2 * f ≤ 2 ^ k)
      _ ≤ T ^ k := pow_le_pow_left₀ (by norm_num) hT k
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hP : 0 < T ^ k := by linarith
  have hpow : (T ^ k) ^ f = T ^ (f * k) := by rw [← pow_mul, mul_comm]
  constructor
  · have e : T ^ k - 1 = T ^ k * (1 + (-(1 / T ^ k))) := by field_simp; ring
    have hsm : 1 / T ^ k ≤ 1 := by rw [div_le_one hP]; linarith
    have hb := one_add_mul_le_pow (a := -(1 / T ^ k)) (by linarith) f
    have hc : (f : ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hP]; linarith
    have hd : S ^ (f * k) ≤ T ^ (f * k) := pow_le_pow_left₀ hS.le h1 _
    have hTn : 0 ≤ T ^ (f * k) := by positivity
    rw [e, mul_pow, hpow]
    calc S ^ (f * k) / 2 ≤ T ^ (f * k) * (1 / 2) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hTn
  · have hn : 0 < f * k := Nat.mul_pos hf (by omega)
    have hn' : (0 : ℝ) < ((f * k : ℕ) : ℝ) := by exact_mod_cast hn
    have he : (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) ≤ 3 := by
      have h3 : 1 + 1 / ((f * k : ℕ) : ℝ) ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) := by
        have := Real.add_one_le_exp (1 / ((f * k : ℕ) : ℝ)); linarith
      calc _ ≤ Real.exp (1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := pow_le_pow_left₀ (by positivity) h3 _
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hn'.ne']
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = T ^ (f * k) := hpow
      _ ≤ ((1 + 1 / ((f * k : ℕ) : ℝ)) * S) ^ (f * k) := pow_le_pow_left₀ (by linarith) h2 _
      _ ≤ 3 * S ^ (f * k) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right he (by positivity)

end GlobalTheory.Diag.PG.DuWinThree

namespace GlobalTheory.Diag.PG

open GlobalTheory.Diag.PG.DuWinThree

theorem duWin_three_of_count : ∀ D : D7, (∀ u, (D.duS u : ℝ) = ((D.mem u).A.duStar : ℝ) *
    (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → DuWin D 3 := by
  intro D h u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hT : 2 ≤ (D.mem u).A.T := (D.mem u).A.T_prime.two_le
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hf : 1 ≤ D.R.f := le_trans (by have := D.R.two_le_m; omega) (D.R.m_le_f : D.R.m ≤ D.R.f)
  have hn : 0 < D.R.f * D.R.k := Nat.mul_pos hf (by omega)
  have hS : 0 < (D.mem u).A.Tstar := by
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    positivity
  have hSn : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    rw [← star_pow (div_pos hD hd) hG hn, ColumnsAtT.Tstar, ColumnsAtT.Xu, Nat.cast_mul]
  obtain ⟨w1, w2⟩ := D.T_win u
  obtain ⟨a, b⟩ := window hS (by exact_mod_cast hT) hf hfk w1 (by rw [Nat.cast_mul]; exact w2)
  rw [hSn] at a b
  rw [h u, ← D.Dstar_eq u]
  set X := (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
  have hG2 : (D.mem u).A.GamP ^ (-2 : ℤ) = 1 / (D.mem u).A.GamP ^ 2 := by
    rw [zpow_neg, one_div]; norm_cast
  rw [hG2]
  set c := (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have e : 1 / (D.mem u).A.GamP ^ 2 * (D.mem u).A.Dstar = ((D.mem u).A.duStar : ℝ) * c := by
    rw [hcdef]; field_simp
  rw [e]
  constructor
  · have := mul_le_mul_of_nonneg_left a hd.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left b hd.le
    nlinarith

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegral
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagCoef

theorem coef_integral_of_flag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hc : IsFixedConv Λ g F)
    (j : ℕ) (x : S.V) (hx : x ∈ Xflag F j)
    (hP : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
        ∃ o : 𝓞 E, (s : E) * w c = o := by
  classical
  have hxa : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hxa

  have hxw : x = ∑ i, l i • F.fl.e i := by
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    simp
  refine ⟨fun c => l c, hxw, ?_, ?_⟩
  · intro c hc
    by_contra h
    have hmem : c.val < j := hl (Finsupp.mem_support_iff.2 h)
    omega
  · intro P hgP c
    have := P.isPrime
    have key : ∀ {L : Submodule (𝓞 E) S.V} {y : S.V},
        y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L ↔ ∃ u ∈ P.asIdeal.primeCompl, u • y ∈ L := Iff.rfl

    obtain ⟨s, hs, hsx⟩ := key.1 (hP P hgP)
    have hxX : x ∈ Submodule.span E (Set.range F.fl.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hxa
    have hsX : s • x ∈ Formalism.MainNotions.S.Lat.XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨hsx, ?_⟩
      exact Submodule.smul_of_tower_mem _ s hxX

    obtain ⟨cc, -, hc1, heq⟩ := hc.1 P
    have hloc : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.MainNotions.S.Lat.XLam Λ F) :=
      key.2 ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hsX⟩
    have hfun : (fun a => cc a • F.fl.e a) = F.fl.e :=
      funext fun a => by rw [hc1 hgP a, one_smul]
    rw [heq, hfun] at hloc
    obtain ⟨t, ht, htx⟩ := key.1 hloc
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 htx
    have h1 : ∑ i, ((o i : 𝓞 E) : E) • F.fl.e i = t • s • x := by
      rw [← ho]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact algebraMap_smul E (o i) (F.fl.e i)
    have h2 : t • s • x = ∑ i, (((t * s : 𝓞 E) : E) * l i) • F.fl.e i := by
      rw [← mul_smul, ← algebraMap_smul E (t * s) x, hxw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
    have hsum : ∑ i, (((o i : 𝓞 E) : E) - ((t * s : 𝓞 E) : E) * l i) • F.fl.e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, ← h2, sub_self]
    have hc0 := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum c
    exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, o c, (sub_eq_zero.1 hc0).symm⟩

end GlobalTheory.FlagCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangular
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_integral_over {E : Type} [Field E] [NumberField E]
    (g : ℕ) (hg : g ≠ 0) (m : E)
    (hm : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * m = o) :
    ∃ ξ c : 𝓞 E, m - (ξ : E) = (g : E) * (c : E) * m := by
  let D : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E m) 1
  have hD : ∀ s : 𝓞 E, s ∈ D ↔ ∃ o : 𝓞 E, (s : E) * m = o := by
    intro s
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [Algebra.smul_def] at hy; exact hy.symm⟩
    · rintro ⟨o, ho⟩; exact ⟨o, by rw [Algebra.smul_def]; exact ho.symm⟩
  have htop : D ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_le_maximal _ hne
    have hgQ : (g : 𝓞 E) ∈ Q := hQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast hg
    have hQbot : Q ≠ ⊥ := fun h => hg0 (by rw [h] at hgQ; simpa using hgQ)
    obtain ⟨s, hs, o, ho⟩ := hm ⟨Q, hQmax.isPrime, hQbot⟩ hgQ
    exact hs (hQ (Ideal.mem_sup_left ((hD s).2 ⟨o, ho⟩)))
  have h1 : (1 : 𝓞 E) ∈ D ⊔ Ideal.span {(g : 𝓞 E)} := by rw [htop]; trivial
  obtain ⟨d, hd, y, hy, hdy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨o, ho⟩ := (hD d).1 hd
  refine ⟨o, c, ?_⟩
  have e := congrArg (fun x : 𝓞 E => (x : E)) hdy
  push_cast at e
  rw [← ho]
  linear_combination (-m) * e

theorem admissible_of_congr_unitriangular {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hlow : ∀ a b, b < a → M a b = 0) (hdiag : ∀ a, M a a = 1)
    (hint : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b,
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o)
    (hloc : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a,
      frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ))
    (hmod : ∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) :
    IsAdmissible Λ g F F' := by
  classical
  have key : ∀ a b, ∃ ξ c : 𝓞 E, M a b - (ξ : E) = (g : E) * (c : E) * M a b :=
    fun a b => exists_int_sub_eq_mul_of_integral_over g hg (M a b) (fun P hP => hint P hP a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else (key a b).choose
  have hξ : ∀ a b, ∃ c : 𝓞 E, M a b - ((ξ a b : 𝓞 E) : E) = (g : E) * (c : E) * M a b := by
    intro a b
    by_cases h1 : b < a
    · exact ⟨0, by simp [ξ, h1, hlow a b h1]⟩
    · by_cases h2 : a = b
      · subst h2; exact ⟨0, by simp [ξ, hdiag]⟩
      · obtain ⟨c, hc⟩ := (key a b).choose_spec
        exact ⟨c, by simpa [ξ, h1, h2] using hc⟩
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], ?_⟩
  intro b P hP
  haveI := P.isPrime
  have hsplit : frame F' b - frameAct (frame F) ξ b =
      (frame F' b - ∑ a, M a b • frame F a) + ∑ a, (M a b - (ξ a b : E)) • frame F a := by
    simp only [frameAct, sub_smul, Finset.sum_sub_distrib]; abel
  rw [hsplit]
  refine Submodule.add_mem _ (hmod b P hP) (Submodule.sum_mem _ fun a _ => ?_)
  obtain ⟨c, hc⟩ := hξ a b
  obtain ⟨t, ht, htf⟩ := hloc P hP a
  obtain ⟨s, hs, o, ho⟩ := hint P hP a b
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  rw [hc]
  have e : (s * t) • (((g : E) * (c : E) * M a b) • frame F a) =
      ((g : 𝓞 E) * (c * o)) • (t • frame F a) := by
    rw [← algebraMap_smul E (s * t), ← algebraMap_smul E ((g : 𝓞 E) * (c * o)),
      ← algebraMap_smul E t, smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_natCast]
    change (s : E) * (t : E) * ((g : E) * (c : E) * M a b) = (g : E) * ((c : E) * (o : E)) * (t : E)
    rw [← ho]; ring
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) htf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeRelIndexPiUnivEqFinprod
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem invVol_pi_univ : ∀ {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (K U : ∀ i, Subgroup (G i)),
    {i | K i ≠ U i}.Finite → (∀ i, (K i).relIndex (U i) ≠ 0 ∧ (U i).relIndex (K i) ≠ 0) →
    (Subgroup.pi Set.univ K).relIndex (Subgroup.pi Set.univ U) ≠ 0 ∧
    (Subgroup.pi Set.univ U).relIndex (Subgroup.pi Set.univ K) ≠ 0 ∧
    invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) = ∏ᶠ i, invVol (K i) (U i) := by
  intro ι G _ K U hfin hne
  classical
  set S := hfin.toFinset with hSdef
  have hoff : ∀ i, i ∉ S → K i = U i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have key : ∀ A B : ∀ i, Subgroup (G i), (∀ i, i ∉ S → A i ≤ B i) →
      (Subgroup.pi Set.univ B).relIndex (Subgroup.pi Set.univ A) =
        ∏ i ∈ S, (B i).relIndex (A i) := by
    intro A B hAB
    exact GlobalTheory.relIndex_eq_prod_local (∀ i, G i) ι G (fun i => Pi.evalMonoidHom G i) ⊤
      (Subgroup.pi Set.univ A) (Subgroup.pi Set.univ B) A B S
      (fun v h _ => ⟨Pi.mulSingle v h, Subgroup.mem_top _, by simp,
        fun w hw => by simp [Pi.mulSingle_eq_of_ne hw]⟩)
      (fun g => by simp [Subgroup.mem_pi])
      (fun g => by simp [Subgroup.mem_pi])
      hAB
  have h1 := key K U (fun i hi => (hoff i hi).le)
  have h2 := key U K (fun i hi => (hoff i hi).ge)
  have hfp : ∀ f : ι → ℝ, (∀ i, i ∉ S → f i = 1) → ∏ᶠ i, f i = ∏ i ∈ S, f i := fun f hf =>
    finprod_eq_prod_of_mulSupport_subset f (fun i hi => by
      by_contra h
      exact hi (hf i h))
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; exact Finset.prod_ne_zero_iff.2 (fun i _ => (hne i).1)
  · rw [h1]; exact Finset.prod_ne_zero_iff.2 (fun i _ => (hne i).2)
  · rw [hfp _ (fun i hi => by simp [invVol, hoff i hi, Subgroup.relIndex_self])]
    simp only [invVol, h1, h2, Nat.cast_prod]
    rw [Finset.prod_div_distrib]

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetSecondTypeFamilyAmpSqLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyBound

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (i : ℕ) : ∑ m ∈ Finset.range (i + 1), x ^ m ≤ 2 * x ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 ≤ x ^ i := by positivity
    have : 2 * x ^ i ≤ x ^ (i + 1) := by rw [pow_succ]; nlinarith
    linarith

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  unfold Frames.mass
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · rw [if_pos ho, if_pos ⟨ho.1, h _ ho.1 ho.2⟩]
  · rw [if_neg ho]; exact bot_le

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ m ∈ s, Q m Λ) : S.mass d P ≤ ∑ m ∈ s, S.mass d (Q m) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨m, hm, hq⟩ := h _ ho.1 ho.2
    rw [if_pos ho]
    refine le_trans ?_ (Finset.single_le_sum (f := fun m =>
      if S.IsTerm d o.out ∧ Q m o.out then ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => bot_le) hm)
    rw [if_pos ⟨ho.1, hq⟩]
  · rw [if_neg ho]; exact bot_le

theorem sumData_mono (φ ψ : S.Datum → ℝ≥0∞) (h : ∀ d, φ d ≤ ψ d) : S.sumData φ ≤ S.sumData ψ := by
  unfold Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => by gcongr; exact h _

end

theorem family_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β J βJ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ S.InFF β J βJ d Λ
  swap
  · have h0 : ∀ d, S.amp d (S.InFF β J βJ d) = 0 := by
      intro d
      unfold Frames.amp
      have : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
          ¬ (S.IsTerm d o.out ∧ S.InFF β J βJ d o.out) := fun o ho => hex ⟨d, _, ho⟩
      simp [this]
    have : S.ampSq (S.InFF β J βJ) = 0 := by
      unfold Frames.ampSq Frames.sumData
      simp [h0]
    rw [this]; exact bot_le
  obtain ⟨d₀, Λ₀, ht, hF⟩ := hex
  obtain ⟨-, -, -, -, hH, ⟨i, -, hi⟩, hbz, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht
  have hβ : β = S.q ^ i := by rw [← hF.2.1, hi]
  have hq0 : 0 < S.q := GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  have hq1 : S.q ≠ 1 := by
    intro h
    exact hF.1.1 (hbz.2 (by rw [hi, h, one_pow]))
  have hq : 2 ≤ S.q := by omega
  have hβ1 : 1 ≤ β := by rw [hβ]; exact Nat.one_le_pow _ _ hq0
  have hk1 : 1 ≤ k := by omega
  set A0 : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA1
  set e : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with he
  have hA0p : 0 ≤ A0 := by positivity
  have hA1p : 0 ≤ A1 := by positivity
  have hep : 0 ≤ e := by positivity
  have hmass : ∀ d, S.mass d (S.InFF β J βJ d) ≤ ENNReal.ofReal (2 * A0 * (β : ℝ) ^ (k - 1)) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun m Λ => S.cardI d Λ = S.q ^ m) ?_).trans ?_
    · intro Λ hΛ hP
      obtain ⟨⟨m, hm⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ hΛ
      refine ⟨m, ?_, hm⟩
      rw [hm, hP.2.1, hβ] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      exact Finset.mem_range.2 (by omega)
    · refine (Finset.sum_le_sum fun m _ => (_root_.GlobalTheory.HL.MassGlue.mass_le_and_finite L r k S hk1 d).1 (S.q ^ m)).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ (k - 1) := by
        have h2 : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
        exact h2.trans (le_self_pow₀ (by linarith) (by omega))
      have hg := geom_le _ hx i
      have hc : ∀ m : ℕ, ((S.q ^ m : ℕ) : ℝ) ^ (k - 1) = ((S.q : ℝ) ^ (k - 1)) ^ m := by
        intro m; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
      rw [← Finset.mul_sum, hβ]
      simp only [hc]
      nlinarith [mul_le_mul_of_nonneg_left hg hA0p]
  have h1 := (GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk1).2 (S.InFF β J βJ) _ (7 * e) (by positivity)
    hmass (fun d => GlobalTheory.T.amplitude_le_mass_secondType_family L r k S hk β J βJ d)
  have h2 : (S.sumData fun d => S.mass d (S.InFF β J βJ d)) ≤
      ENNReal.ofReal (A1 * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn :=
    (sumData_mono S _ _ fun d => mass_mono S d _ _ fun Λ _ h => h.2.1).trans (_root_.GlobalTheory.DefectShare.mass_defect_order_le L r k S hk β hβ1)
  refine h1.trans ?_
  refine (mul_le_mul_right h2 _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hb : (β : ℝ) ^ (k - 1) ≠ 0 := by
    have : (0 : ℝ) < β := by exact_mod_cast hβ1
    positivity
  have : (7 * e) ^ 2 * (2 * A0 * (β : ℝ) ^ (k - 1)) * (A1 * ((β : ℝ) ^ (k - 1))⁻¹) = 98 * A0 * A1 * e ^ 2 := by
    field_simp
    ring
  rw [this]

end GlobalTheory.HL.FamilyBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactNormBoundedBesselClosedSubgroup
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf


open scoped Matrix.Norms.L2Operator in
theorem isCompact_closed_inter_opn_le {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)) (hS : IsClosed S)
    (R : ℝ) : IsCompact {g | g ∈ S ∧ opn g ≤ R} := by

  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have hK : IsCompact (e ⁻¹' Metric.closedBall 0 R) :=
    e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hset : {g | g ∈ S ∧ opn g ≤ R} = S ∩ e ⁻¹' Metric.closedBall 0 R := by
    ext g
    simp [opn, e, mem_closedBall_zero_iff]
  rw [hset]
  exact hK.inter_left hS

theorem isCompact_normBounded : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S →
    ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  intro k r S hS R
  exact isCompact_closed_inter_opn_le S hS.2.1 R

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpqRepVocabularyAgree
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem upqRep_vocabulary_agree : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), (Formalism.MainNotions.S.IsDSHpk k r ε lam σ ↔ PI.UpqRep.IsDSHpk k r ε lam σ) ∧ (∀ v, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v ↔ PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) ∧ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ = PI.UpqRep.smoothVecs (k := k) (r := r) σ ∧ (Formalism.QuantumDeterminants.IsHCParam lam ↔ PI.UpqRep.IsHCParam lam) ∧ (∀ P, Formalism.MainNotions.S.IsCayleyU k r ε P ↔ PI.UpqRep.IsCayleyU k r ε P) ∧ Formalism.MainNotions.S.lowKSub ε lam σ = PI.UpqRep.lowKSub ε lam σ := by
  intro k r H _ _ _ σ ε lam
  exact ⟨Iff.rfl, fun _ => Iff.rfl, rfl, Iff.rfl, fun _ => Iff.rfl, rfl⟩

end GlobalTheory
end

