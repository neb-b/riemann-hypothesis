module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundTwo
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem coefBound_two :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ a c : H, Sm ε σ a → a ≠ 0 → Sm ε σ c → c ≠ 0 → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ γ : H → H → ℂ, (∀ b, Sm ε σ b → SobFun ε σ (γ b)) → (∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w))) → ∀ M : ℝ, 0 ≤ M → (∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ‖γ (σ g' c) (σ g a)‖ ≤ M * (1 + hs g) ^ N * (1 + hs g') ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖γ b w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ hS hB a c ha ha0 hc hc0 N
  obtain ⟨Sa, Ca, hSa, hCa, ba⟩ := hB a ha ha0 N
  obtain ⟨Sc, Cc, hSc, hCc, bc⟩ := hB c hc hc0 N
  refine ⟨Sa ++ Sc, Ca * Cc, words_append hSa hSc, mul_nonneg hCa hCc, ?_⟩
  intro γ h1 h2 M hM hγ b w hb hw
  have step : ∀ g' ∈ UJset ε, ‖γ (σ g' c) w‖ ≤ (Ca * M * sobNorm σ Sa w) * (1 + hs g') ^ N := by
    intro g' hg'
    obtain ⟨ℓ, hℓ, e⟩ := (h1 _ (hc.translate hS.1 hg')).exists_ext
    have hp : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have := ba ℓ hℓ (M * (1 + hs g') ^ N) (mul_nonneg hM hp) (fun g hg => by
      rw [e _ (ha.translate hS.1 hg)]
      exact (hγ g hg g' hg').trans (le_of_eq (by ring))) w hw
    rw [e _ hw] at this
    exact this.trans (le_of_eq (by ring))
  obtain ⟨ℓ, hℓ, e⟩ := (h2 w hw).exists_ext
  have n1 := sobNorm_nonneg σ Sa w
  have n2 := sobNorm_nonneg σ Sc w
  have n3 := sobNorm_nonneg σ Sa b
  have n4 := sobNorm_nonneg σ Sc b
  have key := bc ℓ hℓ (Ca * M * sobNorm σ Sa w) (by positivity) (fun g hg => by
    rw [e _ (hc.translate hS.1 hg), norm_star]
    exact step g hg) b hb
  rw [e _ hb, norm_star] at key
  rw [sobNorm_append, sobNorm_append]
  refine key.trans ?_
  calc Cc * (Ca * M * sobNorm σ Sa w) * sobNorm σ Sc b
      = Ca * Cc * M * sobNorm σ Sc b * sobNorm σ Sa w := by ring
    _ ≤ _ := by gcongr <;> linarith

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)
      have h3 := mul_mem h2 h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
      exact h3
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

theorem toEAf_incA (D : D7) (x : D.host.E) : toEAf D (incA D x) = eToEAf D x := rfl

theorem eToEAf_int (D : D7) (x : 𝓞 D.host.E) :
    eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)

theorem conj_mem_at (D : D7) (e : AE D) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have hi : IsIntegral ℤ (D.sp.cm.sig (c : D.host.E)) :=
    (show IsIntegral ℤ (c : D.host.E) from c.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom
  have h3 := mul_mem h2 (eToEAf_int D ⟨_, hi⟩)
  rw [map_mul, toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  change D.sp.cm.sig a = ((n : 𝓞 D.host.E) : D.host.E)⁻¹ * D.sp.cm.sig (c : D.host.E)
  rw [hc', hcast, map_mul, map_natCast]
  field_simp

theorem conj_mem_intAf : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rintro D e P ⟨⟨es, hes, rfl⟩, -⟩ hP a ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => conj_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

end GlobalTheory.IdemIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCf
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.TypeSumCtrl

def allWords {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) : List (List α) :=
  Nat.rec [[]] (fun _ T => [] :: T.flatMap fun l => (List.ofFn E).map fun X => X :: l) m

theorem allWords_zero {α : Type} {k : ℕ} (E : Fin k → α) : allWords E 0 = [[]] := rfl

theorem allWords_succ {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) :
    allWords E (m + 1) = [] :: (allWords E m).flatMap fun l => (List.ofFn E).map fun X => X :: l := rfl

theorem mem_allWords {α : Type} {k : ℕ} (E : Fin k → α) :
    ∀ (m : ℕ) (l : List α), l ∈ allWords E m ↔ l.length ≤ m ∧ ∀ X ∈ l, ∃ i, E i = X
  | 0, l => by
    cases l <;> simp [allWords_zero]
  | m + 1, [] => by simp [allWords_succ]
  | m + 1, X :: l => by
    simp only [allWords_succ, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_ofFn, List.length_cons,
      reduceCtorEq, false_or, List.cons.injEq, forall_eq_or_imp, Nat.add_le_add_iff_right]
    constructor
    · rintro ⟨l', h1, Y, h2, rfl, rfl⟩
      exact ⟨((mem_allWords E m _).1 h1).1, h2, ((mem_allWords E m _).1 h1).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨l, (mem_allWords E m _).2 ⟨h1, h3⟩, X, h2, rfl, rfl⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {k : ℕ}

def cf (E : Fin k → Mx n) (X : Mx n) : ℝ := ∑ i, |((X * (E i)ᴴ).trace).re|

theorem cf_nonneg (E : Fin k → Mx n) (X : Mx n) : 0 ≤ cf E X := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_cf (E : Fin k → Mx n) : Continuous (cf E) := by
  unfold cf
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)).abs

omit [CompleteSpace H] in
theorem Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) (c : Fin k → ℂ)
    {x : Fin k → H} (hx : ∀ i, Sm ε σ (x i)) : Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hL] at this
  exact this

theorem key (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    ∀ p : List (Mx n), (∀ X ∈ p, ∃ i, E i = X) → p.length + l.length ≤ m →
      ‖Dw σ (p ++ l) w‖ ≤ (l.map (cf E)).prod * sobNorm σ (allWords E m) w := by
  induction l with
  | nil =>
    intro p hp hm
    simpa using norm_Dw_le_sobNorm σ ((mem_allWords E m p).2 ⟨by simpa using hm, hp⟩) w
  | cons X l ih =>
    intro p hp hm
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hp' : ∀ Y ∈ p, Y ∈ lieSet ε := fun Y hY => by
      obtain ⟨i, rfl⟩ := hp Y hY
      exact hE i
    have hs := hw.word h.1 hl'
    have e1 : Dw σ (p ++ X :: l) w =
        ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • Dw σ ((p ++ [E i]) ++ l) w := by
      rw [Dw_append]
      show Dw σ p (dRep σ X (Dw σ l w)) = _
      conv_lhs => rw [hx X hX]
      rw [h.dRep_sum hE hs, Dw_sum h.1 hp' _ (fun i => dRep_mem (isUnit_Jm ε) h.1 hs (hE i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Dw_append, Dw_append]
      rfl
    rw [e1, List.map_cons, List.prod_cons, mul_assoc, cf, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (ih hl' _ ?_ ?_) (abs_nonneg _)
    · intro Y hY
      rcases List.mem_append.1 hY with hY | hY
      · exact hp Y hY
      · exact ⟨i, (List.mem_singleton.1 hY).symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hm ⊢
      omega

theorem sob_le (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (S : List (List (Mx n))) (hS : Words (lieSet ε) S) (hm : ∀ l ∈ S, l.length ≤ m) :
    sobNorm σ S w ≤ (S.map fun l => (l.map (cf E)).prod).sum * sobNorm σ (allWords E m) w := by
  rw [← List.sum_map_mul_right]
  conv_lhs => unfold sobNorm
  refine List.sum_le_sum fun l hl => ?_
  simpa using key h hE hx m hw l (hS l hl) [] (by simp) (by simpa using hm l hl)

theorem exists_ctrl : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ S₀ : List (List (Mx n)), Words (lieSet ε) S₀ → ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ [] ∈ S ∧ Ctrl (lieSet ε) (UJset ε) σ S ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ w, Sm ε σ w → sobNorm σ S₀ w ≤ A * sobNorm σ S w := by
  intro n ε H _ _ _ σ h S₀ hS₀
  obtain ⟨E, hE, -, hx⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hE' : ∀ i, E i ∈ lieSet ε := fun i => (hE i).1
  have hx' : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i := fun X hX => by
    simpa only [Complex.coe_smul] using hx X hX
  set m := (S₀.map List.length).sum with hm
  have hW : Words (lieSet ε) (allWords E m) := fun l hl X hX => by
    obtain ⟨i, rfl⟩ := ((mem_allWords E m l).1 hl).2 X hX
    exact hE' i
  refine ⟨allWords E m, hW, (mem_allWords E m _).2 (by simp), ?_,
    (S₀.map fun l => (l.map (cf E)).prod).sum, ?_, fun w hw => sob_le h hE' hx' m hw S₀ hS₀ fun l hl => ?_⟩
  · refine ⟨fun g => ((allWords E m).map fun l => (l.map fun X => cf E (Jm ε * gᴴ * Jm ε * X * g)).prod).sum, ?_,
      fun g hg w hw => ?_⟩
    · refine continuous_list_sum _ fun l _ => continuous_list_prod _ fun X _ => ?_
      exact (continuous_cf E).comp (f := fun g : Mx n => Jm ε * gᴴ * Jm ε * X * g)
        (((((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
          continuous_const).matrix_mul continuous_const)).matrix_mul continuous_id)
    · rw [sobNorm_translate h.1 hg hw hW]
      have := sob_le h hE' hx' m hw ((allWords E m).map fun l => l.map fun X => g⁻¹ * X * g) ?_ ?_
      · simpa only [List.map_map, Function.comp_def, inv_eq_UJ hg] using this
      · intro l hl X hX
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact conj_mem_lie (isUnit_Jm ε) hg (hW l' hl' Y hY)
      · intro l hl
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        simpa using ((mem_allWords E m l').1 hl').1
  · refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    refine List.prod_nonneg fun y hy => ?_
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hy
    exact cf_nonneg E X
  · exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨l, hl, rfl⟩)

end GlobalTheory.TypeSumCtrl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.ExpansionAverage

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem integrable_K {E : Type} [NormedAddCommGroup E] {F : KG ε → E} (hF : Continuous F) : Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem toMK_mem (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integrable_Dw (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Integrable (fun k : KG ε => e k • Dw σ l (σ (toMK k) w)) (muK ε) :=
  integrable_K (he.smul ((h.continuousOn_Dw hl hw).comp_continuous (continuous_toMK ε) toMK_mem))

theorem Dw_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    Dw σ l (kAvg ε σ e w) = ∫ k, e k • Dw σ l (σ (toMK k) w) ∂(muK ε) := by
  refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
  have h0 : Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) := integrable_Dw h he (l := []) (by simp) hw
  rw [inner_Dw h.1 hl hy hw', kAvg, ← integral_inner h0, ← integral_inner (integrable_Dw h he hl hw),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_Dw h.1 hl hy (hw.translate h.1 (toMK_mem k))]
  ring

theorem form_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ)
    {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    ℓ (kAvg ε σ e w) = ∫ k, e k * ℓ (σ (toMK k) w) ∂(muK ε) := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  have hΛ' : ∀ w, Sm ε σ w → ℓ w = ∑ i, Λ i (Dw σ (S i) w) := hΛ
  rw [hΛ' _ hw']
  simp only [fun i => Dw_kAvg h he (hS i) hw hw',
    fun i => ((Λ i).integral_comp_comm (integrable_Dw h he (hS i) hw)).symm]
  rw [← integral_finsetSum _ fun i _ => (Λ i).integrable_comp (integrable_Dw h he (hS i) hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [hΛ' _ (hw.translate h.1 (toMK_mem k)), Finset.mul_sum, map_smul, smul_eq_mul]

theorem continuousOn_and_hasSum_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (S : List (List (Mx n))) (v : ℕ → H) (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ),
      Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → IsExpn (lieSet ε) (UJset ε) σ S v ℓ C f →
      ContinuousOn f (UJset ε) ∧ ∀ e : KG ε → ℂ, Continuous e → (∀ w, Sm ε σ (kAvg ε σ e w)) → ∀ g ∈ UJset ε,
        HasSum (fun i => ℓ i (σ g (kAvg ε σ e (v i)))) (∫ k, e k * f (g * toMK k) ∂(muK ε)) := by
  intro n ε H _ _ _ σ h S v ℓ C f hS ⟨B, hB, hBd⟩ hE
  have hsc := hE.sobCont hS
  obtain ⟨hv, hC, hb, hsum, hf⟩ := hE
  have hc : ∀ i, ContinuousOn (fun g => ℓ i (σ g (v i))) (UJset ε) := fun i => h.continuousOn_coef (hsc i) (hv i)
  have hbd : ∀ (M : ℝ) i, ∀ g ∈ UJset ε, B g ≤ M → ‖ℓ i (σ g (v i))‖ ≤ M * (C i * sobNorm σ S (v i)) := by
    intro M i g hg hM
    calc ‖ℓ i (σ g (v i))‖ ≤ C i * sobNorm σ S (σ g (v i)) := hb i _ (Sm.translate h.1 (hv i) hg)
      _ ≤ C i * (M * sobNorm σ S (v i)) := mul_le_mul_of_nonneg_left
          ((hBd g hg _ (hv i)).trans (mul_le_mul_of_nonneg_right hM (sobNorm_nonneg _ _ _))) (hC i)
      _ = _ := by ring
  refine ⟨fun g₀ hg₀ => ?_, fun e he hs g hg => ?_⟩
  · have ho : {g | B g < B g₀ + 1} ∈ 𝓝 g₀ := (isOpen_lt hB continuous_const).mem_nhds (lt_add_one (B g₀))
    have h1 : ContinuousOn (fun g => ∑' i, ℓ i (σ g (v i))) (UJset ε ∩ {g | B g < B g₀ + 1}) :=
      continuousOn_tsum (fun i => (hc i).mono Set.inter_subset_left) (hsum.mul_left (B g₀ + 1))
        fun i g hg => hbd _ i g hg.1 (le_of_lt hg.2)
    have h2 : ContinuousOn f (UJset ε ∩ {g | B g < B g₀ + 1}) := h1.congr fun g hg => (hf g hg.1).tsum_eq.symm
    exact (continuousWithinAt_inter ho).1 (h2 g₀ ⟨hg₀, lt_add_one (B g₀)⟩)
  · have hm : ∀ k : KG ε, g * toMK k ∈ UJset ε := fun k => mul_mem_UJ hg (toMK_mem k)
    have hcm : Continuous fun k : KG ε => g * toMK k := continuous_const.mul (continuous_toMK ε)
    obtain ⟨M, hM⟩ := (isCompact_range (hB.comp hcm)).bddAbove
    have hM' : ∀ k : KG ε, B (g * toMK k) ≤ M := fun k => hM ⟨k, rfl⟩
    have hF : ∀ i, Integrable (fun k : KG ε => e k * ℓ i (σ (g * toMK k) (v i))) (muK ε) := fun i =>
      integrable_K (he.mul ((hc i).comp_continuous hcm hm))
    have hS' : Summable fun i => ∫ k, ‖e k * ℓ i (σ (g * toMK k) (v i))‖ ∂(muK ε) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) (fun i => ?_)
        ((hsum.mul_left M).mul_left (∫ k, ‖e k‖ ∂(muK ε)))
      rw [← integral_mul_const]
      refine integral_mono (hF i).norm ((integrable_K he.norm).mul_const _) fun k => ?_
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd M i _ (hm k) (hM' k)) (norm_nonneg _)
    have key := hasSum_integral_of_summable_integral_norm hF hS'
    simp only [fun k => ((hf _ (hm k)).mul_left (e k)).tsum_eq] at key
    refine Eq.mpr (congrArg (HasSum · _) (funext fun i => ?_)) key
    have := form_kAvg h he (sobCont_translate h.1 (hsc i) hg) (hv i) (hs (v i))
    simp only [fun k => sigma_mul h.1 hg (toMK_mem k)]
    exact this

end GlobalTheory.ExpansionAverage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfOrthKfin
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.KFinSep

variable {n : ℕ} {ε : Fin n → Bool}

lemma kfin_of_span {ι : Type} [Finite ι] (b : ι → KG ε → ℂ) (hc : ∀ i, Continuous (b i))
    (ht : ∀ i (k₀ : KG ε), (fun k => b i (k₀ * k)) ∈ Submodule.span ℂ (Set.range b) ∧
      (fun k => b i (k * k₀)) ∈ Submodule.span ℂ (Set.range b)) (i : ι) : KFinFun ε (b i) := by
  refine ⟨Submodule.span ℂ (Set.range b), FiniteDimensional.span_of_finite ℂ (Set.finite_range b),
    Submodule.subset_span ⟨i, rfl⟩, ?_, ?_⟩
  · intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  · intro φ hφ k₀
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact ht j k₀
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy => exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ a hx.1, Submodule.smul_mem _ a hx.2⟩

lemma kfin_const (c : ℂ) : KFinFun ε (fun _ => c) :=
  kfin_of_span (ε := ε) (ι := Unit) (fun _ _ => c) (fun _ => continuous_const)
    (fun i _ => ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩) ()

lemma kfin_add {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p + q) := by
  obtain ⟨F, _, hpF, hFc, hF⟩ := hp
  obtain ⟨G, _, hqG, hGc, hG⟩ := hq
  refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hpF hqG, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact (hFc x hx).add (hGc y hy)
  · intro φ hφ k₀
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact ⟨Submodule.add_mem_sup (hF x hx k₀).1 (hG y hy k₀).1, Submodule.add_mem_sup (hF x hx k₀).2 (hG y hy k₀).2⟩

lemma kfin_mul {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p * q) := by
  obtain ⟨F, hFf, hpF, hFc, hF⟩ := hp
  obtain ⟨G, hGf, hqG, hGc, hG⟩ := hq
  refine ⟨F * G, ?_, Submodule.mul_mem_mul hpF hqG, ?_, ?_⟩
  · exact Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hFf).mul (Module.Finite.iff_fg.1 hGf))
  · intro φ hφ
    refine Submodule.mul_induction_on hφ (fun x hx y hy => (hFc x hx).mul (hGc y hy)) (fun x y hx hy => hx.add hy)
  · intro φ hφ k₀
    refine Submodule.mul_induction_on (C := fun φ => (fun k => φ (k₀ * k)) ∈ F * G ∧ (fun k => φ (k * k₀)) ∈ F * G)
      hφ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · exact ⟨Submodule.mul_mem_mul (hF x hx k₀).1 (hG y hy k₀).1, Submodule.mul_mem_mul (hF x hx k₀).2 (hG y hy k₀).2⟩
    · exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩

lemma mem_span_of_sum {ι κ : Type} [Fintype κ] (b : ι → KG ε → ℂ) (f : KG ε → ℂ) (c : κ → ℂ) (j : κ → ι)
    (h : ∀ k, f k = ∑ l, c l * b (j l) k) : f ∈ Submodule.span ℂ (Set.range b) := by
  have : f = ∑ l, c l • b (j l) := by
    funext k; simp [h, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j l, rfl⟩)

lemma kfin_entry (i j : Fin n) : KFinFun ε (fun k => toMK k i j) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => toMK k a.1 a.2)
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ a.1 l) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply]
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ l a.2) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, mul_comm]

lemma kfin_conjEntry (i j : Fin n) : KFinFun ε (fun k => star (toMK k i j)) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => star (toMK k a.1 a.2))
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous.star) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ a.1 l)) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul']
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ l a.2)) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul', mul_comm]

def finAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | KFinFun ε p ∧ KFinFun ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨kfin_mul hp.1 hq.1, by
    rw [star_mul']; exact kfin_mul hp.2 hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨kfin_add hp.1 hq.1, by
    rw [star_add]; exact kfin_add hp.2 hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact kfin_const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact kfin_const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma finAlg_dense (ε : Fin n → Bool) : (finAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have h : toMK x ≠ toMK y := fun h => hxy ((GlobalTheory.KHolExt.isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push Not at hc
    exact h (Matrix.ext hc)
  exact ⟨GlobalTheory.KHolExt.ent ε i j, ⟨GlobalTheory.KHolExt.ent ε i j, ⟨kfin_entry i j, kfin_conjEntry i j⟩, rfl⟩, hij⟩

end GlobalTheory.KFinSep
end
end

