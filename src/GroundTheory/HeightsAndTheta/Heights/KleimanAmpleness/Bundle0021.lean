module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltKernel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Filt.Kernel

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_secs_iff' {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by
  simp [SubSystem.secs, Submodule.mem_iInf]

def ratioPow (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (j : Fin (N + 1)) (b : ℕ) :
    chartRing S x I :=
  ⟨x j ^ b / x i ^ b, X j ^ b, X i ^ b, b, pow_mem (X_mem_monos hi) b, isHomogeneous_X_pow _ _,
    isHomogeneous_X_pow _ _, by simp⟩

theorem aeval_div_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (f : Poly S N) :
    aeval (fun l => x l / x i) f ∈ chartRing S x I := by
  have h : (aeval (fun l => x l / x i) : Poly S N →ₐ[S] Ω).range ≤ chartRing S x I := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X _ _, isHomogeneous_X _ _, by simp⟩
  exact h ⟨f, rfl⟩

theorem idealMod_le (j : Fin (N + 1)) (b : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)) I ≤
      Submodule.span (chartRing S x I) {x j ^ b / x i ^ b} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set M := Submodule.span (chartRing S x I) {x j ^ b / x i ^ b}
  let K : Ideal (Poly S N) :=
    { carrier := {f | aeval (fun l => x l / x i) f ∈ M}
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *; exact M.add_mem hf hg
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact M.zero_mem
      smul_mem' := fun r f hf => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact M.smul_mem ⟨_, aeval_div_mem_chartRing I hi r⟩ hf }
  have hK : primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b) ≤ K := by
    refine sup_le (fun f hf => ?_) (Ideal.span_le.mpr ?_)
    · change aeval (fun l => x l / x i) f ∈ M
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent f, map_sum]
      convert M.zero_mem
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f) i,
        (mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
          (homogeneousComponent_mem_primeOf x hf d), zero_div]
    · rintro g ⟨c, hg, hz⟩
      have hδ : x i ^ b ∈ (twistSys S x (b : ℤ)).sub I := by
        change x i ^ b ∈ twistMod S x (b : ℤ) I
        rw [twistMod_eq_span _ I hi, zpow_natCast]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨o, ho, he⟩ := hz I _ hδ
      rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at ho
      obtain ⟨a, rfl⟩ := ho
      change aeval (fun l => x l / x i) g ∈ M
      rw [aeval_div_of_isHomogeneous hg i, Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      rw [chartRing_smul_def] at he ⊢
      field_simp
      linear_combination -he
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hm : aeval (fun l => x l / x i) f ∈ M := hK hf
  rw [aeval_div_of_isHomogeneous hfe i] at hm
  have h := M.smul_mem (⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow _ _, hse,
    by simp⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at h
  rw [SetLike.mem_coe]
  convert h using 1
  change _ = x i ^ e / aeval x s * (aeval x f / x i ^ e)
  have : x i ^ e ≠ 0 := pow_ne_zero _ hxi
  field_simp

theorem proof : SectionCount.Drop.Filt.Kernel.Statement.{u, w} := by
  intro S _ Ω _ _ N x j b F hj
  have hjb : x j ^ b ≠ 0 := pow_ne_zero _ hj
  constructor
  · intro t ht
    refine mem_secs_iff'.mpr fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp ht I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · change q ∈ twistMod S x (-(b : ℤ)) I at hq
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      have h := (F.sub I).smul_mem (a * ratioPow I hi j b) hy
      rw [chartRing_smul_def] at h ⊢
      convert h using 1
      simp only [ratioPow, Subalgebra.coe_mul, zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact (F.sub I).add_mem hu hv
  · intro s hs
    refine ⟨(x j ^ b)⁻¹ * s, mem_secs_iff'.mpr fun I => ?_, by field_simp⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp hs I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    rw [SubSystem.twist_sub_eq_mul_of_line]
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (idealMod_le j b I hi hq)
      have hq' : (a : Ω) * x i ^ (-(b : ℤ)) ∈ (twistSys S x (-(b : ℤ))).sub I := by
        change _ ∈ twistMod S x (-(b : ℤ)) I
        rw [twistMod_eq_span _ I hi]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
      convert Submodule.mul_mem_mul hq' hy using 1
      rw [chartRing_smul_def]
      simp only [zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact add_mem hu hv

end SectionCount.Drop.Filt.Kernel

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Sections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mul_mem_pow_succ (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) : a * q ∈ (Q.pow (m + 1)).sub I :=
  Submodule.subset_span ⟨q, hq, a, ha, by rw [smul_eq_mul, mul_comm]⟩

theorem mul_pow_mem_pow (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_pow_succ Q I ih hq

theorem aeval_mem_pow (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by
  have hI : ∀ l, h l ∈ Q.sub I := fun l =>
    (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)
  have hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))),
      ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I := by
    intro α s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_twistMod_zero (S := k) I
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
      exact mul_pow_mem_pow Q I ih (hI j) (α j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ α.support, α i = n := by
    have := hf (mem_support_iff.mp hα)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  have hmem := hprod α α.support
  rw [hdeg] at hmem
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_of_tower_mem _ _ hmem

theorem coordGraded_le_secs (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (n : ℕ) : (coordGraded k h).piece (n : ℤ) ≤ (twistMul Q n 0).secs := by
  rw [twistMul, SubSystem.twist_twistSys_zero]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  have hen : e = n := by exact_mod_cast he
  subst hen
  exact (Submodule.mem_iInf _).mpr fun I =>
    (Submodule.restrictScalars_mem k _ _).mpr (aeval_mem_pow Q hh I hf)

theorem finite_secs_twistMul (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by
  obtain ⟨m, deg, gen, -, hspan⟩ :=
    hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates
  have e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) =
      twistMul Nb.toSubSystem n 0 := by
    rw [twistMul, SubSystem.twist_twistSys_zero]
    exact twistSys_zero_twist _
  have hle := hspan n
  rw [e1] at hle
  let T : Submodule k Ω := ⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map
    ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)
  have hT : T.FG := Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _
  have hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ),
      f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, f, e, hf, hed, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    convert hf using 1
    omega
  have : FiniteDimensional k T := Module.Finite.iff_fg.mpr hT
  exact Submodule.finiteDimensional_of_le (hle.trans hle')

end Sections

theorem SectionCount.Top.proof (hHP : HilbertPositive.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w}) (hTF : TwistFinite.Statement.{u, w})
    (hDim : VeryAmpleDim.Statement.{u, w}) (hDeg : VeryAmpleDegree.Statement.{u, w}) :
    SectionCount.Top.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb hZ hN
  obtain ⟨r, h, hV⟩ := hN
  have hx : x ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hZ.relevant
    exact hi ((mem_primeOf_of_isHomogeneous _ (isHomogeneous_X k i)).mpr (by simp))
  have hZh := hDim k Ω N x (d + 1) Nb r h hZ hV
  obtain ⟨⟨C, hC⟩, -, -⟩ := hHP k Ω r h (d + 1) (Nat.le_add_left 1 d) hZh
  have hnum : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      NumbersDVR.intNum k (primeOfOne (S := k) h) (fun _ : Fin (d + 1) => fun _ : Unit => (1 : ℤ)) := by
    rw [hDeg k Ω N x (d + 1) Nb r h hZ hV]
    exact hTie k Ω r h (d + 1) (primeOf (S := k) h) (fun _ => 1) hZh
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  have hle : (Module.finrank k ((coordGraded k h).piece (n : ℤ)) : ℝ) ≤
      (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) := by
    have := finite_secs_twistMul hTF Nb hx hV n
    exact_mod_cast Submodule.finrank_mono (coordGraded_le_secs Nb.toSubSystem hV.mem_secs n)
  rw [hnum]
  rw [Nat.add_sub_cancel] at hn
  have := (abs_le.mp hn).1
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepDataJProper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section JProper

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    exact Submodule.mul_mem_mul hq hy
  · refine Submodule.mul_le.mpr fun q hq y hy => Submodule.subset_span ⟨q, hq, y, hy, rfl⟩

def ChartInvertible {I : Chart x} (P : Submodule (chartRing S x I) Ω) : Prop :=
  ∃ Q' : Submodule (chartRing S x I) Ω, P * Q' = 1

theorem ChartInvertible.mul {I : Chart x} {P P' : Submodule (chartRing S x I) Ω}
    (h : ChartInvertible P) (h' : ChartInvertible P') : ChartInvertible (P * P') := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨Q', hQ'⟩ := h'
  exact ⟨Q * Q', by rw [mul_mul_mul_comm, hQ, hQ', one_mul]⟩

theorem chartInvertible_twistSys (c : ℤ) (I : Chart x) :
    ChartInvertible ((twistSys S x c).sub I) :=
  (twistBundle S x c).invertible I

theorem chartInvertible_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) (I : Chart x) :
    ChartInvertible ((twistMul M.toSubSystem p m).sub I) := by
  have hpow : ∀ n : ℕ, ChartInvertible ((M.toSubSystem.pow n).sub I) := by
    intro n
    induction n with
    | zero => exact chartInvertible_twistSys 0 I
    | succ n ih =>
      change ChartInvertible (((M.toSubSystem.pow n).twist M.toSubSystem).sub I)
      rw [twist_sub_eq_mul]
      exact ChartInvertible.mul (M.invertible I) ih
  rw [twistMul, twist_sub_eq_mul]
  exact ChartInvertible.mul (chartInvertible_twistSys m I) (hpow p)

theorem aeval_mul_mem_twistMod {I : Chart x} {G : Poly S N} {b : ℕ} (hG : G.IsHomogeneous b) {a : ℤ}
    {o : Ω} (ho : o ∈ twistMod S x a I) : aeval x G * o ∈ twistMod S x (a + b) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x G * o ∈ twistMod S x (a + b) I)
    ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    refine Submodule.subset_span ⟨G * f, s, e, b + e', hs, hG.mul hf, hse, by push_cast; omega, ?_⟩
    rw [map_mul, mul_div_assoc]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [mul_add]; exact Submodule.add_mem _ hy hz
  · intro r z _ hz
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ r hz

theorem exists_form_chart {I : Chart x} {P : Submodule (chartRing S x I) Ω} (hP : ChartInvertible P)
    {σ : Ω} (hσ : σ ∈ P) (hσ0 : σ ≠ 0) : ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      aeval x g ≠ 0 ∧ ∀ δ ∈ P, ∃ o ∈ twistMod S x (e : ℤ) I, aeval x g * δ = σ * o := by
  obtain ⟨Q', hQ'⟩ := hP
  have hq : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have h1 : (1 : Ω) ∈ (1 : Submodule (chartRing S x I) Ω) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← hQ', hbot, Submodule.mul_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨q, hqQ, hq0⟩ := hq
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hσ hqQ :
    σ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨g, s, e, hs, hg, hse, hbg⟩ := b.2
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hb' : (b : Ω) = σ * q := hb
  have hgx : aeval x g = σ * q * aeval x s := by
    rw [← hb', hbg, div_mul_cancel₀ _ hs0]
  refine ⟨g, e, hg, by rw [hgx]; exact mul_ne_zero (mul_ne_zero hσ0 hq0) hs0, fun δ hδ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hδ hqQ :
    δ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨h, t, e', ht, hh, hte, hah⟩ := a.2
  have ha' : aeval x h / aeval x t = δ * q := by rw [← hah]; exact ha
  refine ⟨aeval x (s * h) / aeval x t,
    Submodule.subset_span ⟨s * h, t, e', e + e', ht, hse.mul hh, hte, by push_cast; ring, rfl⟩, ?_⟩
  rw [map_mul, mul_div_assoc, ha', hgx]
  ring

end JProper

theorem StepData.JProper.proof : StepData.JProper.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T
  have hloc : ∀ I : Chart x, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧ aeval x g ≠ 0 ∧
      ∀ δ ∈ T.D.sub I, ∃ o ∈ twistMod k x (e : ℤ) I, aeval x g * δ = T.si * o := fun I =>
    exists_form_chart (chartInvertible_twistMul T.M T.p (T.m - T.c₁) I)
      ((Submodule.mem_iInf _).mp T.si_mem I) T.si_ne
  choose g e hg hg0 hgD using hloc
  refine ⟨∏ I, g I, ∑ I, e I, Ideal.subset_span ⟨∑ I, e I, IsHomogeneous.prod _ _ _
    fun I _ => hg I, fun I δ hδ => ?_⟩, IsHomogeneous.prod _ _ _ fun I _ => hg I, ?_⟩
  · obtain ⟨o, ho, hδo⟩ := hgD I δ hδ
    have hrest : (∏ J ∈ Finset.univ.erase I, g J).IsHomogeneous (∑ J ∈ Finset.univ.erase I, e J) :=
      IsHomogeneous.prod _ _ _ fun J _ => hg J
    refine ⟨aeval x (∏ J ∈ Finset.univ.erase I, g J) * o, ?_, ?_⟩
    · have hm := aeval_mul_mem_twistMod hrest ho
      have hdeg : ((e I : ℕ) : ℤ) + ((∑ J ∈ Finset.univ.erase I, e J : ℕ) : ℤ) =
          ((∑ J, e J : ℕ) : ℤ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ I)]; push_cast; ring
      rwa [hdeg] at hm
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (aeval x (g I)),
        mul_assoc, hδo]
      ring
  · rw [mem_primeOf_of_isHomogeneous x (IsHomogeneous.prod _ _ _ fun I _ => hg I), map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun I _ => hg0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneMidSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SnapperHyperplaneMid.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp →
    ∀ (a : ℤ) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
      eulerCharQuot k
          ((((twistSys k x (a + 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)}))).twistPows t
            (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a + 1)).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)) =
        pieceChar k pp a L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperHyperplane.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp → ∀ a : ℤ,
    ∃ (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp ≤ qq m ∧
        (X i : Poly k N) ∈ qq m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L n (c + 1) - pieceChar k pp a L n c = ∑ m, pieceChar k (qq m) (b m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotAdd.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ F₃ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    (∀ I, F₃.sub I ≤ F₂.sub I) →
    eulerCharQuot k F₁.toSubSystem F₃.toSubSystem =
      eulerCharQuot k F₁.toSubSystem F₂.toSubSystem + eulerCharQuot k F₂.toSubSystem F₃.toSubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

