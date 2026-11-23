module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0018
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0025
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0020
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0024

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnTwo
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1
open scoped ComplexConjugate

theorem an_two_shift (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ) :
    F.sgStar L (z + ω₀ / 2)
      = -(Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2)) := by
  have h := F.sgStarQuasi L ω₀ (z - ω₀ / 2) h0
  have e1 : z - ω₀ / 2 + ω₀ = z + ω₀ / 2 := by ring
  have e2 : (Real.pi : ℂ) * F.herm L (z - ω₀ / 2) ω₀ + (Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2
      = (Real.pi : ℂ) * F.herm L z ω₀ := by
    unfold F.herm; ring
  have e3 : F.semiChar L ω₀ = -1 := by
    unfold F.semiChar; exact if_neg h1
  rw [e1, e2, e3] at h
  rw [h]; ring

theorem an_two_sq (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2) ^ 2
      = F.sgStar L z ^ 2 * F.sgStar L (ω₀ / 2) ^ 2
        * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) := by
  have h := F.sgStarAdd L z (ω₀ / 2) hz h1
  rw [an_two_shift L ω₀ h0 h1 z] at h
  linear_combination -h

theorem an_two_kap (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) * F.sgStar L (ω₀ / 2) ^ 4
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
  have hz : ω₀ / 4 ∉ L.lattice := by
    intro h
    apply h1
    have := L.lattice.add_mem h h
    have e : ω₀ / 4 + ω₀ / 4 = ω₀ / 2 := by ring
    rwa [e] at this
  have hzt : ω₀ / 4 + ω₀ / 2 ∉ L.lattice := by
    intro h
    apply hz
    have := L.lattice.sub_mem h0 h
    have e : ω₀ - (ω₀ / 4 + ω₀ / 2) = ω₀ / 4 := by ring
    rwa [e] at this
  have h2t : 2 * (ω₀ / 2) ∈ L.lattice := by
    have e : 2 * (ω₀ / 2) = ω₀ := by ring
    rwa [e]
  have hH := F.halfShift L (ω₀ / 2) (ω₀ / 4) h1 h2t hz hzt
  have hA := an_two_shift L ω₀ h0 h1 (ω₀ / 4)
  have hB1 := an_two_sq L ω₀ h0 h1 (ω₀ / 4) hz
  have hB2 := an_two_sq L ω₀ h0 h1 (ω₀ / 4 + ω₀ / 2) hzt
  have e1 : ω₀ / 4 + ω₀ / 2 - ω₀ / 2 = ω₀ / 4 := by ring
  have e2 : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4 + ω₀ / 2) ω₀)
      = Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀)
        * Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
    rw [← Complex.exp_add]; congr 1; unfold F.herm; ring
  rw [e1, e2, hA] at hB2
  have hs : F.sgStar L (ω₀ / 4) ≠ 0 := fun h => hz (((F.sgStarBasic L).2.2.1 _).1 h)
  have hE : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) ≠ 0 := Complex.exp_ne_zero _
  have hne : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) * F.sgStar L (ω₀ / 4) ^ 2 ≠ 0 :=
    mul_ne_zero hE (pow_ne_zero _ hs)
  apply mul_left_cancel₀ hne
  rw [← hH]
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) = E at *
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) = X at *
  generalize F.sgStar L (ω₀ / 4) = s at *
  generalize F.sgStar L (ω₀ / 4 - ω₀ / 2) = s' at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize L.weierstrassP (ω₀ / 4) - L.weierstrassP (ω₀ / 2) = a at *
  generalize L.weierstrassP (ω₀ / 4 + ω₀ / 2) - L.weierstrassP (ω₀ / 2) = b at *
  linear_combination (-1 : ℂ) * hB2 + (-(E * T ^ 2 * b)) * hB1

theorem an_two_odd (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (m : ℕ) :
    F.sgStar L (((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2)) ^ 2
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) ^ (2 * (m ^ 2 + m))
        * F.sgStar L (ω₀ / 2) ^ 2 := by
  have hm : (m : ℂ) * ω₀ ∈ L.lattice := by
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem h0 m
  have h := F.sgStarQuasi L ((m : ℂ) * ω₀) (ω₀ / 2) hm
  have e1 : ((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ / 2 + (m : ℂ) * ω₀ := by push_cast; ring
  have hchi : F.semiChar L ((m : ℂ) * ω₀) ^ 2 = 1 := by
    unfold F.semiChar; split_ifs <;> norm_num
  rw [e1, h, mul_pow, mul_pow, hchi, one_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  unfold F.herm
  simp only [map_mul, Complex.conj_natCast]
  push_cast
  ring

theorem an_two_card (L : PeriodPair) (n : ℕ) (hn : n ≠ 0) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) : S.card + 1 = n ^ 2 := by
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem hω n
  have h := F.kerRepsCard L (n : ℂ) S (by exact_mod_cast hn) hst hS
  have e : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.normSq_ofReal]; ring
  rw [e] at h
  exact_mod_cast h

theorem an_two (L : PeriodPair) (n : ℕ) (hn : Odd n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    ((n : ℂ) ^ 2 * ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P)) ^ 2
      = (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) ^ (n ^ 2 - 1) := by
  obtain ⟨m, rfl⟩ := hn
  have hn0 : 2 * m + 1 ≠ 0 := by omega
  have hst : F.MulStable L ((2 * m + 1 : ℕ) : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem hω _
  have hI := F.isogenySigma L ((2 * m + 1 : ℕ) : ℂ) S (by exact_mod_cast hn0) hst hS (ω₀ / 2) h1
  rw [an_two_card L _ hn0 S hS, an_two_odd L ω₀ h0 m, ← an_two_kap L ω₀ h0 h1] at hI
  have hT : F.sgStar L (ω₀ / 2) ≠ 0 := fun h => h1 (((F.sgStarBasic L).2.2.1 _).1 h)
  have ek : (2 * m + 1) ^ 2 - 1 = 4 * (m ^ 2 + m) := by
    have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    omega
  have ek2 : 2 * (2 * m + 1) ^ 2 = 8 * (m ^ 2 + m) + 2 := by ring
  rw [ek]
  rw [ek2] at hI
  clear ek ek2
  generalize m ^ 2 + m = k at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) = κ at *
  generalize ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P) = Q at *
  generalize ((2 * m + 1 : ℕ) : ℂ) = N at *
  have hT' : T ^ (8 * k + 2) ≠ 0 := pow_ne_zero _ hT
  have h3 : κ ^ (2 * k) = N ^ 2 * Q := by
    apply mul_left_cancel₀ hT'
    have : (κ * T ^ 4) ^ (2 * k) * T ^ 2 = T ^ (8 * k + 2) * κ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, pow_add]
      have : 4 * (2 * k) = 8 * k := by ring
      rw [this]; ring
    rw [← this, hI]; ring
  rw [← h3, ← pow_mul]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModInertKur
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem inertKur {d l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (x : Om d)
    (hx : ∀ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ → σ x = x) : ι (x : ℂ) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨e, he⟩ := locEmb d l ι
  have hs : (e (algebraMap (KQ d) (Om d) (sqK d))) ^ 2 = -(d : PadicAlgCl l) := by
    have h1 : (algebraMap (KQ d) (Om d) (sqK d)) ^ 2 = -(d : Om d) := by
      apply Subtype.ext
      simpa [sqK] using sqD_sq d
    rw [← map_pow, h1, map_neg, map_natCast]
  have hint : IsIntegral ℚ_[l] (e (algebraMap (KQ d) (Om d) (sqK d))) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ_[l]), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩
    simp [hs]
  have hK := IntermediateField.adjoin.finiteDimensional hint
  have hmem := fixed_mem_Kur _ hK (e x) (fun ρ hρ => by
    obtain ⟨σ, hσ, hc⟩ := locLift ι e he ρ hρ
    rw [← hc, hx σ hσ])
  rw [← he]
  exact kur_le hl hld hs hmem

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedSeries
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

def HasT (f : ℂ → ℂ) (s : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = s

theorem HasT.add {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z + g z) (s + t) :=
  ⟨hf.1.add hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩

theorem HasT.mul {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z * g z) (s * t) :=
  ⟨hf.1.mul hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩

theorem hasT_const (c : ℂ) : HasT (fun _ => c) (PowerSeries.C c) :=
  ⟨analyticAt_const, taylorRing.2.1 c⟩

theorem hasT_id : HasT (fun z => z) PowerSeries.X := ⟨analyticAt_id, taylorRing.2.2.1⟩

theorem HasT.pow {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (n : ℕ) :
    HasT (fun z => f z ^ n) (s ^ n) := by
  induction n with
  | zero => simpa using hasT_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem hasT_sum {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ι → PowerSeries ℂ)
    (h : ∀ i ∈ S, HasT (f i) (s i)) : HasT (fun z => ∑ i ∈ S, f i z) (∑ i ∈ S, s i) := by
  induction S using Finset.induction_on with
  | empty => simpa using hasT_const 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasT.rescale {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (a : ℂ) :
    HasT (fun z => f (a * z)) (PowerSeries.rescale a s) := by
  refine ⟨?_, by rw [taylorDeriv.2.1 f a hf.1, hf.2]⟩
  refine AnalyticAt.fun_comp (f := fun z : ℂ => a * z) (g := f) ?_ (analyticAt_const.mul analyticAt_id)
  simpa using hf.1

def uFun (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

theorem hasT_uFun (L : PeriodPair) : HasT (uFun L) (wpNum L.g₂ L.g₃) := by
  have h : HasT (L.weierstrassPExcept 0) (pOf L.g₂ L.g₃) :=
    ⟨L.analyticAt_weierstrassPExcept 0, pOfLattice L⟩
  rw [(wpNumDen ℂ L.g₂ L.g₃).1]
  have h3 := (hasT_const 1).add ((hasT_id.pow 2).mul h)
  rw [map_one] at h3
  exact h3

theorem uFun_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) : uFun L z = z ^ 2 * L.weierstrassP z := by
  have h := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h
  rw [← h, uFun]
  field_simp
  ring

def homF (u : ℂ → ℂ) (m : ℕ) (Q : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), Q.coeff i * u z ^ i * z ^ (2 * (m - i))

theorem hasT_homF {u : ℂ → ℂ} {U : PowerSeries ℂ} (hu : HasT u U) (m : ℕ) (Q : ℂ[X]) :
    HasT (homF u m Q) (homS U m Q) :=
  hasT_sum _ _ _ fun i _ => ((hasT_const (Q.coeff i)).mul (hu.pow i)).mul (hasT_id.pow _)

theorem homF_eq {u : ℂ → ℂ} {m : ℕ} {Q : ℂ[X]} (hQ : Q.natDegree ≤ m) {z t : ℂ}
    (h : u z = z ^ 2 * t) : homF u m Q z = z ^ (2 * m) * Q.eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ), Finset.mul_sum, homF]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [h, Nat.add_sub_cancel_left]
  ring

theorem eventually_notMem (L : PeriodPair) {α : ℂ} (hα : α ≠ 0) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ≠ 0 ∧ α * z ∉ L.lattice := by
  have h1 : Filter.Tendsto (fun z : ℂ => α * z) (nhds 0) (nhds 0) := by
    have : ContinuousAt (fun z : ℂ => α * z) 0 := by fun_prop
    simpa [ContinuousAt] using this
  have h2 := h1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h2] with z hz hz0
  refine ⟨hz0, fun hm => hz ⟨hm, ?_⟩⟩
  simpa [hα] using hz0

theorem xs_notMem (L : PeriodPair) {α : ℂ} {T : Finset ℂ} (hs : MulStable L α)
    (hT : IsHalfReps L α T) {z : ℂ} (hz : α * z ∉ L.lattice) : L.weierstrassP z ∉ xsOf L T := by
  intro hm
  obtain ⟨P, hP, hPz⟩ := Finset.mem_image.1 hm
  have hz' : z ∉ L.lattice := fun h => hz (hs z h)
  have hP' : P ∉ L.lattice := fun h => (hT.1 P hP).2 (by
    rw [two_mul]; exact L.lattice.add_mem h h)
  have hαP := (hT.1 P hP).1
  rcases (pInjective L z P hz' hP').1 hPz.symm with h | h
  · apply hz
    have : α * z = α * (z - P) + α * P := by ring
    rw [this]; exact L.lattice.add_mem (hs _ h) hαP
  · apply hz
    have : α * z = α * (z + P) - α * P := by ring
    rw [this]; exact L.lattice.sub_mem (hs _ h) hαP

theorem velu_series (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) :
    PowerSeries.rescale α (wpNum L.g₂ L.g₃)
        * homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2)
      = homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T)) := by
  have hu := hasT_uFun L
  have h1 := (hu.rescale α).mul (hasT_homF hu (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2))
  have h2 := hasT_homF hu (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T))
  rw [← h1.2, ← h2.2]
  refine taylorRing.2.2.2 _ _ ((h1.1.frequently_eq_iff_eventually_eq h2.1).1 ?_)
  refine Filter.Eventually.frequently ?_
  filter_upwards [eventually_notMem L hα] with z hz
  obtain ⟨hz0, hzα⟩ := hz
  have hx := xs_notMem L hs hT hzα
  have hd : (rootPoly (xsOf L T) ^ 2).natDegree ≤ 2 * (xsOf L T).card := by
    rw [(rootPoly_monic (xsOf L T)).natDegree_pow, rootPoly_natDegree]
  rw [homF_eq hd (uFun_eq L hz0), homF_eq (veluNum_natDegree_le _ _ _) (uFun_eq L hz0),
    uFun_eq L (mul_ne_zero hα hz0), veluNum_eval _ _ _ hx, ← velu_fun L α T hα hs hT z hzα,
    Polynomial.eval_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorMain
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem tor_nsmul_fix {A : Type*} [AddGroup A] (P : A) (N n : ℕ) (hNP : N • P = 0)
    (hn : n ≡ 1 [MOD N]) : n • P = P := by
  have h1 : n ≡ 1 [MOD addOrderOf P] := hn.of_dvd (addOrderOf_dvd_of_nsmul_eq_zero hNP)
  have h2 := nsmul_eq_nsmul_iff_modEq.mpr h1
  simpa using h2

theorem tor_norm_mult_lt (N : ℕ) (hN0 : 0 < N) : ‖((l ^ N.totient : ℕ) : ℂ_[l])‖ < 1 := by
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [Nat.cast_pow, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hl (Nat.totient_pos.mpr hN0).ne'

theorem tor_x_step (h : GoodPair l g2 g3) (P Q : (shortW g2 g3).toAffine.Point) (N : ℕ)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (h2 : P + P ≠ 0) (hD : InFormalGroupPoints (P - Q)) (n : ℕ)
    (hn : n ≡ 1 [MOD N]) : ‖px _ P - px _ (n • Q)‖ ≤ ‖uOf (n • (P - Q))‖ := by
  obtain ⟨hW, hΔ⟩ := good_model h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hfix : n • P = P := tor_nsmul_fix P N n hNP hn
  have hsub : P - n • Q = n • (P - Q) := by
    rw [nsmul_sub, hfix]
  have hB : n • Q = P - n • (P - Q) := by
    rw [← hsub]; abel
  have hE : InFormalGroupPoints (n • (P - Q)) := (formalGroup_nsmul_estimate _ hW hΔ _ hD n).1
  by_cases h0 : n • (P - Q) = 0
  · have : n • Q = P := by rw [hB, h0, sub_zero]
    rw [this, sub_self, norm_zero]
    exact norm_nonneg _
  have hPE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P N hN hNP hP0
  have hBE : ¬ InFormalGroupPoints (n • Q) := by
    rw [hB]; exact not_mem_formalGroup_sub h P _ hPE hE
  have h2E : ¬ InFormalGroupPoints (P + P) :=
    torsion_not_mem_formalGroup h (P + P) N hN (by rw [nsmul_add, hNP, add_zero]) h2
  have hS : P + n • Q = (P + P) - n • (P - Q) := by
    rw [hB]; abel
  have hSE : ¬ InFormalGroupPoints (P + n • Q) := by
    rw [hS]; exact not_mem_formalGroup_sub h _ _ h2E hE
  obtain ⟨_, _, hPy⟩ := integral_of_not_mem_formalGroup h P hPE
  obtain ⟨hB0, _, hBy⟩ := integral_of_not_mem_formalGroup h _ hBE
  obtain ⟨hS0, hSx, _⟩ := integral_of_not_mem_formalGroup h _ hSE
  have := norm_x_sub_le_of_formalGroup (shortW g2 g3) rfl rfl rfl hW P (n • Q) hP0 hB0 hPy hBy hS0 hSx
    (by rw [hsub]; exact h0) (by rw [hsub]; exact hE)
  rwa [hsub] at this

theorem tor_x_mem (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN0 : 0 < N)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (h2 : P + P ≠ 0) : px _ P ∈ MaximalUnramifiedExtension l := by
  obtain ⟨hW, hΔ⟩ := good_model h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hPE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P N hN hNP hP0
  obtain ⟨_, hPx, _⟩ := integral_of_not_mem_formalGroup h P hPE
  obtain ⟨Q, hQ, hD⟩ := tor_lift h P hP0 hPx (tor_y_unit h P N hN hNP h2)
  have hcop : Nat.Coprime l N := ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hN
  have hM : ∀ k : ℕ, (l ^ N.totient) ^ k ≡ 1 [MOD N] := fun k => by
    simpa using (Nat.ModEq.pow_totient hcop).pow k
  have ht := formalGroup_pow_tendsto_zero _ hW hΔ _ hD (l ^ N.totient) (tor_norm_mult_lt N hN0)
  have hlim : Filter.Tendsto (fun k : ℕ => px _ ((l ^ N.totient) ^ k • Q)) Filter.atTop
      (nhds (px _ P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) ht
    rw [norm_sub_rev]
    exact tor_x_step h P Q N hN hNP h2 hD _ (hM k)
  have hcl : IsClosed ((MaximalUnramifiedExtension l : Subfield ℂ_[l]) : Set ℂ_[l]) :=
    Subfield.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
  exact (inSub_px _ _ _ (inSub_nsmul _ _ (good_coeff h) _ Q hQ)).1

theorem tor_kur (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN0 : 0 < N)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (hP0 : P ≠ 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  by_cases h2 : P + P = 0
  · exact tor_two h P hP0 h2
  have hx := tor_x_mem h P N hN0 hN hNP h2
  have hy := tor_y_unit h P N hN hNP h2
  refine ⟨hx, ?_⟩
  have hl : l ≠ 2 := by have := h.five; omega
  have heq : (py _ P) ^ 2 = (px _ P) ^ 3 - g2 / 4 * px _ P - g3 / 4 := by
    match P, hP0 with
    | .zero, hP0 => exact absurd rfl hP0
    | .some x y hxy, _ =>
      have := (Affine.equation_iff _ _).mp hxy.1
      simp only [shortW, px, py] at this ⊢
      linear_combination this
  have h4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
  refine sqrt_mem l hl _ _ ?_ hy heq
  exact sub_mem (sub_mem (pow_mem hx 3) (mul_mem (div_mem h.mem2 h4) hx)) (div_mem h.mem3 h4)

end ReciprocityTheory.ChartRestriction.L1
end
end

