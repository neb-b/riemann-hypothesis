module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepHomog

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {v : Ω} (hv : v ∈ chartLat y a 1) (e : ℕ) :
    v ^ e ∈ chartLat y a e := by
  induction e with
  | zero => intro c _; simp
  | succ e ih => rw [pow_succ]; exact mul_mem ih hv

abbrev forms {q : ℕ} (w : Fin q → Ω) (e : ℕ) : AddSubgroup Ω :=
  gradedSpan w (fun _ : Fin 1 => 0) (fun _ => 1) e

theorem mul_forms_mem {q r : ℕ} {w : Fin q → Ω} {d : Fin r → ℕ} {t : Fin r → Ω} {N e : ℕ} {x f : Ω}
    (hx : x ∈ gradedSpan w d t N) (hf : f ∈ forms w e) : x * f ∈ gradedSpan w d t (N + e) := by
  have hmono : ∀ μ : Fin q → ℕ, x * ∏ i, w i ^ μ i ∈ gradedSpan w d t (N + ∑ i, μ i) := by
    intro μ
    induction hx using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, ν, hν, rfl⟩ := hz
      have h := gradedSpan_gen_mem w d t l (ν + μ)
      have hdeg : d l + ∑ i, (ν + μ) i = N + ∑ i, μ i := by
        rw [← hν]; simp [Finset.sum_add_distrib, add_assoc]
      have hval : t l * ∏ i, w i ^ (ν + μ) i = t l * (∏ i, w i ^ ν i) * ∏ i, w i ^ μ i := by
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]; ring
      rwa [hdeg, hval] at h
    | zero => rw [zero_mul]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [add_mul]; exact add_mem hz hz'
    | neg z _ hz => rw [neg_mul]; exact neg_mem hz
  induction hf using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨l, μ, hμ, rfl⟩ := hz
    have h := hmono μ
    rwa [one_mul, ← hμ, zero_add]
  | zero => rw [mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [mul_neg]; exact neg_mem hz

theorem one_mem_forms {q : ℕ} (w : Fin q → Ω) : (1 : Ω) ∈ forms w 0 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (fun _ => 0)
  simpa using h

theorem mem_forms_one {q : ℕ} (w : Fin q → Ω) (i : Fin q) : w i ∈ forms w 1 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (Pi.single i 1)
  simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using h

theorem pow_mem_forms {q : ℕ} (w : Fin q → Ω) (i : Fin q) (e : ℕ) : w i ^ e ∈ forms w e := by
  induction e with
  | zero => simpa using one_mem_forms w
  | succ e ih => rw [pow_succ]; exact mul_forms_mem ih (mem_forms_one w i)

theorem exists_mul_pow_mem_forms {q : ℕ} {w : Fin q → Ω} {j : Fin q} (hj : w j ≠ 0) {c : Ω}
    (hc : c ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) : ∃ E : ℕ, c * w j ^ E ∈ forms w E := by
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hj]
    exact mem_forms_one w i
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, algebraMap_int_eq, eq_intCast, ← zsmul_one]
    exact zsmul_mem (one_mem_forms w) r
  | add x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    have h1 := mul_forms_mem hE (pow_mem_forms w j E')
    have h2 := mul_forms_mem hE' (pow_mem_forms w j E)
    rw [add_comm E' E] at h2
    rw [show (x + x') * w j ^ (E + E') = x * w j ^ E * w j ^ E' + x' * w j ^ E' * w j ^ E by ring]
    exact add_mem h1 h2
  | mul x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    rw [show x * x' * w j ^ (E + E') = x * w j ^ E * (x' * w j ^ E') by ring]
    exact mul_forms_mem hE hE'

theorem mul_pow_mem_forms_of_le {q : ℕ} {w : Fin q → Ω} {j : Fin q} {c : Ω} {E E' : ℕ}
    (h : c * w j ^ E ∈ forms w E) (hle : E ≤ E') : c * w j ^ E' ∈ forms w E' := by
  have h' := mul_forms_mem h (pow_mem_forms w j (E' - E))
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle] at h'

end SpanStepHomog


open SpanStepHomog in
theorem SpanStepHomog.proof (hL : SpanStepLocal.Statement) : SpanStepHomog.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  have H : ∀ j, ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      (w j ≠ 0 → ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧
          g = ∑ l, c l * b l) := by
    intro j
    by_cases hj : w j = 0
    · exact ⟨0, Fin.elim0, fun l => l.elim0, fun h => (h hj).elim⟩
    · obtain ⟨r, b, h1, h2⟩ := hL K ι Ω y a q w hy hw hgen j hj
      exact ⟨r, b, h1, fun _ => h2⟩
  choose r b hb hspan using H
  choose nb hnb using hb
  set m := ∑ j, ∑ l, nb j l with hm
  have hle : ∀ j l, nb j l ≤ m := fun j l =>
    (Finset.single_le_sum (f := nb j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j => ∑ l, nb j l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  let e := Fintype.equivFin (Σ j, Fin (r j))
  let T : (Σ j, Fin (r j)) → Ω := fun p => b p.1 p.2 * w p.1 ^ m
  let t : Fin (Fintype.card (Σ j, Fin (r j))) → Ω := fun i => T (e.symm i)
  have htv : ∀ j l, t (e ⟨j, l⟩) = b j l * w j ^ m := fun j l => by
    show T (e.symm (e ⟨j, l⟩)) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨m, _, t, fun i => ?_, fun n s hs j hj => ?_⟩
  · have h := mul_mem (hnb (e.symm i).1 (e.symm i).2) (pow_mem (hw (e.symm i).1) (m - nb (e.symm i).1 (e.symm i).2))
    rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' (hle _ _)] at h
  have hwn : w j ^ n ≠ 0 := pow_ne_zero n hj
  obtain ⟨c, hc, hg⟩ := hspan j hj (s / w j ^ n) n (by rwa [div_mul_cancel₀ _ hwn])
  choose E hE using fun l => exists_mul_pow_mem_forms hj (hc l)
  refine ⟨m + ∑ l, E l, ?_⟩
  have hs' : s * w j ^ (m + ∑ l, E l) =
      ∑ l, t (e ⟨j, l⟩) * (c l * w j ^ (∑ l, E l)) * w j ^ n := by
    rw [show s = s / w j ^ n * w j ^ n by rw [div_mul_cancel₀ _ hwn], hg, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [htv, pow_add]; ring
  rw [hs', show n + (m + ∑ l, E l) = m + ∑ l, E l + n by ring]
  refine sum_mem fun l _ => mul_forms_mem (mul_forms_mem ?_ (mul_pow_mem_forms_of_le (hE l)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)))) (pow_mem_forms w j n)
  have h := gradedSpan_gen_mem w (fun _ => m) t (e ⟨j, l⟩) (fun _ => 0)
  simpa using h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepLocal

def powMulSub {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω) (v : Ω) (hv : v ∈ R) : Subalgebra ℤ Ω where
  carrier := {x | ∃ E : ℕ, x * v ^ E ∈ R}
  mul_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : x * z * v ^ (E₁ + E₂) = (x * v ^ E₁) * (z * v ^ E₂) := by ring
    rw [e]; exact R.mul_mem h₁ h₂
  add_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : (x + z) * v ^ (E₁ + E₂) = (x * v ^ E₁) * v ^ E₂ + (z * v ^ E₂) * v ^ E₁ := by ring
    rw [e]; exact R.add_mem (R.mul_mem h₁ (R.pow_mem hv _)) (R.mul_mem h₂ (R.pow_mem hv _))
  algebraMap_mem' r := ⟨0, by rw [pow_zero, mul_one]; exact R.algebraMap_mem r⟩

theorem pow_twist {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (c : ∀ k, ι k) (g w : Ω) (n : ℕ) :
    g * w ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) = g * (w * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ n := by
  rw [mul_pow, ← Finset.prod_pow, mul_assoc]
  congr 3; funext k
  rw [← zpow_natCast, ← zpow_mul]; ring_nf

end SpanStepLocal


open SpanStepLocal in
theorem SpanStepLocal.proof (hR : RelLatticeFinite.Statement) : SpanStepLocal.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen j hj
  classical
  set P := Algebra.adjoin ℤ (Set.range fun i => w i / w j) with hPdef

  set v : (∀ k, ι k) → Fin q → Ω := fun c i => w i * ∏ k, y ⟨k, c k⟩ ^ (-a k) with hvdef
  have hv : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ i, v c i ∈ chartRingZ y c := fun c hc i => by
    simpa [hvdef] using hw i c hc
  have hv0 : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → v c j ≠ 0 := fun c hc =>
    mul_ne_zero hj (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
  have hquot : ∀ c i, w i / w j * v c j = v c i := fun c i => by
    simp only [hvdef]; rw [← mul_assoc, div_mul_cancel₀ _ hj]
  have hrel : ∀ (g : Ω) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (g ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ↔
      g * ∏ k, y ⟨k, c k⟩ ^ (-(((0 : ℕ) : ℤ) * (fun _ => (0 : ℤ)) k)) ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) := fun g c _ => by simp

  have incl₁ : ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n → g ∈ relChartLat P y (fun _ => 0) 0 := by
    intro g n hg c hc
    rw [← hrel g c hc]
    set S := Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
    have hRS : ∀ x ∈ chartRingZ y c, x ∈ S := fun x hx =>
      (Algebra.adjoin_le Algebra.subset_adjoin : chartRingZ y c ≤ S.restrictScalars ℤ) hx
    have hPS : ∀ x ∈ P, x ∈ S := fun x hx => S.algebraMap_mem (⟨x, hx⟩ : P)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hinv : (∑ i, u i * (w i / w j)) = (v c j)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, hquot]
    have hinvS : (v c j)⁻¹ ∈ S := hinv ▸ S.sum_mem fun i _ =>
      S.mul_mem (hRS _ (hu i)) (hPS _ (Algebra.subset_adjoin ⟨i, rfl⟩))
    have hgv : g * v c j ^ n ∈ S := hRS _ (by rw [← pow_twist]; exact hg c hc)
    have e : g = g * v c j ^ n * (v c j)⁻¹ ^ n := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (hv0 c hc), one_pow, mul_one]
    rw [e]; exact S.mul_mem hgv (S.pow_mem hinvS n)
  have incl₂ : ∀ g ∈ relChartLat P y (fun _ => 0) 0, ∃ n : ℕ, g * w j ^ n ∈ chartLat y a n := by
    intro g hg
    have hE : ∀ c, ∃ E : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → g * v c j ^ E ∈ chartRingZ y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      swap; · exact ⟨0, fun h => absurd h hc⟩
      have hgS := (hrel g c hc).2 (hg c hc)
      have hg' : g ∈ Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
        rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact hgS
      have hle : Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ≤ powMulSub _ _ (hv c hc j) := by
        refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
        · rintro _ ⟨i, rfl⟩; exact ⟨1, by rw [pow_one, hquot]; exact hv c hc i⟩
        · rintro _ ⟨p, rfl⟩; exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨p, rfl⟩⟩
      obtain ⟨E, hE⟩ := hle hg'
      exact ⟨E, fun _ => hE⟩
    choose E hE using hE
    refine ⟨∑ c, E c, fun c hc => ?_⟩
    rw [pow_twist]
    have e : g * v c j ^ (∑ c, E c) = g * v c j ^ E c * v c j ^ (∑ c, E c - E c) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))]
    rw [e]; exact (chartRingZ y c).mul_mem (hE c hc) ((chartRingZ y c).pow_mem (hv c hc j) _)

  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hR K ι Ω y (fun _ => 0) 0 q (fun i => w i / w j) hy)
  have hbmem : ∀ l, b l ∈ relChartLat P y (fun _ => 0) 0 := fun l =>
    hb ▸ Submodule.subset_span ⟨l, rfl⟩
  refine ⟨r, b, fun l => incl₂ _ (hbmem l), fun g n hg => ?_⟩
  have hgN := incl₁ g n hg
  rw [← hb, Submodule.mem_span_range_iff_exists_fun] at hgN
  obtain ⟨c, hc⟩ := hgN
  exact ⟨fun l => (c l : Ω), fun l => (c l).2, by rw [← hc]; rfl⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SupBoundBlock.eval_torus_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      c k₀ ^ n * eval z (map (Int.castRingHom ℂ) f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem SupBoundBlock.normRatio_torus {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hA : A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z (map (Int.castRingHom ℂ) f)‖ / A.h z ^ n = ‖eval z' (map (Int.castRingHom ℂ) f)‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [SupBoundBlock.eval_torus_blockDeg hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, hk]]
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem SupBoundBlock.isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem SupBoundBlock.proof (hS : SupNormAgainstL2.Statement) (hR : ResolutionPullback.Statement)
    (hN : NonvanishingDense.Statement) : SupBoundBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨A, L, W, dV, -, hW, hμ, hsec⟩ := hR D K ι Ω d
  obtain ⟨⟨C, hC⟩, -⟩ := hS A L W dV hW
  refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w (map (Int.castRingHom ℂ) f)‖ / d.A.h w ^ n with hg
  set M := max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f with hM
  obtain ⟨s, hs, hps⟩ := hsec n f hf

  have hL2 : Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt 2 * blockL2Norm d n f := by
    have hI : sectionL2NormSq W dV n s = ∫ x, g (blockPt d x) ^ 2 ∂d.dV := by
      rw [sectionL2NormSq, hμ]
      exact integral_congr_ae (Eventually.of_forall hps)
    have h2 : 0 ≤ ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) f)‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV := integral_nonneg fun _ => sq_nonneg _
    rw [hI, blockL2Norm, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf

  have hres : ∀ x, g (blockPt d x) ≤ M := by
    intro x
    have h1 : g (blockPt d x) ≤ Real.sqrt (ptNormSq W n s x) := by
      rw [hps x, Real.sqrt_sq_eq_abs]
      exact le_abs_self _
    have h3 := hC n hn s hs x
    rw [hpow] at h3
    have ha : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc g (blockPt d x) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := h1.trans h3
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * blockL2Norm d n f) := by
          gcongr
      _ = M := by rw [hM]; ring

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (SupBoundBlock.normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hres x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField Filter Topology

theorem isOpen_multiconePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem leviForm_eq_of_eventuallyEq_add_const {κ : Type*} [Fintype κ] (φ ψ : (κ → ℂ) → ℝ) (c : ℝ)
    (z w : κ → ℂ) (h : ψ =ᶠ[𝓝 z] fun x => φ x + c) : leviForm ψ z w = leviForm φ z w := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 z] fderiv ℝ φ := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h1.fderiv_eq]

theorem TwistMetric.proof (hEW : EmbeddingWeight.Statement)
    (hTI : TwistIntersectionAnyDegree.Statement) : TwistMetric.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A P0 II u hD hII hY hbir _ hsemi hconj hlies hu hsum
  refine ⟨((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a, fun δ hδ => ?_⟩
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hEW K ι Ω F y (fun sg => Real.exp (u sg + δ))
    (fun _ => Real.exp_pos _) (fun sg => by simp only [hu]) hlies
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (F →+* ℂ) :=
      Fintype.card_pos_iff.mpr ⟨(IsAlgClosed.lift (R := ℚ) (S := F) (M := ℂ)).toRingHom⟩
    exact_mod_cast this.ne'
  refine ⟨A.tensor B, ?_, ?_, ?_, fun z hz sg hsg => ?_, ?_⟩
  · change A.a + B.a = A.a
    rw [hBa, add_zero]
  · unfold IsSemipositiveRel
    refine ⟨ContDiffOn.mul hsemi.1 hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := hlies z hz
    have hzA : ∀ᶠ x in 𝓝 z, A.h x ≠ 0 := by
      filter_upwards [isOpen_multiconePts.mem_nhds hz.1] with x hx using (A.pos x hx).ne'
    have heq : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Real.exp (u sg + δ)) := by
      filter_upwards [hzA, hBloc z hz sg hsg] with x hx hB
      change Real.log (A.h x * B.h x) = _
      rw [hB, Real.log_mul hx (Real.exp_pos _).ne']
    rw [leviForm_eq_of_eventuallyEq_add_const _ _ _ z w heq]
    exact hsemi.2 z hz w hw
  · intro z
    change A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  · change A.h z * B.h z = _
    rw [(hBloc z hz sg hsg).self_of_nhds, mul_comm]
  · rw [hTI K ι Ω F y D A B II (fun sg => Real.exp (u sg + δ)) hD hII hY hbir hsemi.1 hBa hBs
      (fun _ => Real.exp_pos _) hlies hBloc]
    have hs : (∑ sg, Real.log ((fun sg => Real.exp (u sg + δ)) sg)) / Fintype.card (F →+* ℂ) = δ := by
      simp only [Real.log_exp, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, zero_add]
      field_simp
    rw [hs]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRelLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreRelLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (ℓ : ℕ) (a : K → ℤ) (r : ℕ) (s : Fin r → Ω)
    (J : KH.Cell K ι 0)
    (u : Fin r → LocalizedModule (KH.cellMon (ZMod ℓ) J.1) (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))),
    (∀ j, s j ∈ chartLat y a 1) → (∀ k, y ⟨k, GenOnFibres.cellChart J k⟩ ≠ 0) →
    (∀ j, u j ∈ KH.locPart ι (KH.quotPart (ZMod ℓ) (GenOnFibres.idealOver y (ZMod ℓ))) (KH.cellMon (ZMod ℓ) J.1) (-a)) →
    ∑ j, u j * GenOnFibres.secCoch (y := y) (S := ZMod ℓ) (s j) a J = 1 →
    ∃ (u' : Fin r → Ω) (v : Ω), (∀ j, u' j ∈ chartRingZ y (GenOnFibres.cellChart J)) ∧
      v ∈ chartRingZ y (GenOnFibres.cellChart J) ∧
      ∑ j, u' j * (s j * ∏ k, y ⟨k, GenOnFibres.cellChart J k⟩ ^ (-a k)) + ℓ * v = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

