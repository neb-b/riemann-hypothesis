module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Mathlib
public import Lemmata.PowerApplication.PowApp
public import Lemmata.MiscLemmasP.Imports

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.AntiEIsGlRep
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def antiE (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => -E (Fin.rev b) (Fin.rev a)

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompA
section
noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS

section
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

def dc_cplxPts (B : Finset ℝ) : Finset ℂ := B.image (fun b : ℝ => (b : ℂ))

theorem dc_injOn_id_cplx (B : Finset ℝ) : Set.InjOn (id : ℂ → ℂ) (dc_cplxPts B : Set ℂ) :=
  fun _ _ _ _ h => h

theorem dc_mem_cplxPts {B : Finset ℝ} {z : ℂ} : z ∈ dc_cplxPts B ↔ ∃ b ∈ B, (b : ℂ) = z := by
  simp [dc_cplxPts]

theorem dc_aeval_eigen {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by
  first | exact Bl.PowerApplication.goal1 .. | (apply Bl.PowerApplication.goal1 <;> assumption) | (intros; apply Bl.PowerApplication.goal1 <;> assumption)

theorem dc_X_sub_mul_basis {s : Finset ℂ} {z : ℂ} (hz : z ∈ s) :
    (X - C z) * Lagrange.basis s id z = C (Lagrange.nodalWeight s id z) * Lagrange.nodal s id := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hz, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero z) (Lagrange.X_sub_C_dvd_nodal id hz)

variable {T : Module.End ℂ Y} {S : Submodule ℂ Y} {B : Finset ℝ}

theorem dc_aeval_mem (hT : ∀ f ∈ S, T f ∈ S) (p : ℂ[X]) : ∀ f ∈ S, aeval T p f ∈ S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro f hf; simpa using S.add_mem (hp f hf) (hq f hf)
  | monomial k a =>
    intro f hf
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine S.smul_mem _ ?_
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih

theorem dc_basis_eigen (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) {z : ℂ}
    (hz : z ∈ dc_cplxPts B) : ∀ f ∈ S, T (aeval T (Lagrange.basis (dc_cplxPts B) id z) f) =
      z • aeval T (Lagrange.basis (dc_cplxPts B) id z) f := by
  intro f hf
  have h := congrArg (fun p => aeval T p f) (dc_X_sub_mul_basis hz)
  simp only [map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply, hP f hf, map_zero] at h
  exact sub_eq_zero.mp h

theorem dc_eq_zero_of_eigen_not_mem (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0)
    {z : ℂ} (hz : z ∉ dc_cplxPts B) {f : Y} (hf : f ∈ S) (he : T f = z • f) : f = 0 := by
  have h := hP f hf
  rw [dc_aeval_eigen he] at h
  refine (smul_eq_zero.mp h).resolve_left ?_
  rw [Lagrange.eval_nodal]
  exact Finset.prod_ne_zero_iff.mpr fun w hw h0 => hz (by simpa [sub_eq_zero] using (sub_eq_zero.mp h0) ▸ hw)

theorem dc_lagrange_decomp (hT : ∀ f ∈ S, T f ∈ S)
    (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) :
    ∀ f ∈ S, ∃ fb : ℝ → Y, (∀ b, fb b ∈ S ∧ T (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b := by
  classical
  intro f hf
  refine ⟨fun b => if b ∈ B then aeval T (Lagrange.basis (dc_cplxPts B) id (b : ℂ)) f else 0, fun b => ?_, ?_⟩
  · by_cases hb : b ∈ B
    · simp only [hb, if_true]
      exact ⟨dc_aeval_mem hT _ f hf, dc_basis_eigen hP (dc_mem_cplxPts.mpr ⟨b, hb, rfl⟩) f hf⟩
    · simp [hb]
  · rcases B.eq_empty_or_nonempty with hB | hB
    · subst hB
      have := hP f hf
      simpa [dc_cplxPts, Lagrange.nodal] using this
    · rw [Finset.sum_congr rfl fun b hb => if_pos hb]
      have hs : (dc_cplxPts B).Nonempty := hB.image _
      have h1 := Lagrange.sum_basis (dc_injOn_id_cplx B) hs
      have h2 : ∑ b ∈ B, aeval T (Lagrange.basis (dc_cplxPts B) id (b : ℂ)) f =
          ∑ z ∈ dc_cplxPts B, aeval T (Lagrange.basis (dc_cplxPts B) id z) f := by
        rw [dc_cplxPts, Finset.sum_image fun x _ y _ h => Complex.ofReal_injective h]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h2, ← LinearMap.sum_apply, ← map_sum, h1, map_one, Module.End.one_apply]

theorem dc_lagrange_eig (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) :
    ∀ z : ℂ, ∀ f ∈ S, f ≠ 0 → T f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ) := by
  intro z f hf h0 he
  by_contra hno
  refine h0 (dc_eq_zero_of_eigen_not_mem hP (fun hz => hno ?_) hf he)
  obtain ⟨b, hb, e⟩ := dc_mem_cplxPts.mp hz
  exact ⟨b, hb, e.symm⟩

def dc_lagProj (T : Module.End ℂ Y) (B : Finset ℝ) (z : ℂ) : Module.End ℂ Y :=
  if z ∈ dc_cplxPts B then aeval T (Lagrange.basis (dc_cplxPts B) id z) else 0

theorem dc_lagProj_props (hT : ∀ f ∈ S, T f ∈ S)
    (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) (z : ℂ) :
    (∀ f ∈ S, dc_lagProj T B z (dc_lagProj T B z f) = dc_lagProj T B z f) ∧
      (∀ f ∈ S, T (dc_lagProj T B z f) = z • dc_lagProj T B z f) ∧
      (∀ f ∈ S, T f = z • f → dc_lagProj T B z f = f) ∧
      ∀ f ∈ S, ∀ z' : ℂ, z' ≠ z → T f = z' • f → dc_lagProj T B z f = 0 := by
  classical
  by_cases hz : z ∈ dc_cplxPts B
  · simp only [dc_lagProj, hz, if_true]
    refine ⟨fun f hf => ?_, dc_basis_eigen hP hz, fun f hf he => ?_, fun f hf z' hz' he => ?_⟩
    · rw [dc_aeval_eigen (dc_basis_eigen hP hz f hf)]
      have := Lagrange.eval_basis_self (v := id) (dc_injOn_id_cplx B) hz
      simp only [id] at this
      rw [this, one_smul]
    · rw [dc_aeval_eigen he]
      have := Lagrange.eval_basis_self (v := id) (dc_injOn_id_cplx B) hz
      simp only [id] at this
      rw [this, one_smul]
    · by_cases hz'' : z' ∈ dc_cplxPts B
      · rw [dc_aeval_eigen he]
        have := Lagrange.eval_basis_of_ne (v := id) (s := dc_cplxPts B) (Ne.symm hz') hz''
        simp only [id] at this
        rw [this, zero_smul]
      · rw [dc_eq_zero_of_eigen_not_mem hP hz'' hf he, map_zero]
  · simp only [dc_lagProj, hz, if_false, LinearMap.zero_apply]
    refine ⟨fun _ _ => trivial, fun _ _ => by simp, fun f hf he => (dc_eq_zero_of_eigen_not_mem hP hz hf he).symm,
      fun _ _ _ _ _ => trivial⟩

end

end ReciprocityTheory.ChartRestriction.DS

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS

section
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {S W : Submodule ℂ Y}
  {Q : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ}

theorem dc_symm_eig_real (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) {u : Y} (hu : u ∈ S) (hu0 : u ≠ 0) {μ : ℂ}
    (he : T u = μ • u) : (μ.re : ℂ) = μ := by
  have h := hsym u hu u hu
  rw [he, LinearMap.map_smulₛₗ, LinearMap.smul_apply, (Q u).map_smul, smul_eq_mul, smul_eq_mul] at h
  have hq : Q u u ≠ 0 := fun h0 => by have := hpos u hu hu0; rw [h0] at this; simp at this
  have h2 : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hq h
  exact Complex.conj_eq_iff_re.mp h2

theorem dc_symm_semisimple (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) (hTS : ∀ f ∈ S, T f ∈ S) (μ : ℂ) :
    ∀ k : ℕ, ∀ x ∈ S, ((T - μ • 1) ^ k) x = 0 → T x = μ • x := by
  intro k
  induction k with
  | zero => intro x _ hx; simp at hx; simp [hx]
  | succ k ih =>
    intro x hx h
    set u := T x - μ • x with hu
    have huS : u ∈ S := S.sub_mem (hTS x hx) (S.smul_mem μ hx)
    have hk : ((T - μ • 1) ^ k) u = 0 := by
      rw [pow_succ, Module.End.mul_apply] at h
      simpa [hu] using h
    have hue : T u = μ • u := ih u huS hk
    by_contra hne
    have hu0 : u ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
    have hr := dc_symm_eig_real hpos hsym huS hu0 hue
    have h1 : Q u u = 0 := by
      have e1 : Q u u = Q (T x) u - Q (μ • x) u := by
        rw [← LinearMap.sub_apply, ← Q.map_sub]
      rw [e1, hsym x hx u huS, hue, (Q x).map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul]
      rw [← hr]; simp
    have := hpos u huS hu0
    rw [h1] at this; simp at this

theorem dc_symm_nodal (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) (hTS : ∀ f ∈ S, T f ∈ S) (hWS : W ≤ S)
    (hW : FiniteDimensional ℂ W) (hTW : ∀ f ∈ W, T f ∈ W) :
    ∃ B : Finset ℝ, ∀ w ∈ W, aeval T (Lagrange.nodal (dc_cplxPts B) id) w = 0 := by
  classical
  set T' : Module.End ℂ W := T.restrict hTW with hT'
  have hfin := Module.End.finite_hasEigenvalue T'
  refine ⟨hfin.toFinset.image Complex.re, fun w hw => ?_⟩
  have key : ∀ μ : ℂ, ∀ x ∈ T'.maxGenEigenspace μ, aeval T (Lagrange.nodal (dc_cplxPts (hfin.toFinset.image Complex.re)) id) (x : Y) = 0 := by
    intro μ x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T' μ x).mp hx
    have hk' : ((T - μ • 1) ^ k) (x : Y) = 0 := by
      have : ∀ j : ℕ, (((T' - μ • 1) ^ j) x : Y) = ((T - μ • 1) ^ j) (x : Y) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]; simp [hT']
      rw [← this, hk]; simp
    have he := dc_symm_semisimple hpos hsym hTS μ k (x : Y) (hWS x.2) hk'
    by_cases hx0 : (x : Y) = 0
    · rw [hx0, map_zero]
    have hr := dc_symm_eig_real hpos hsym (hWS x.2) hx0 he
    rw [dc_aeval_eigen he, Lagrange.eval_nodal]
    have hmem : μ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, fun h => hx0 (by simp [h])⟩
      rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa [hT'] using he)
    have : μ ∈ dc_cplxPts (hfin.toFinset.image Complex.re) :=
      dc_mem_cplxPts.mpr ⟨μ.re, Finset.mem_image_of_mem _ hmem, hr⟩
    rw [Finset.prod_eq_zero this (by simp), zero_smul]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top T'
  have gen : ∀ y : W, y ∈ ⨆ μ, T'.maxGenEigenspace μ →
      aeval T (Lagrange.nodal (dc_cplxPts (hfin.toFinset.image Complex.re)) id) (y : Y) = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem μ x hx => exact key μ x hx
    | zero => simp
    | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
  exact gen ⟨w, hw⟩ (by rw [htop]; trivial)

end

end ReciprocityTheory.ChartRestriction.DS

end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Gelfand
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def ePow (E : Fin n → Fin n → Module.End ℂ M) : ℕ → Fin n → Fin n → Module.End ℂ M :=
  Bl.ThirdBlockLemmaA.goal1 E

def gelfand (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) : Module.End ℂ M :=
  ∑ a, ePow E k a a

theorem commutator_mul_right (X Y Z : Module.End ℂ M) :
    X * (Y * Z) - Y * Z * X = (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
  noncomm_ring

theorem ePow_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    E a b * ePow E k c d - ePow E k c d * E a b =
      (if b = c then ePow E k a d else 0) - (if d = a then ePow E k c b else 0) := by
  have hz : ∀ c d, ePow E 0 c d = if c = d then 1 else 0 := fun c d => rfl
  have hs : ∀ k c d, ePow E (k + 1) c d = ∑ e, E c e * ePow E k e d := by
    intro k c d
    unfold ePow Bl.ThirdBlockLemmaA.goal1
    simp [pow_succ', Matrix.mul_apply]
  induction k generalizing c d with
  | zero =>
    simp only [hz]
    split_ifs <;> subst_vars <;> simp_all
  | succ k ih =>
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [commutator_mul_right, hE a b c, ih]
    by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp [hbc, hda, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc] <;> abel

theorem gelfand_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b : Fin n) :
    E a b * gelfand E k = gelfand E k * E a b := by
  have h : E a b * gelfand E k - gelfand E k * E a b = 0 := by
    unfold gelfand
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [ePow_comm hE]
    simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  exact sub_eq_zero.mp h

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.KernelLemma
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def oppCount (ε : Fin n → Bool) (a : Fin n) : ℕ := (univ.filter fun b => ε b ≠ ε a).card

theorem dot_root_right (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_boole]

theorem dot_sum_root_right (u : Fin n → ℝ) (Ph : Finset (Fin n × Fin n)) :
    dot u (∑ x ∈ Ph, root x.1 x.2) = ∑ x ∈ Ph, (u x.1 - u x.2) := by
  have h := fun x : Fin n × Fin n => dot_root_right u x.1 x.2
  simp only [dot] at h ⊢
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => h x

theorem oppCount_add (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) :
    (oppCount ε a : ℝ) + oppCount ε b = n := by
  have key : oppCount ε a + oppCount ε b = n := by
    unfold oppCount
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n, ((if ε c ≠ ε a then 1 else 0) + (if ε c ≠ ε b then 1 else 0) : ℕ) = 1 := by
      intro c
      revert hab
      cases ε a <;> cases ε b <;> cases ε c <;> simp
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact_mod_cast key

theorem sum_root_apply (Ph : Finset (Fin n × Fin n)) (c : Fin n) :
    (∑ x ∈ Ph, root x.1 x.2) c =
      ((Ph.filter fun x => x.1 = c).card : ℝ) - ((Ph.filter fun x => x.2 = c).card : ℝ) := by
  rw [Finset.sum_apply]
  simp only [root, Pi.sub_apply, Finset.sum_sub_distrib, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.1 = c
    · rw [h]; simp
    · have h' : ¬ c = x.1 := fun e => h e.symm
      simp [Pi.single_apply, h, h']
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.2 = c
    · rw [h]; simp
    · have h' : ¬ c = x.2 := fun e => h e.symm
      simp [Pi.single_apply, h, h']

theorem card_fst_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (c : Fin n) :
    (Ph.filter fun x => x.1 = c).card ≤ oppCount ε c := by
  unfold oppCount
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 := hnc x hx.1
    rw [hx.2] at h1
    exact Ne.symm h1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy

theorem card_snd_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (c : Fin n) :
    (Ph.filter fun x => x.2 = c).card ≤ oppCount ε c := by
  unfold oppCount
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 := hnc x hx.1
    rw [hx.2] at h1
    exact h1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext hxy (hx.2.trans hy.2.symm)

theorem nsq_sum_root_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) :
    nsq (∑ x ∈ Ph, root x.1 x.2) ≤ n * Ph.card := by
  have hpt : ∀ c, (∑ x ∈ Ph, root x.1 x.2) c * (∑ x ∈ Ph, root x.1 x.2) c ≤
      (((Ph.filter fun x => x.1 = c).card : ℝ) + ((Ph.filter fun x => x.2 = c).card : ℝ)) *
        (oppCount ε c : ℝ) := by
    intro c
    rw [sum_root_apply]
    have h1 : ((Ph.filter fun x => x.1 = c).card : ℝ) ≤ oppCount ε c := by
      exact_mod_cast card_fst_le ε Ph hnc c
    have h2 : ((Ph.filter fun x => x.2 = c).card : ℝ) ≤ oppCount ε c := by
      exact_mod_cast card_snd_le ε Ph hnc c
    have h3 : (0 : ℝ) ≤ ((Ph.filter fun x => x.1 = c).card : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((Ph.filter fun x => x.2 = c).card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h3 h4, mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h4]
  have hfib : ∀ g : Fin n × Fin n → Fin n,
      ∑ c, ((Ph.filter fun x => g x = c).card : ℝ) * (oppCount ε c : ℝ) =
        ∑ x ∈ Ph, (oppCount ε (g x) : ℝ) := by
    intro g
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  calc nsq (∑ x ∈ Ph, root x.1 x.2)
        = ∑ c, (∑ x ∈ Ph, root x.1 x.2) c * (∑ x ∈ Ph, root x.1 x.2) c := rfl
    _ ≤ ∑ c, (((Ph.filter fun x => x.1 = c).card : ℝ) + ((Ph.filter fun x => x.2 = c).card : ℝ)) *
          (oppCount ε c : ℝ) := Finset.sum_le_sum fun c _ => hpt c
    _ = ∑ c, ((Ph.filter fun x => x.1 = c).card : ℝ) * (oppCount ε c : ℝ) +
          ∑ c, ((Ph.filter fun x => x.2 = c).card : ℝ) * (oppCount ε c : ℝ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ x ∈ Ph, (oppCount ε x.1 : ℝ) + ∑ x ∈ Ph, (oppCount ε x.2 : ℝ) := by
        rw [hfib Prod.fst, hfib Prod.snd]
    _ = ∑ x ∈ Ph, (n : ℝ) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x hx => oppCount_add ε (hnc x hx)
    _ = n * Ph.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem kernel_lemma (ε : Fin n → Bool) (μ : Fin n → ℝ) {h : ℝ} (_hh : 0 < h) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (hpos : ∀ x ∈ Ph, h ≤ μ x.1 - μ x.2) :
    nsq (μ - ∑ x ∈ Ph, root x.1 x.2) ≤ nsq μ - (2 * h - n) * Ph.card := by
  have hexp : nsq (μ - ∑ x ∈ Ph, root x.1 x.2) =
      nsq μ - 2 * dot μ (∑ x ∈ Ph, root x.1 x.2) + nsq (∑ x ∈ Ph, root x.1 x.2) := by
    simp only [nsq, dot, Pi.sub_apply, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hd : h * Ph.card ≤ dot μ (∑ x ∈ Ph, root x.1 x.2) := by
    rw [dot_sum_root_right]
    have h2 : ∑ _x ∈ Ph, h ≤ ∑ x ∈ Ph, (μ x.1 - μ x.2) := Finset.sum_le_sum fun x hx => hpos x hx
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    linarith
  have hn := nsq_sum_root_le ε Ph hnc
  rw [hexp]
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

