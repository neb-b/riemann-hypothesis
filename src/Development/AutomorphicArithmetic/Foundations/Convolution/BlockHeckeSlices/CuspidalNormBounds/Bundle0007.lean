module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatCons
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceHecke

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompCap
section
open NumberField

noncomputable section

namespace UpperTheory.ConvolutionTheory.BW

open GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin UpperTheory.V.Cm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

private theorem umg_range {A : Module.End ℂ (Sm E n)} (hA : A ∈ (uC E n).range) {φ : Sm E n} (hφ : Umg φ) :
    Umg (A φ) := by
  obtain ⟨u, rfl⟩ := hA
  exact ((umgOps E n).2 φ hφ).2.2.2.1 u

private def relAlg (b : Blo S r) (s : ℕ) (t : ℝ) :
    Subalgebra ℂ (Module.End ℂ (Sm E s) × Module.End ℂ (Sm E (r + s))) where
  carrier := {p | ∀ (φ : Sm E (r + s)) (ψ : Sm E s), Umg φ → ψ.1 = slice b.f.1 t φ.1 →
    Umg (p.2 φ) ∧ (p.1 ψ).1 = slice b.f.1 t (p.2 φ).1}
  mul_mem' := fun {p q} hp hq φ ψ hφ h => hp _ _ (hq φ ψ hφ h).1 (hq φ ψ hφ h).2
  add_mem' := fun {p q} hp hq φ ψ hφ h => by
    obtain ⟨p1, p2⟩ := hp φ ψ hφ h
    obtain ⟨q1, q2⟩ := hq φ ψ hφ h
    refine ⟨((umgOps E _).2 _ p1).2.1 _ q1, funext fun m => ?_⟩
    have := (sliceBound E S r s b).2 _ _ 1 p1 q1 t m
    rw [one_smul, one_mul, ← p2, ← q2] at this
    exact this.symm
  algebraMap_mem' := fun c φ ψ hφ h => by
    refine ⟨((umgOps E _).2 _ hφ).2.2.1 c, funext fun m => ?_⟩
    have := (sliceBound E S r s b).2 _ _ (c - 1) hφ hφ t m
    rw [← h, sub_smul, one_smul, sub_add_cancel, sub_mul, one_mul, sub_add_cancel] at this
    exact this.symm

private theorem eop_rel (b : Blo S r) (t : ℝ) (τ : E →+* ℂ) (i j : Fin s) :
    (Eop τ i j, Eop τ (Fin.natAdd r i) (Fin.natAdd r j)) ∈ relAlg b s t := fun φ ψ hφ h => by
  refine ⟨umg_range ⟨_, uC_genC _ _ _⟩ hφ, ?_⟩
  obtain ⟨ψ', h1, -, h2, -⟩ := sliceUmg E S r s b t φ hφ
  obtain rfl : ψ = ψ' := Subtype.ext (h.trans h1.symm)
  exact h2 τ i j

private theorem pair_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (R : Subalgebra ℂ (A × B)) {m : ℕ}
    (X : Fin m → Fin m → A) (Y : Fin m → Fin m → B) (h : ∀ i j, (X i j, Y i j) ∈ R) (u : ℂ) :
    (Formalism.REAL.qdet X u, Formalism.REAL.qdet Y u) ∈ R := by
  have h1 : Formalism.REAL.qdet (fun i j => (X i j, Y i j)) u ∈ R := by
    refine R.sum_mem fun σ _ => R.mul_mem (intCast_mem _ _) (R.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine R.add_mem ?_ (h _ _)
    split_ifs
    · exact R.algebraMap_mem _
    · exact R.zero_mem
  convert h1 using 1
  exact Prod.ext (UpperTheory.V.Fb.map_qdet (AlgHom.fst ℂ A B) (fun i j => (X i j, Y i j)) u).symm
    (UpperTheory.V.Fb.map_qdet (AlgHom.snd ℂ A B) (fun i j => (X i j, Y i j)) u).symm

private theorem pair_prod {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (R : Subalgebra ℂ (A × B)) {m : ℕ}
    (c : Fin m → ℂ) (X : Fin m → A) (Y : Fin m → B) (h : ∀ i, (X i, Y i) ∈ R) :
    ((List.ofFn fun i => algebraMap ℂ A (c i) + X i).prod, (List.ofFn fun i => algebraMap ℂ B (c i) + Y i).prod) ∈ R := by
  have h1 : (List.ofFn fun i => algebraMap ℂ (A × B) (c i) + (X i, Y i)).prod ∈ R := R.list_prod_mem fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact R.add_mem (R.algebraMap_mem _) (h i)
  convert h1 using 1
  refine Prod.ext ?_ ?_
  · refine Eq.trans ?_ (map_list_prod (RingHom.fst A B) _).symm
    rw [List.map_ofFn]
    rfl
  · refine Eq.trans ?_ (map_list_prod (RingHom.snd A B) _).symm
    rw [List.map_ofFn]
    rfl

private theorem pair_sum {A B I J : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (R : Subalgebra ℂ (A × B)) [Fintype I]
    (T : Finset J) (c : ℂ) (X : I → J → A) (Y : I → J → B) (h : ∀ i j, (X i j, Y i j) ∈ R) :
    (c • ∑ i, ∑ j ∈ T, X i j, c • ∑ i, ∑ j ∈ T, Y i j) ∈ R := by
  have h1 : c • ∑ i, ∑ j ∈ T, (X i j, Y i j) ∈ R := R.smul_mem (R.sum_mem fun i _ => R.sum_mem fun j _ => h i j) c
  convert h1 using 1
  simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_sum, Prod.snd_sum, and_self]

private theorem prod_mem_ofFn {A : Type} [Ring A] [Algebra ℂ A] (R : Subalgebra ℂ A) {m : ℕ} (X : Fin m → A) (h : ∀ i, X i ∈ R) :
    (List.ofFn X).prod ∈ R := R.list_prod_mem fun x hx => by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact h i

private theorem cap_rel (b : Blo S r) (t : ℝ) (τ : E →+* ℂ) (u : ℂ) :
    (cap τ u, capS r s τ u) ∈ relAlg b s t :=
  pair_qdet (relAlg b s t) (Eop τ) (fun i j => Eop τ (Fin.natAdd r i) (Fin.natAdd r j)) (eop_rel b t τ) (u + ((s : ℂ) - 1) / 2)

private def z0 (b : Blo S r) (d : Dat S s) : Fin (Dat.cons b d).len := (0 : Fin (d.len + 1))

private def sc (b : Blo S r) (d : Dat S s) (j : Fin d.len) : Fin (Dat.cons b d).len := (j.succ : Fin (d.len + 1))

private theorem idx_cast (b : Blo S r) (d : Dat S s) (i : Fin r) :
    (Dat.cons b d).idx (Fin.castAdd s i) = (z0 b d) := by
  rw [Dat.idx]
  exact Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) i

private theorem idx_nat (b : Blo S r) (d : Dat S s) (i : Fin s) :
    (Dat.cons b d).idx (Fin.natAdd r i) = sc b d (d.idx i) := by
  rw [Dat.idx]
  exact Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (right := fun i => (d.idx i).succ) i

private theorem sum_zero {M : Type} [AddCommMonoid M] (b : Blo S r) (d : Dat S s) (f : Fin (r + s) → M) :
    ∑ i ∈ Finset.univ.filter fun i => (Dat.cons b d).idx i = (z0 b d), f i = ∑ i, f (Fin.castAdd s i) := by
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin s))), add_zero]
  · exact Finset.sum_congr rfl fun i _ => if_pos (idx_cast b d i)
  · exact fun i _ => if_neg (by rw [idx_nat]; exact Fin.succ_ne_zero _)

private theorem sum_succ {M : Type} [AddCommMonoid M] (b : Blo S r) (d : Dat S s) (j : Fin d.len) (f : Fin (r + s) → M) :
    ∑ i ∈ Finset.univ.filter fun i => (Dat.cons b d).idx i = (sc b d j), f i =
      ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, f (Fin.natAdd r i) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_add, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin r))),
    zero_add]
  · exact Finset.sum_congr rfl fun i _ => if_congr (by rw [idx_nat]; exact Fin.succ_inj) rfl rfl
  · exact fun i _ => if_neg (by rw [idx_cast]; exact (Fin.succ_ne_zero _).symm)

private theorem size_zero (b : Blo S r) (d : Dat S s) : (Dat.cons b d).size (z0 b d) = r := by
  rw [Dat.size, Finset.card_eq_sum_ones, sum_zero]; simp

private theorem size_succ (b : Blo S r) (d : Dat S s) (j : Fin d.len) :
    (Dat.cons b d).size (sc b d j) = d.size j := by
  rw [Dat.size, Finset.card_eq_sum_ones, sum_succ, Dat.size, Finset.card_eq_sum_ones]

private theorem sum_size (d : Dat S s) : ∑ j, d.size j = s := by
  have := Finset.card_eq_sum_card_fiberwise (f := d.idx) (s := Finset.univ) (t := Finset.univ) fun _ _ => Finset.mem_univ _
  simpa [Dat.size] using this.symm

private theorem rho_zero (b : Blo S r) (d : Dat S s) : (Dat.cons b d).rho (z0 b d) = -(s : ℝ) / 2 := by
  have : ∀ f : Fin (d.len + 1) → ℝ, ∑ l ∈ Finset.Iio 0, f l - ∑ l ∈ Finset.Ioi 0, f l = -∑ l : Fin d.len, f l.succ := fun f => by
    rw [Fin.sum_Ioi_zero, show Finset.Iio (0 : Fin (d.len + 1)) = ∅ from Finset.Iio_bot]; simp
  refine (congrArg (· / 2) (this fun l => ((Dat.cons b d).size l : ℝ))).trans ?_
  have e : ∀ l : Fin d.len, (Dat.cons b d).size (l.succ : Fin (d.len + 1)) = d.size l := size_succ b d
  simp only [e]
  rw [← Nat.cast_sum, sum_size]

private theorem rho_succ (b : Blo S r) (d : Dat S s) (j : Fin d.len) :
    (Dat.cons b d).rho (sc b d j) = (r : ℝ) / 2 + d.rho j := by
  have : ∀ f : Fin (d.len + 1) → ℝ, ∑ l ∈ Finset.Iio j.succ, f l - ∑ l ∈ Finset.Ioi j.succ, f l =
      f 0 + (∑ l ∈ Finset.Iio j, f l.succ - ∑ l ∈ Finset.Ioi j, f l.succ) := fun f => by
    rw [Fin.sum_Ioi_succ, ← Finset.filter_gt_eq_Iio, ← Finset.filter_gt_eq_Iio, Finset.sum_filter, Finset.sum_filter,
      Fin.sum_univ_succ]
    simp [add_sub_assoc]
  refine (congrArg (· / 2) (this fun l => ((Dat.cons b d).size l : ℝ))).trans ?_
  have e : ∀ l : Fin d.len, (Dat.cons b d).size (l.succ : Fin (d.len + 1)) = d.size l := size_succ b d
  have e0 : (Dat.cons b d).size (0 : Fin (d.len + 1)) = r := size_zero b d
  simp only [e, e0, Dat.rho, add_div]

private theorem J_zero (b : Blo S r) (d : Dat S s) : (Dat.cons b d).J (z0 b d) = j1 E r s := by
  simp only [Dat.J, j1, size_zero, sum_zero]

private theorem J_rel (b : Blo S r) (d : Dat S s) (t : ℝ) (j : Fin d.len) :
    (d.J j, (Dat.cons b d).J (sc b d j)) ∈ relAlg b s t := by
  simp only [Dat.J, size_succ, sum_succ]
  exact pair_sum (relAlg b s t) _ _ _ _ fun τ i => eop_rel b t τ i i

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin UpperTheory.V.Cm in
theorem UpperTheory.ConvolutionTheory.BW.compCap :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CompCap E := by
  intro E _ _ _ S n d
  induction d with
  | nil =>
    intro φ τ u _
    have : cap (a := 0) τ u = 1 := by simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor]
    rw [this, List.ofFn_zero, List.prod_nil]
  | @cons r s b d ih =>
    intro φ τ u hφ
    funext t
    set F : Fin (r + s) → Module.End ℂ (Sm E (r + s)) := fun i => algebraMap ℂ _
      (u + (Dat.cons b d).lam τ i + ((Dat.cons b d).rho ((Dat.cons b d).idx i) : ℂ)) +
        (Dat.cons b d).J ((Dat.cons b d).idx i) with hF
    have hc : ∀ i j, Commute (F i) (F j) := fun i j =>
      ((Algebra.commute_algebraMap_left _ _).add_left (Commute.add_right (Algebra.commute_algebraMap_right _ _)
        (((datBasics E).2 S _ (Dat.cons b d)).2.2.2.2.2.2.2.1 _ _)))
    have hr : ∀ i, F i ∈ (uC E (r + s)).range := fun i => by
      obtain ⟨v, hv⟩ := ((datBasics E).2 S _ (Dat.cons b d)).2.2.2.2.2.2.2.2.2 ((Dat.cons b d).idx i)
      exact (uC E (r + s)).range.add_mem ((uC E (r + s)).range.algebraMap_mem _) ⟨v, hv.symm⟩
    have hP : Polynomial.aeval (j1 E r s) (∏ i, (Polynomial.X + Polynomial.C (u - (s : ℂ) / 2 + b.Λ τ i))) =
        (List.ofFn fun i => F (Fin.castAdd s i)).prod := by
      rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
      congr 2
      funext i
      simp only [Function.comp_apply, hF, idx_cast, rho_zero, J_zero, Dat.lam, Fin.addCases_left]
      rw [map_add (f := _), Polynomial.aeval_X, Polynomial.aeval_C]
      refine (add_comm _ _).trans (congrArg (fun c : ℂ => algebraMap ℂ _ c + j1 E r s) ?_)
      push_cast
      ring
    have hsplit : (List.ofFn F).prod = (List.ofFn fun i => F (Fin.natAdd r i)).prod *
        (List.ofFn fun i => F (Fin.castAdd s i)).prod := by
      rw [List.ofFn_add, List.prod_append]
      refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
      exact hc _ _
    set χ := (List.ofFn fun i => F (Fin.castAdd s i)).prod φ with hχ
    have uχ : Umg χ := umg_range (prod_mem_ofFn (uC E (r + s)).range _ fun i => hr _) hφ
    obtain ⟨ψ, hψ, uψ, -⟩ := sliceUmg E S r s b (t (0 : Fin (d.len + 1))) χ uχ
    have hQ : ((List.ofFn fun i : Fin s => algebraMap ℂ (Module.End ℂ (Sm E s))
        (u + (r : ℂ) / 2 + d.lam τ i + (d.rho (d.idx i) : ℂ)) + d.J (d.idx i)).prod,
        (List.ofFn fun i => F (Fin.natAdd r i)).prod) ∈ relAlg b s (t (0 : Fin (d.len + 1))) := by
      have e : (fun i => F (Fin.natAdd r i)) = fun i => algebraMap ℂ _ (u + (r : ℂ) / 2 + d.lam τ i + (d.rho (d.idx i) : ℂ)) +
          (Dat.cons b d).J (sc b d (d.idx i)) := by
        funext i
        simp only [hF, idx_nat, rho_succ, Dat.lam, Fin.addCases_right]
        refine congrArg (fun c : ℂ => algebraMap ℂ _ c + _) ?_
        push_cast
        ring
      rw [e]
      exact pair_prod _ _ _ _ fun i => J_rel b d _ _
    change d.comp (slice b.f.1 (t (0 : Fin (d.len + 1))) (cap τ u φ).1) _ =
      d.comp (slice b.f.1 (t (0 : Fin (d.len + 1))) ((List.ofFn F).prod φ).1) _
    rw [sliceCap E S r s b _ φ τ u hφ, hP, hsplit, Module.End.mul_apply, ← hχ,
      ← (cap_rel b _ τ _ χ ψ uχ hψ).2, ← (hQ χ ψ uχ hψ).2, ih ψ τ _ uψ]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompHecke
section
open NumberField

noncomputable section

namespace UpperTheory.ConvolutionTheory.BW

open GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin UpperTheory.V.Cm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

private theorem sum_pi {m j : ℕ} (F : (Fin (m + 1) → ℕ) → ℂ) :
    ∑ A ∈ Finset.piAntidiag Finset.univ j, F A =
      ∑ a ∈ Finset.range (j + 1), ∑ A ∈ Finset.piAntidiag Finset.univ (j - a), F (Fin.cons a A) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun A _ => ⟨A 0, Fin.tail A⟩) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma,
      Finset.mem_range] at hA ⊢
    refine ⟨by omega, ?_⟩
    change ∑ i : Fin m, A i.succ = _
    omega
  · intro p hp
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma,
      Finset.mem_range, Fin.cons_zero, Fin.cons_succ] at hp ⊢
    have h2 : ∑ i, p.2 i = j - p.1 := hp.2
    omega
  · intro A _
    exact Fin.cons_self_tail A
  · intro p _
    simp
  · intro A _
    simp

private theorem comp_sum (d : Dat S n) {ι : Type} (A : Finset ι) (c : ι → ℂ) (φ : ι → Sm E n) (h : ∀ i, Umg (φ i)) (t) :
    d.comp (∑ i ∈ A, c i • φ i).1 t = ∑ i ∈ A, c i * d.comp (φ i).1 t := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have h0 : Umg (0 : Sm E n) := (umgOps E n).1
    have h1 := (compBound E S n d).2 0 0 1 h0 h0 t
    rw [one_smul, add_zero, one_mul, left_eq_add] at h1
    exact h1
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, (compBound E S n d).2 _ _ _ (h a) (Umg.sum fun i _ => (h i).smul _), ih]

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin UpperTheory.V.Cm in
theorem UpperTheory.ConvolutionTheory.BW.compHecke :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CompHecke E := by
  intro E _ _ _ S n d
  induction d with
  | nil =>
    intro φ w j t _ hs hw hj
    obtain rfl : j = 0 := by omega
    rw [((hkOps E 0 w 0).2.2.2 S φ hw hs).2.1, Finset.piAntidiag_zero, Finset.sum_singleton,
      Finset.prod_eq_one fun l _ => l.elim0, one_mul]
    rfl
  | @cons r s b d ih =>
    intro φ w j (t : Fin (d.len + 1) → ℝ) hφ hs hw hj
    choose ψ h1 h2 _ _ h3 _ using fun v => sliceUmg E S r s b v φ hφ
    have hq : qc w ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
    change d.comp (slice b.f.1 (t 0) (hk (r + s) w j φ).1) (fun l => t l.succ) = _
    rw [sliceHecke E S r s b (t 0) φ ψ w j hφ hs hw hj h1, comp_sum d _ _ _ fun a => (h2 _).hk w _]
    refine Eq.trans ?_ (sum_pi (m := d.len) _).symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    split_ifs with h
    · rw [ih _ w _ _ (h2 _) (h3 _ hs) hw h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun A hA => ?_
      have hA' : ∑ l, (A l : ℂ) = (j : ℂ) - a := by
        rw [← Nat.cast_sum, (Finset.mem_piAntidiag.1 hA).1, Nat.cast_sub ha']
      rw [← mul_assoc, h1]
      congr 1
      rw [Dat.prod_cons, Dat.sat_zero, Dat.rho_zero]
      simp only [Dat.sat_succ, Dat.rho_succ]
      change _ = _ * qc w ^ (_ * (a : ℂ)) * ∏ l, _ * qc w ^ (_ * (A l : ℂ))
      simp only [Finset.prod_mul_distrib, Formalism.UG.P.satake_cpow_prod _ hq]
      rw [mul_mul_mul_comm, mul_mul_mul_comm _ (qc w ^ _), ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
      congr 2
      push_cast
      simp only [neg_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hA']
      ring
    · refine (Finset.sum_eq_zero fun A hA => ?_).symm
      obtain ⟨l, hl⟩ : ∃ l, d.size l < A l := by
        by_contra hn
        push Not at hn
        have := Finset.sum_le_sum (s := Finset.univ) fun l _ => hn l
        rw [d.sum_size, (Finset.mem_piAntidiag.1 hA).1] at this
        exact h this
      apply mul_eq_zero_of_left
      apply Finset.prod_eq_zero (i := Dat.sc b d l) (Finset.mem_univ _)
      apply mul_eq_zero_of_left
      rw [Dat.sat_succ]
      change Multiset.esymm _ (A l) = 0
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty]
      · rfl
      · rwa [Multiset.card_map, ((datBasics E).2 S s d).2.2.2.1 l w hw]
end
end

