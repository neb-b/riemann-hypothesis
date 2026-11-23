module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CommuteCenterRtInfGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillOne
section
open NumberField

noncomputable section

namespace UpperTheory.ConvolutionTheory.BW

open GlobalTheory.CuspRep PositivityTheory.Rg.Fx UpperTheory.V.Cm

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

private theorem esymm_zero' (s : Multiset ℂ) : s.esymm 0 = 1 := by simp [Multiset.esymm]

private theorem esymm_add' (s t : Multiset ℂ) (j : ℕ) :
    (s + t).esymm j = ∑ a ∈ Finset.range (j + 1), s.esymm a * t.esymm (j - a) :=
  _root_.UpperTheory.Reformulated.B.Qk43.esymm_add s t j

private theorem esymm_sum : ∀ (m : ℕ) (M : Fin m → Multiset ℂ) (j : ℕ),
    (∑ l, M l).esymm j = ∑ a ∈ Finset.piAntidiag Finset.univ j, ∏ l, (M l).esymm (a l)
  | 0, M, 0 => by simp [esymm_zero']
  | 0, M, j + 1 => by simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | m + 1, M, j => by
    rw [Fin.sum_univ_succ, esymm_add', sum_pi]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [esymm_sum m, Finset.mul_sum]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n : ℕ}

private theorem ev_hEP (d : Dat S n) (z : Fin d.len → ℂ) (k : Pl E × Fin n) :
    ev z (d.hEP k) = d.ptH (fun l => z l + d.rho l) k := by
  have hq : qc k.1 ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero k.1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Dat.hEP, map_sum, Dat.ptH, Dat.ptS, esymm_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ∀ (v : Fin d.len → ℝ) (c : ℂ), ev z (AddMonoidAlgebra.single v (MvPolynomial.C c)) =
      c * Complex.exp (∑ l, (v l : ℂ) * z l) := fun v c => by
    simp [ev, lift, AddMonoidAlgebra.liftNCRingHom, expChar]
  rw [e, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have h := Multiset.pow_smul_esymm (qc k.1 ^ (-(z l + d.rho l))) (a l) ((d.sat l k.1).map fun x : ℂˣ => (x : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [mul_comm _ (qc k.1 ^ (-(z l + d.rho l)))]
  rw [← h, mul_assoc, mul_comm]
  congr 1
  rw [← Complex.cpow_natCast, Complex.cpow_def_of_ne_zero hq, Complex.cpow_natCast, Complex.cpow_def_of_ne_zero hq,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [Pi.neg_apply]
  push_cast
  unfold qc
  ring

private theorem supp_good {F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n)}
    {G : ℕ → MvPolynomial (Pl E × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)} (hF : ∀ x ∈ F.vars, x.1 ∉ S) (hG : Gen F G)
    (k : ℕ) {β : (Pl E × Fin n) →₀ ℕ} (hβ : β ∈ (G k).support) : ∀ x ∈ β.support, x.1 ∉ S := by
  classical
  intro x hx
  refine hF x ((MvPolynomial.mem_vars_iff_mem_support x).2 ⟨β, ?_, hx⟩)
  by_contra hn
  have h := congrArg (AddMonoidAlgebra.coeff · β) (hG k)
  rw [MvPolynomial.coeff_map, pieceK, MvPolynomial.coeff_sum, Finset.sum_eq_zero fun γ hγ => by
    rw [MvPolynomial.coeff_monomial, if_neg fun e : γ = β => hn (e ▸ hγ)]] at h
  exact MvPolynomial.mem_support_iff.1 hβ (UpperTheory.ConvolutionTheory.FX.blockE_inj (E →+* ℂ) n (h.trans (map_zero _).symm))

private theorem list_rel {M A ι : Type} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} [CommRing A] [Module A V]
    (f : ι → A) (g : ι → Module.End ℂ M) (e : ι → ℕ) (l : List ι) (h : ∀ i ∈ l, ∀ v : V, ((f i • v : V) : M) = g i v) :
    ∀ v : V, (((l.map fun i => f i ^ e i).prod • v : V) : M) = (l.map fun i => g i ^ e i).prod v := by
  induction l with
  | nil => simp
  | cons i l ih =>
    intro v
    have hp : ∀ (m : ℕ) (v : V), ((f i ^ m • v : V) : M) = (g i ^ m) v := fun m => by
      induction m with
      | zero => simp
      | succ m ih => intro v; rw [pow_succ', pow_succ', mul_smul, h i (by simp), ih, Module.End.mul_apply]
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, mul_smul, hp, Module.End.mul_apply,
      ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep PositivityTheory.Rg.Fx in
theorem UpperTheory.ConvolutionTheory.BW.killOne :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KillOne E := by
  intro E _ _ _ S n C d φ F G hC hb hs hF hK hG t
  obtain ⟨A, _, _, _, _, Z, H, I, T, hZ, hH, hsys⟩ := exists_sys d hC
  have h := absKill (E →+* ℂ) (Pl E × Fin n) A (bsp S n hC) n d.len Z H I T (cmp d hC) d.idx d.lamR d.hEP _ C hsys F G hF
    (fun z => by
      have := hK fun l => z l + d.rho l
      rw [← this]
      congr 2
      · funext p
        simp only [Dat.lamR, Dat.ptL]
        ring
      · funext k
        exact ev_hEP d z k) hG ⟨φ, hb, hs⟩ t
  have e : ∀ k (v : bsp S n hC), ((MvPolynomial.eval₂ (MvPolynomial.aeval Z).toRingHom H (G k) • v : bsp S n hC) : Sm E n) =
      app (G k) v := fun k v => by
    rw [MvPolynomial.eval₂_eq, Finset.sum_smul, Submodule.coe_sum, app, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [mul_smul, Module.End.mul_apply, hmon, ← Finset.prod_map_toList,
      ← list_rel H (fun p => hk n p.1 (p.2 + 1)) β _ fun p hp => hH p (supp_good hF hG k hβ p (Finset.mem_toList.1 hp))]
    exact hZ _ _
  convert h using 2 with k
  exact congrArg (fun ψ : Sm E n => d.comp ψ.1 t) (e k ⟨φ, hb, hs⟩).symm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RhoLe
section
open NumberField UpperTheory.ConvolutionTheory.BW

private theorem rho_le {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} {S : Set (Pl E)}
    (d : Dat S n) (j : Fin d.len) : ‖(d.rho j : ℂ)‖ ≤ n := by
  have h : ∑ l, d.size l = n := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := d.idx)
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have h' : ∀ s : Finset (Fin d.len), 0 ≤ ∑ l ∈ s, (d.size l : ℝ) ∧ ∑ l ∈ s, (d.size l : ℝ) ≤ n := fun s => by
    refine ⟨Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, ?_⟩
    have := (Finset.sum_le_sum_of_subset (f := d.size) (Finset.subset_univ s)).trans h.le
    exact_mod_cast this
  rw [Complex.norm_real, Real.norm_eq_abs, Dat.rho, abs_le]
  have h1 := h' (Finset.Iio j)
  have h2 := h' (Finset.Ioi j)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem UpperTheory.ConvolutionTheory.BW.far :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.Far E := by
  intro E _ _ _ n C hC
  obtain ⟨B, hB⟩ := absFar (E →+* ℂ) n C (∑ _p : (E →+* ℂ) × Fin n, (n : ℝ))
  refine ⟨B + n, fun S d φ hφ hs ⟨τ, i, hi⟩ => ?_⟩
  obtain ⟨A, _, _, _, _, Z, H, I, t, -, -, h⟩ := exists_sys d hC
  have h0 := hB _ A _ d.len Z H I t _ _ _ _ _ h (fun j => ?_) ⟨(τ, i), ?_⟩
  · exact LinearMap.congr_fun h0 ⟨φ, hφ, hs⟩
  · simp only [Dat.lamR]
    rw [Finset.sum_add_distrib, ((datBasics E).2 S n d).2.2.1 j, zero_add]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => rho_le d _).trans ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  · have h1 := norm_sub_le (d.lamR (τ, i)) (d.rho (d.idx i) : ℂ)
    have h2 : d.lamR (τ, i) - (d.rho (d.idx i) : ℂ) = d.lam τ i := add_sub_cancel_right _ _
    rw [h2] at h1
    linarith [rho_le d (d.idx i)]
end

