module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsBoundedDenominatorOfLocalIntegralityConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma norm_le_of_integral_image {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det ≠ 0) (v : Fin n → K)
    (h : ∀ i, ‖(((M *ᵥ v) i : K) : PadicAlgCl p)‖ ≤ 1) (i : Fin n) :
    ‖(v i : PadicAlgCl p)‖ ≤ ∑ a, ∑ b, ‖((M⁻¹ a b : K) : PadicAlgCl p)‖ := by
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, u = M *ᵥ v := ⟨_, rfl⟩
  have hv : v = M⁻¹ *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  have hu1 : ∀ b, ‖(u b : PadicAlgCl p)‖ ≤ 1 := by
    intro b
    rw [hu]
    exact h b
  have hrow : ‖(v i : PadicAlgCl p)‖ ≤ ∑ b, ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ := by
    rw [hv]
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul]
    calc ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ * ‖(u b : PadicAlgCl p)‖
        ≤ ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hu1 b) (norm_nonneg _)
      _ = ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ := mul_one _
  refine hrow.trans ?_
  exact Finset.single_le_sum (f := fun a => ∑ b, ‖((M⁻¹ a b : K) : PadicAlgCl p)‖)
    (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ i)

private lemma framePow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    ‖((p ^ k : ℕ) : PadicAlgCl p)‖ = ((p : ℝ) ^ k)⁻¹ := by
  rw [Nat.cast_pow, norm_pow, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
    PadicAlgCl.norm_extends, Padic.norm_p, inv_pow]

theorem UpperTheory.exists_bounded_denominator_of_local_integrality_conj :
    UpperTheory.Gal.W2.FInt → ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (S B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)), (∀ w, (S w).det ≠ 0) → (∀ w, (B w).det ≠ 0) → ∃ k : ℕ, ∀ y : Fin G.n → G.F, IntL (G := G) (fun w => S w *ᵥ (fun i => G.embW w (y i))) → IntL (G := G) (fun w => B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (y i)))) → ∃ (m : ℕ) (c : Fin G.n → 𝓞 G.F), m.Coprime p ∧ ∀ i, (c i : G.F) = ((m * p ^ k : ℕ) : G.F) * y i := by
  intro hF p _ G S B hS hB
  classical
  set R : ℝ := ∑ w, ((∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖) +
    ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖) with hR
  have hnnS : ∀ w, 0 ≤ ∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ :=
    fun w => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  have hnnB : ∀ w, 0 ≤ ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ :=
    fun w => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  have hone : ∀ w, (∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖) +
      ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ ≤ R := fun w =>
    Finset.single_le_sum
      (f := fun w' => (∑ a, ∑ b, ‖(((S w')⁻¹ a b : G.Fw w') : PadicAlgCl p)‖) +
        ∑ a, ∑ b, ‖(((B w')⁻¹ a b : G.Fw w') : PadicAlgCl p)‖)
      (fun w' _ => add_nonneg (hnnS w') (hnnB w')) (Finset.mem_univ w)
  have hSR : ∀ w, ∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ ≤ R := by
    intro w
    have h1 := hone w
    have h2 := hnnB w
    linarith
  have hBR : ∀ w, ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ ≤ R := by
    intro w
    have h1 := hone w
    have h2 := hnnS w
    linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hp1
  refine ⟨k, fun y hyS hyB => ?_⟩
  have hp0 : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by linarith) k
  have key : ∀ (w : Fin G.m) (z : G.Fw w), ‖(z : PadicAlgCl p)‖ ≤ R →
      ‖((G.embW w ((p ^ k : ℕ) : G.F) * z : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
    intro w z hz
    have hc : ((G.embW w ((p ^ k : ℕ) : G.F) * z : G.Fw w) : PadicAlgCl p)
        = ((p ^ k : ℕ) : PadicAlgCl p) * (z : PadicAlgCl p) := by
      rw [map_natCast]
      push_cast
      rfl
    rw [hc, norm_mul, framePow]
    calc ((p : ℝ) ^ k)⁻¹ * ‖(z : PadicAlgCl p)‖
        ≤ ((p : ℝ) ^ k)⁻¹ * (p : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (hz.trans hk.le) (inv_nonneg.mpr hp0.le)
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  have hint : ∀ i w,
      ‖((G.embW w (((p ^ k : ℕ) : G.F) * y i) : G.Fw w) : PadicAlgCl p)‖ ≤ 1 ∧
      ‖((G.embW w (IsCMField.complexConj G.F (((p ^ k : ℕ) : G.F) * y i)) : G.Fw w) :
        PadicAlgCl p)‖ ≤ 1 := by
    intro i w
    constructor
    · rw [map_mul]
      exact key w _ ((norm_le_of_integral_image _ (S w) (hS w) (fun j => G.embW w (y j)) (hyS w) i).trans (hSR w))
    · rw [map_mul, map_natCast, map_mul]
      exact key w _ ((norm_le_of_integral_image _ (B w) (hB w)
        (fun j => G.embW w (IsCMField.complexConj G.F (y j))) (hyB w) i).trans (hBR w))
  have hx := fun i => hF p G (((p ^ k : ℕ) : G.F) * y i) (hint i)
  choose m c hmc hc using hx
  refine ⟨∏ i, m i, fun i => ((∏ j ∈ Finset.univ.erase i, m j : ℕ) : 𝓞 G.F) * c i,
    Nat.Coprime.prod_left (fun i _ => hmc i), fun i => ?_⟩
  have hci := hc i
  push_cast at hci ⊢
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  refine (congrArg (fun t => (∏ x ∈ Finset.univ.erase i, (m x : G.F)) * t) hci).trans ?_
  beta_reduce
  ring
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsFinsetSpanOfIntegralMultiples
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.exists_finset_span_of_integral_multiples :
    ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module ℚ V] (n : ℕ) (kp : V ≃+ (Fin n → F)), ∃ s : Finset V, Submodule.span ℚ (s : Set V) = ⊤ ∧ ∀ (x : V) (N : ℕ) (c : Fin n → 𝓞 F), (∀ i, (c i : F) = (N : F) * kp x i) → N • x ∈ AddSubgroup.closure (s : Set V) := by
  intro F V _ _ _ _ n kp
  classical
  let ib := NumberField.integralBasis F
  let b := NumberField.RingOfIntegers.basis F
  let g : Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 F) → V :=
    fun ij => kp.symm (Pi.single ij.1 (ib ij.2))
  have hg : ∀ i j, g (i, j) ∈ ((Finset.univ.image g : Finset V) : Set V) := fun i j =>
    Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro v -
    have hsum : v = ∑ i, kp.symm (Pi.single i (kp v i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    let Φ : F →+ V := kp.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin n => F) i)
    have hΦa : ∀ y, kp.symm (Pi.single i y) = Φ y := fun y => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦa, ← ib.sum_repr (kp v i), map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_rat_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hg i j))
  · intro x N c hc
    have hx : N • x = kp.symm (fun i => (c i : F)) := by
      apply kp.injective
      rw [AddEquiv.apply_symm_apply, map_nsmul]
      funext i
      rw [Pi.smul_apply, hc i, nsmul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, ← Finset.univ_sum_single (fun i => (c i : F)), map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    beta_reduce
    let Φ : F →+ V := kp.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin n => F) i)
    have hΦa : ∀ y, kp.symm (Pi.single i y) = Φ y := fun y => rfl
    have hci : ((c i : 𝓞 F) : F) = ∑ j, (b.repr (c i) j) • ib j := by
      calc ((c i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ j, b.repr (c i) j • b j) := by
            rw [b.sum_repr]
        _ = ∑ j, (b.repr (c i) j) • ib j := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_zsmul, NumberField.integralBasis_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦa, hci, map_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hg i j)) _
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsGlobalApproxOfLocalModPPowConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma normPPow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    ‖((p : PadicAlgCl p)) ^ k‖ = ((p : ℝ) ^ k)⁻¹ := by
  rw [norm_pow, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
    Padic.norm_p, inv_pow]

private lemma stepAt {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {n : ℕ}
    (S : Matrix (Fin n) (Fin n) K) (hS : S.det ≠ 0) (a v : Fin n → K) (k : ℕ) (e C : ℝ) (he : 0 ≤ e)
    (hC : ∀ i, ∑ j, ‖(S i j : PadicAlgCl p)‖ ≤ C) (hCe : C * e = ((p : ℝ) ^ k)⁻¹)
    (hv : ∀ i, ‖((v i - (S⁻¹ *ᵥ a) i : K) : PadicAlgCl p)‖ < e) :
    ∃ a' : Fin n → K, (∀ i, ‖(a' i : PadicAlgCl p)‖ ≤ 1) ∧ S *ᵥ v = a + p ^ k • a' := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K, d = v - S⁻¹ *ᵥ a := ⟨_, rfl⟩
  have hv' : ∀ j, ‖(d j : PadicAlgCl p)‖ < e := by
    intro j
    rw [hd]
    exact hv j
  have hSd : S *ᵥ v - a = S *ᵥ d := by
    rw [hd, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS), Matrix.one_mulVec]
  have hbound : ∀ i, ‖(((S *ᵥ v - a) i : K) : PadicAlgCl p)‖ ≤ ((p : ℝ) ^ k)⁻¹ := by
    intro i
    rw [hSd, ← hCe]
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    calc ‖∑ j, (S i j : PadicAlgCl p) * (d j : PadicAlgCl p)‖
        ≤ ∑ j, ‖(S i j : PadicAlgCl p) * (d j : PadicAlgCl p)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖(S i j : PadicAlgCl p)‖ * e := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (le_of_lt (hv' j)) (norm_nonneg _)
      _ = (∑ j, ‖(S i j : PadicAlgCl p)‖) * e := (Finset.sum_mul _ _ _).symm
      _ ≤ C * e := mul_le_mul_of_nonneg_right (hC i) he
  have hp0 : (0 : ℝ) < (p : ℝ) ^ k :=
    pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) k
  have hpK : ((p : K) ^ k) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨fun i => ((p : K) ^ k)⁻¹ * (S *ᵥ v - a) i, ?_, ?_⟩
  · intro i
    have hi := hbound i
    have hnorm : ‖((((p : K) ^ k)⁻¹ * (S *ᵥ v - a) i : K) : PadicAlgCl p)‖
        = (p : ℝ) ^ k * ‖(((S *ᵥ v - a) i : K) : PadicAlgCl p)‖ := by
      push_cast
      rw [norm_mul, norm_inv, normPPow, inv_inv]
    rw [hnorm]
    calc (p : ℝ) ^ k * ‖(((S *ᵥ v - a) i : K) : PadicAlgCl p)‖
        ≤ (p : ℝ) ^ k * ((p : ℝ) ^ k)⁻¹ := mul_le_mul_of_nonneg_left hi hp0.le
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  · funext i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, mul_inv_cancel_left₀ hpK,
      Pi.sub_apply, add_sub_cancel]

theorem UpperTheory.exists_global_approx_of_local_mod_p_pow_conj :
    UpperTheory.Gal.W2.FApprox → ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (S B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)), (∀ w, (S w).det ≠ 0) → (∀ w, (B w).det ≠ 0) → ∀ (a b : Loc G) (k : ℕ), ∃ (y : Fin G.n → G.F) (a' b' : Loc G), IntL a' ∧ IntL b' ∧ (∀ w, S w *ᵥ (fun i => G.embW w (y i)) = a w + p ^ k • a' w) ∧ ∀ w, B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (y i))) = b w + p ^ k • b' w := by
  intro hF p _ G S B hS hB a b k
  classical
  set C : ℝ := 1 + ∑ w, ∑ i, ∑ j,
    (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) with hCdef
  have hnn : ∀ w i, 0 ≤ ∑ j, (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) :=
    fun w i => Finset.sum_nonneg fun j _ => by positivity
  have hbig : ∀ w i, ∑ j, (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) ≤ C := by
    intro w i
    have h2 := Finset.single_le_sum
      (f := fun i' => ∑ j, (‖(S w i' j : PadicAlgCl p)‖ + ‖(B w i' j : PadicAlgCl p)‖))
      (fun i' _ => hnn w i') (Finset.mem_univ i)
    have h3 := Finset.single_le_sum
      (f := fun w' => ∑ i', ∑ j, (‖(S w' i' j : PadicAlgCl p)‖ + ‖(B w' i' j : PadicAlgCl p)‖))
      (fun w' _ => Finset.sum_nonneg fun i' _ => hnn w' i') (Finset.mem_univ w)
    linarith
  have hrowS : ∀ w i, ∑ j, ‖(S w i j : PadicAlgCl p)‖ ≤ C := by
    intro w i
    refine le_trans ?_ (hbig w i)
    exact Finset.sum_le_sum fun j _ => le_add_of_nonneg_right (norm_nonneg _)
  have hrowB : ∀ w i, ∑ j, ‖(B w i j : PadicAlgCl p)‖ ≤ C := by
    intro w i
    refine le_trans ?_ (hbig w i)
    exact Finset.sum_le_sum fun j _ => le_add_of_nonneg_left (norm_nonneg _)
  have hCpos : 0 < C := by
    have : 0 ≤ ∑ w, ∑ i, ∑ j, (‖(S w i j : PadicAlgCl p)‖ + ‖(B w i j : PadicAlgCl p)‖) :=
      Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => hnn w i
    linarith
  have hp0 : (0 : ℝ) < (p : ℝ) ^ k :=
    pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) k
  set e : ℝ := ((p : ℝ) ^ k)⁻¹ / C with he_def
  have he : 0 < e := div_pos (inv_pos.mpr hp0) hCpos
  have hCe : C * e = ((p : ℝ) ^ k)⁻¹ := by
    rw [he_def, mul_div_cancel₀ _ hCpos.ne']
  have hy : ∀ i : Fin G.n, ∃ x : G.F, ∀ w,
      ‖((G.embW w x - ((S w)⁻¹ *ᵥ a w) i : G.Fw w) : PadicAlgCl p)‖ < e ∧
      ‖((G.embW w (IsCMField.complexConj G.F x) - ((B w)⁻¹ *ᵥ b w) i : G.Fw w) :
        PadicAlgCl p)‖ < e :=
    fun i => hF p G (fun w => ((S w)⁻¹ *ᵥ a w) i) (fun w => ((B w)⁻¹ *ᵥ b w) i) e he
  choose y hy using hy
  have hA : ∀ w, ∃ c : Fin G.n → G.Fw w, (∀ i, ‖(c i : PadicAlgCl p)‖ ≤ 1) ∧
      S w *ᵥ (fun i => G.embW w (y i)) = a w + p ^ k • c :=
    fun w => stepAt (S w) (hS w) (a w) _ k e C he.le (hrowS w) hCe (fun i => (hy i w).1)
  have hB' : ∀ w, ∃ c : Fin G.n → G.Fw w, (∀ i, ‖(c i : PadicAlgCl p)‖ ≤ 1) ∧
      B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (y i))) = b w + p ^ k • c :=
    fun w => stepAt (B w) (hB w) (b w) _ k e C he.le (hrowB w) hCe (fun i => (hy i w).2)
  choose a' ha'1 ha'2 using hA
  choose b' hb'1 hb'2 using hB'
  exact ⟨y, a', b', fun w i => ha'1 w i, fun w i => hb'1 w i, ha'2, hb'2⟩
end

