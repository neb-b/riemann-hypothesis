module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_ratCast {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : ℚ) :
    G.rho w (algebraMap ℚ G.C s) = Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) (algebraMap ℚ ℚ_[p] s)) := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C s, G.rho_F w]
  congr 1
  rw [eq_ratCast (algebraMap ℚ G.F) s, eq_ratCast (algebraMap ℚ ℚ_[p]) s, map_ratCast, map_ratCast]

private theorem pairL_move {p : ℕ} [Fact p.Prime] (G : HTGroup p) (M N : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w))
    (s : ℚ_[p]) (h : ∀ w, M w * N w = Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) s)) (a b : Loc G) :
    pairL (fun w => (M w)ᵀ *ᵥ a w) (fun w => N w *ᵥ b w) = s * pairL a b := by
  unfold pairL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ((M w)ᵀ *ᵥ a w) ⬝ᵥ (N w *ᵥ b w) = s • (a w ⬝ᵥ b w) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h w,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, Algebra.smul_def]
  rw [e, map_smul, smul_eq_mul]

private theorem mem_move {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ} (A : PFrame L β)
    (u : G.Cˣ) (s : ℚˣ) (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) (g g' : Gp G) (x : VQ D)
    (h1 : g'.1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s * g.1)
    (h2 : ∀ w, g'.2 w = Units.map (G.rho w).toMonoidHom u * g.2 w) :
    A.Mem g' (L.rep (u : G.C) x) ↔ A.Mem g x := by
  have hk : (β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C) = ((u⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C s := by
    calc (β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)
        = ((u⁻¹ : G.Cˣ) : G.C) * ((u : G.C) * β * sh G u) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
          rw [hy]
          simp only [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have hM : ∀ w, G.rho w ((β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)) * G.rho w (u : G.C) =
      Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) (algebraMap ℚ ℚ_[p] s)) := by
    intro w
    rw [hk, ← map_mul, ← Algebra.commutes, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, rho_ratCast]
  have t1 : ∀ w, (((g'.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T (L.rep (u : G.C) x) w =
      (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w := by
    intro w
    have hu : (((Units.map (G.rho w).toMonoidHom u)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *
        G.rho w (u : G.C) = 1 := Units.inv_mul (Units.map (G.rho w).toMonoidHom u)
    rw [h2 w, _root_.mul_inv_rev, Units.val_mul, A.act, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ _ (G.rho w (u : G.C)), hu,
      Matrix.one_mulVec]
  have e1 : ((g'.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℚ ℚ_[p] s = ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) := by
    have hs : (((Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℚ ℚ_[p] s = 1 :=
      Units.inv_mul (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s)
    rw [h1, _root_.mul_inv_rev, Units.val_mul, _root_.mul_assoc, hs, _root_.mul_one]
  have t2 : ∀ z : Loc G, ((g'.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' (L.rep (u : G.C) x))
        (fun w => (g'.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) =
      ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) := by
    intro z
    have a1 : A.T' (L.rep (u : G.C) x) = fun w =>
        (G.rho w ((β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ A.T' x w := funext fun w => A.act' _ x w
    have a2 : (fun w => (g'.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) = fun w =>
        G.rho w (u : G.C) *ᵥ ((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) := by
      funext w
      rw [h2 w, Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
    rw [a1, a2, pairL_move G _ _ _ hM, ← _root_.mul_assoc, e1]
  refine and_congr (iff_of_eq (congrArg IntL (funext t1))) (forall_congr' fun z => imp_congr_right fun _ => ?_)
  rw [t2 z]

theorem UpperTheory.Gal.W2.pkEquiv_of :
    UpperTheory.Gal.W2.PkEquiv := by
  intro p _ D G L β A y g x
  exact mem_move A y.1.1 y.1.2 y.2.1 g _ x rfl (fun _ => rfl)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.pkTop_of :
    UpperTheory.Gal.W2.PFrameEx → UpperTheory.Gal.W2.PkLat → UpperTheory.Gal.W2.PkEquiv → UpperTheory.Gal.W2.PkPerf → UpperTheory.Gal.W2.PkInj → UpperTheory.Gal.W2.PkOnto → UpperTheory.Gal.W2.KpMem → UpperTheory.Gal.W2.PDicEx := by
  intro hF hLat hEq hPerf hInj hOnto hKp p _ D G L _ hm B
  obtain ⟨A⟩ := hF p D G L hm B.β B.sym
  let i : Gp G ≃* Gr G 1 := MulEquiv.ofBijective (inclG G 1) (GlobalTheory.TorCls.AtP.inclG_one_bijective G)
  have hi : ∀ g, i g = inclG G 1 g := fun _ => rfl
  choose M hM hMl using hLat p D G L B.β A hm
  refine ⟨{ lat := fun hp => M (i.symm hp), isLat := fun hp => hMl _, perf := ?_, equiv := ?_, inj := ?_, onto := ?_ }⟩
  · intro hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp1 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    set g := i.symm hp with hg
    set v : ℤ := (g.1 : ℚ_[p]).valuation with hv
    refine ⟨(p : ℚ) ^ (-v), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, ?_⟩
    refine hPerf p D G L B.β A g _ ?_ _ (hM g)
    have hne : (g.1 : ℚ_[p]) ≠ 0 := g.1.ne_zero
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hne, ← hv]
    push_cast
    rw [norm_zpow, Padic.norm_p, inv_zpow', neg_neg, ← zpow_add₀ hp1.ne']
    simp
  · intro y hp w
    have e : i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp) = locC G (y : G.Cˣ × ℚˣ) * i.symm hp := by
      rw [map_mul]
      congr 1
      exact i.symm_apply_apply (locC G (y : G.Cˣ × ℚˣ))
    change actY L y w ∈ M (i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp)) ↔ w ∈ M (i.symm hp)
    rw [e, hM, hM]
    exact hEq p D G L B.β A y _ w
  · intro hp hp'
    have e : hp⁻¹ * hp' = inclG G 1 ((i.symm hp)⁻¹ * i.symm hp') := by
      rw [← hi, map_mul, map_inv, i.apply_symm_apply, i.apply_symm_apply]
    change M (i.symm hp) = M (i.symm hp') ↔ _
    rw [e, hKp p G, ← hInj p D G L B.β A]
    constructor
    · intro h x
      rw [← hM, ← hM, h]
    · intro h
      ext x
      rw [hM, hM]
      exact h x
  · rintro N hN ⟨s, hs, hP⟩
    obtain ⟨g, hg⟩ := hOnto p D G L B.β A hm N s hN hs hP
    refine ⟨i g, ?_⟩
    change M (i.symm (i g)) = N
    rw [i.symm_apply_apply]
    ext x
    rw [hM, hg]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTrDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_inverse_different (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ↔
        ‖((a * d : K) : PadicAlgCl p)‖ ≤ 1 := by
  classical
  have hpos : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hmin : ∀ z : K, minpoly ℚ_[p] (z : PadicAlgCl p) = minpoly ℚ_[p] z := fun z =>
    minpoly.algebraMap_eq (algebraMap K (PadicAlgCl p)).injective z
  have hsv : ∀ z : K, ‖(z : PadicAlgCl p)‖ = spectralValue (minpoly ℚ_[p] z) := by
    intro z
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hmin]
  have hnat : ∀ m : ℕ, ‖(m : ℚ_[p])‖ ≤ 1 := fun m => by
    simpa using Padic.norm_int_le_one (p := p) (m : ℤ)
  have hTr : ∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K z‖ ≤ 1 := by
    intro z hz
    rw [hsv, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral z))] at hz
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
    have h2 : ‖(minpoly ℚ_[p] z).nextCoeff‖ ≤ 1 := by
      unfold Polynomial.nextCoeff
      split_ifs
      · simp
      · exact hz _
    calc _ ≤ 1 * 1 := mul_le_mul (hnat _) h2 (norm_nonneg _) zero_le_one
      _ = 1 := _root_.one_mul 1
  have hdisc : ∀ x : K, x ≠ 0 → ∃ j : ℤ,
      ‖(x : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j := by
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hdpos : 0 < (minpoly ℚ_[p] x).natDegree := minpoly.natDegree_pos hint
    have hdle : (minpoly ℚ_[p] x).natDegree ≤ Module.finrank ℚ_[p] K := minpoly.natDegree_le x
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
    have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
    have hx1 : ‖(x : PadicAlgCl p)‖ =
        ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[p] x).natDegree : ℝ)) := by
      rw [← PadicAlgCl.spectralNorm_eq,
        spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) (x : PadicAlgCl p),
        hmin]
    have hx2 : ‖(x : PadicAlgCl p)‖ ^ (minpoly ℚ_[p] x).natDegree = ‖(minpoly ℚ_[p] x).coeff 0‖ := by
      rw [hx1, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hdpos.ne']
    refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation * c, ?_⟩
    rw [hc, pow_mul, hx2, Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast, ← zpow_mul]
  have hn0 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  set c : ℚ_[p] := ((p : ℚ_[p]) * (Module.finrank ℚ_[p] K : ℕ))⁻¹ with hcdef
  have hbd : ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) →
        ‖(a : PadicAlgCl p)‖ < ‖c‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have ha0 : (a : PadicAlgCl p) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      exact absurd hlt (not_le.2 (norm_pos_iff.2 (inv_ne_zero (mul_ne_zero hp0 hn0))))
    have ha0' : a ≠ 0 := fun h => ha0 (by simp [h])
    have hz := ha (algebraMap ℚ_[p] K c * a⁻¹) (by
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv]
      have hcn : ‖((algebraMap ℚ_[p] K c : K) : PadicAlgCl p)‖ = ‖c‖ :=
        PadicAlgCl.norm_extends p c
      rw [hcn, ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 ha0)]
      exact hlt)
    have e2 : a * (algebraMap ℚ_[p] K c * a⁻¹) = algebraMap ℚ_[p] K c := by
      rw [_root_.mul_comm, _root_.mul_assoc, inv_mul_cancel₀ ha0', _root_.mul_one]
    rw [e2, Algebra.trace_algebraMap, nsmul_eq_mul] at hz
    have e3 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) * c = (p : ℚ_[p])⁻¹ := by
      rw [hcdef]
      field_simp
    rw [e3, norm_inv, Padic.norm_p, inv_inv] at hz
    linarith
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (‖c‖ ^ (Module.finrank ℚ_[p] K).factorial) hpos
  have hex := Int.exists_greatest_of_bdd (P := fun j : ℤ => ∃ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ∧ a ≠ 0 ∧
        ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j)
    ⟨B, fun j ⟨a, ha, _, hj⟩ => by
      have h1 : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial <
          ‖c‖ ^ (Module.finrank ℚ_[p] K).factorial :=
        pow_lt_pow_left₀ (hbd a ha) (norm_nonneg _) (Nat.factorial_ne_zero _)
      rw [hj] at h1
      have h2 : (p : ℝ) ^ j < (p : ℝ) ^ (B : ℤ) := by
        rw [zpow_natCast]
        exact h1.trans hB
      exact ((zpow_lt_zpow_iff_right₀ hpos).1 h2).le⟩
    ⟨0, 1, fun z hz => by rw [_root_.one_mul]; exact hTr z hz, one_ne_zero, by simp⟩
  obtain ⟨jm, ⟨am, hamD, ham0, hamj⟩, hmax⟩ := hex
  have hamn : (am : PadicAlgCl p) ≠ 0 := fun h => ham0 (by exact_mod_cast h)
  refine ⟨am⁻¹, inv_ne_zero ham0, fun a => ?_⟩
  have key : ‖((a * am⁻¹ : K) : PadicAlgCl p)‖ ≤ 1 ↔
      ‖(a : PadicAlgCl p)‖ ≤ ‖(am : PadicAlgCl p)‖ := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv,
      ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 hamn)]
  rw [key]
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · simp [ha0]
    obtain ⟨j, hj⟩ := hdisc a ha0
    have hjle := hmax j ⟨a, ha, ha0, hj⟩
    have hle : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial ≤
        ‖(am : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial := by
      rw [hj, hamj]
      exact zpow_le_zpow_right₀ hpos.le hjle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (Nat.factorial_ne_zero _)).1 hle
  · intro ha z hz
    have e : a * z = am * (am⁻¹ * a * z) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, mul_inv_cancel₀ ham0, _root_.one_mul]
    rw [e]
    apply hamD
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv,
      norm_mul, norm_mul, norm_inv]
    have h1 : ‖(am : PadicAlgCl p)‖⁻¹ * ‖(a : PadicAlgCl p)‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 hamn), _root_.mul_one]
      exact ha
    exact mul_le_one₀ h1 (norm_nonneg _) hz

theorem UpperTheory.Gal.W2.trDual_of :
    UpperTheory.Gal.W2.TrDual := by
  intro p _ G w
  exact exists_inverse_different p (G.Fw w)
end

