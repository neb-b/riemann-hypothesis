module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderSurjectsMatrixAlgebraModPrimePower
section
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.MatRed

theorem approx {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ) (x : M ⊗[ℤ] ℤ_[p]) :
    ∃ (b : M) (y : M ⊗[ℤ] ℤ_[p]), x = b ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul o z =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec r z)
    refine ⟨(z.appr r) • o, o ⊗ₜ w, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    congr 1
    rw [nsmul_eq_mul, nsmul_eq_mul, _root_.mul_one]
    push_cast
    linear_combination hw
  | add x y hx hy =>
    obtain ⟨a, u, ha⟩ := hx
    obtain ⟨b, v, hb⟩ := hy
    exact ⟨a + b, u + v, by rw [ha, hb, TensorProduct.add_tmul, smul_add]; abel⟩

theorem dvd_of_tmul {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (r : ℕ) (u : M) (z : M ⊗[ℤ] ℤ_[p]) (h : u ⊗ₜ (1 : ℤ_[p]) = (p ^ r) • z) :
    ∃ v : M, u = (p ^ r) • v := by
  let bs := Module.Free.chooseBasis ℤ M
  have hd : ∀ i, ((p ^ r : ℕ) : ℤ) ∣ bs.repr u i := by
    intro i
    let φ : M ⊗[ℤ] ℤ_[p] →ₗ[ℤ] ℤ_[p] :=
      (TensorProduct.lid ℤ ℤ_[p]).toLinearMap ∘ₗ TensorProduct.map (bs.coord i) LinearMap.id
    have h1 : φ (u ⊗ₜ (1 : ℤ_[p])) = ((bs.repr u i : ℤ) : ℤ_[p]) := by
      show (TensorProduct.lid ℤ ℤ_[p]) (TensorProduct.map (bs.coord i) LinearMap.id (u ⊗ₜ[ℤ] (1 : ℤ_[p]))) = _
      rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
      simp [zsmul_eq_mul]
    rw [h, map_nsmul] at h1
    have h2 := congrArg (PadicInt.toZModPow (p := p) r) h1
    rw [map_nsmul, map_intCast] at h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← h2, nsmul_eq_mul]
    simp
  choose k hk using hd
  refine ⟨∑ i, k i • bs i, ?_⟩
  conv_lhs => rw [← bs.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk i, mul_smul, natCast_zsmul]

theorem mem_smul_top_map {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) (f : X →ₗ[R] Y) {x : X} (hx : x ∈ I • (⊤ : Submodule R X)) :
    f x ∈ I • (⊤ : Submodule R Y) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem exists_matRed : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  intro p _ D w0 r _ hp
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e⟩ := D.splitP
  have hpr : (p : 𝓞 D.F) ^ r ∈ w0 ^ r := Ideal.pow_mem_pow hp r
  have hA : ((p ^ r : ℕ) : 𝓞 D.F ⧸ w0 ^ r) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hpr
    simpa using h
  let ψ₀ : ℤ_[p] →+* 𝓞 D.F ⧸ w0 ^ r :=
    (ZMod.castHom (ringChar.dvd hA) (𝓞 D.F ⧸ w0 ^ r)).comp (PadicInt.toZModPow r)
  let ψ : 𝓞 D.F ⊗[ℤ] ℤ_[p] →ₐ[𝓞 D.F] 𝓞 D.F ⧸ w0 ^ r :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (𝓞 D.F) (w0 ^ r)) ψ₀.toIntAlgHom
      (fun _ _ => Commute.all _ _)
  have hψ : ∀ c, ψ (c ⊗ₜ (1 : ℤ_[p])) = Ideal.Quotient.mk _ c := by
    intro c; simp [ψ, Algebra.TensorProduct.lift_tmul]
  have hψk : ∀ y, ψ y = 0 → y ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    intro y hy
    obtain ⟨c, z, rfl⟩ := approx r y
    rw [map_add (f := _), map_nsmul, hψ, nsmul_eq_mul, hA, zero_mul, add_zero] at hy
    have hc : c ∈ w0 ^ r := Ideal.Quotient.eq_zero_iff_mem.1 hy
    have h1 : c ⊗ₜ[ℤ] (1 : ℤ_[p]) = c • (1 : 𝓞 D.F ⊗[ℤ] ℤ_[p]) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (p ^ r) • z = ((p : 𝓞 D.F) ^ r) • z := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [h1, h2]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc trivial) (Submodule.smul_mem_smul hpr trivial)
  let incl : D.O →ₐ[𝓞 D.F] D.O ⊗[ℤ] ℤ_[p] := Algebra.TensorProduct.includeLeft
  have hincl : ∀ b, incl b = b ⊗ₜ (1 : ℤ_[p]) := fun b => rfl
  refine ⟨ψ.mapMatrix.comp (e.toAlgHom.comp incl), ?_, ?_⟩
  · intro N
    choose c hc using fun i j => Ideal.Quotient.mk_surjective (N i j)
    obtain ⟨b, y, hby⟩ := approx (M := D.O) r (e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])))
    refine ⟨b, ?_⟩
    have hb : incl b = e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])) - (p ^ r) • y := by
      rw [hby, hincl]; abel
    show ψ.mapMatrix (e (incl b)) = N
    rw [hb, map_sub, map_sub, map_nsmul, map_nsmul, e.apply_symm_apply]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, nsmul_eq_mul, hA, zero_mul, sub_zero]
    simp [AlgHom.mapMatrix_apply, hψ, hc]
  · intro b hb
    have hb' : ∀ i j, ψ (e (incl b) i j) = 0 := fun i j => by
      have h := congrFun (congrFun hb i) j
      simpa [AlgHom.mapMatrix_apply] using h
    have hM : e (incl b) ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]))) := by
      rw [Matrix.matrix_eq_sum_single (e (incl b))]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      exact mem_smul_top_map _ (Matrix.singleLinearMap (𝓞 D.F) i j) (hψk _ (hb' i j))
    have hO : incl b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])) := by
      have h := mem_smul_top_map _ e.symm.toLinearEquiv.toLinearMap hM
      simpa using h
    have claim : ∀ x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])),
        ∃ b' ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O), ∃ z : D.O ⊗[ℤ] ℤ_[p],
          x = b' ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • z := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro c hc x _
        obtain ⟨bx, y, rfl⟩ := approx r x
        refine ⟨c • bx, Submodule.smul_mem_smul hc trivial, c • y, ?_⟩
        rw [smul_add, TensorProduct.smul_tmul', smul_comm]
      · rintro x y ⟨a, ha, u, rfl⟩ ⟨a', ha', v, rfl⟩
        exact ⟨a + a', add_mem ha ha', u + v, by rw [TensorProduct.add_tmul, smul_add]; abel⟩
    obtain ⟨b', hb'', z, hz⟩ := claim _ hO
    rw [hincl] at hz
    have h3 : (b - b') ⊗ₜ[ℤ] (1 : ℤ_[p]) = (p ^ r) • z := by
      rw [TensorProduct.sub_tmul, hz]; abel
    obtain ⟨v, hv⟩ := dvd_of_tmul r (b - b') z h3
    have h4 : b = b' + ((p : 𝓞 D.F) ^ r) • v := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← hv]; abel
    rw [h4]
    exact add_mem hb'' (Submodule.smul_mem_smul hpr trivial)

end GlobalTheory.UPel.HT.MatRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferential
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartForm

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_coe (n : ℕ) (P : MvPolynomial (Fin d) O) :
    c.ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x n) P := by
  have h : (c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      MvPolynomial.aeval (c.x n) :=
    MvPolynomial.algHom_ext fun i => by
      simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (c.isEval n).1 i]
  have h2 := DFunLike.congr_fun h P
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using h2

theorem exists_split (n m : ℕ) (f : MvPowerSeries (Fin d) O) :
    ∃ (P : MvPolynomial (Fin d) O) (a : G.A n),
      c.ev n f = MvPolynomial.aeval (c.x n) P + (p : G.A n) ^ m * a ∧
      MvPolynomial.constantCoeff P = constantCoeff f ∧
      ∀ i, AddMonoidAlgebra.coeff P (Finsupp.single i 1) = lin f i := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 m
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => max N 2) f with hP
  have hle : ∀ α : Fin d →₀ ℕ, α.degree < max N 2 →
      α ≤ Finsupp.equivFunOnFinite.symm fun _ => max N 2 := by
    intro α hα i
    show α i ≤ max N 2
    exact (Finsupp.le_degree i α).trans hα.le
  obtain ⟨a, ha⟩ := hN (f - P) fun α hα => by
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc',
      if_pos (hle α (lt_of_lt_of_le hα (le_max_left _ _))), sub_self]
  refine ⟨P, a, ?_, ?_, fun i => ?_⟩
  · rw [← ev_coe, ← ha, ← map_add (f := _), add_sub_cancel]
  · rw [MvPolynomial.constantCoeff_eq, hP, coeff_trunc',
      if_pos (hle 0 (by simp)), coeff_zero_eq_constantCoeff_apply]
  · rw [hP, coeff_trunc', if_pos (hle _ (lt_of_lt_of_le (by simp) (le_max_right N 2))), lin]

theorem eq_zero_of_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ m, (p : O) ^ m ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun m => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h m

theorem counit_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (MvPolynomial.aeval (c.x n) P) =
      MvPolynomial.constantCoeff P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h : (fun i => Bialgebra.counitAlgHom O (G.A n) (c.x n i)) = 0 :=
    funext fun i => by simpa using c.aug n i
  rw [h, MvPolynomial.aeval_zero]
  rfl

theorem counit_ev [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ)
    (f : MvPowerSeries (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n f) = constantCoeff f := by
  refine sub_eq_zero.1 (eq_zero_of_dvd (p := p) _ fun m => ?_)
  obtain ⟨P, a, h1, h2, -⟩ := (exists_split c) n m f
  rw [h1, map_add (f := _), counit_aeval, h2, map_mul, map_pow, map_natCast, add_sub_cancel_left]
  exact dvd_mul_right _ _

theorem d_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    PDiv.dUnit (R := O) (MvPolynomial.aeval (c.x n) P) =
      ∑ i, AddMonoidAlgebra.coeff P (Finsupp.single i 1) • PDiv.dUnit (R := O) (c.x n i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : ∀ x : Fin d, ¬ (0 : Fin d →₀ ℕ) = Finsupp.single x 1 := fun x h =>
      (Finsupp.single_ne_zero.2 one_ne_zero) h.symm
    rw [MvPolynomial.aeval_C]
    simp [MvPolynomial.coeff_C, PDiv.dUnit, h0]
  | add P Q hP hQ =>
    unfold PDiv.dUnit at *
    rw [map_add (f := _), map_add (f := _), hP, hQ, ← Finset.sum_add_distrib]
    simp [add_smul]
  | mul_X P j h =>
    have hc : ∀ i, AddMonoidAlgebra.coeff (P * MvPolynomial.X j) (Finsupp.single i 1) =
        if j = i then MvPolynomial.constantCoeff P else 0 := by
      intro i
      rw [MvPolynomial.coeff_mul_X']
      by_cases hij : j = i
      · subst hij; simp [MvPolynomial.constantCoeff_eq]
      · simp [hij, Finsupp.support_single_ne_zero]
    simp only [hc, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hx : Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := by simpa using c.aug n j
    rw [map_mul, MvPolynomial.aeval_X, PDiv.dUnit, AugCot.d_mul, counit_aeval, hx, zero_smul,
      add_zero]

theorem d_ev (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  obtain ⟨P, a, h1, -, h3⟩ := (exists_split c) n n f
  have h4 : AugCot.d (Bialgebra.counitAlgHom O (G.A n)) ((p : G.A n) ^ n * a) = 0 := by
    rw [show (p : G.A n) ^ n * a = ((p : O) ^ n) • a by
      rw [Algebra.smul_def, map_pow, map_natCast], map_smul]
    exact G.pow_smul_cot n _
  rw [h1, PDiv.dUnit, map_add (f := _), h4, add_zero, ← PDiv.dUnit, (d_aeval c)]
  simp only [h3]

theorem coeff_single_of_mem_sq {h : MvPowerSeries (Fin d) O}
    (hh : h ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) (i : Fin d) :
    coeff (Finsupp.single i 1) h = 0 := by
  rw [pow_two] at hh
  refine Submodule.mul_induction_on hh (fun f hf g hg => ?_) (fun f g hf hg => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg := congrArg Finsupp.degree hq
    rw [map_add (f := _), Finsupp.degree_single] at hdeg
    rcases (show q.1.degree = 0 ∨ q.2.degree = 0 by omega) with h0 | h0
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hf, zero_mul]
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hg, mul_zero]
  · rw [map_add (f := _), hf, hg, add_zero]

def lvl (n : ℕ) : (Fin d → O) →ₗ[O] PDiv.Cot O (G.A n) :=
  Fintype.linearCombination O fun i => PDiv.dUnit (R := O) (c.x n i)

theorem lvl_apply (n : ℕ) (a : Fin d → O) :
    lvl c n a = ∑ i, a i • PDiv.dUnit (R := O) (c.x n i) := Fintype.linearCombination_apply ..

theorem val_comb (a : Fin d → O) (n : ℕ) :
    (Fintype.linearCombination O c.form a).1 n = lvl c n a := by
  rw [Fintype.linearCombination_apply, lvl_apply]
  simp [QLog.Chart.form]

theorem res_lvl (n : ℕ) (a : Fin d → O) :
    PDiv.cotMap (G.res n) (lvl c (n + 1) a) = lvl c n a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lvl_apply, map_sum, map_smul, PDiv.cotMap_d, c.res]

theorem lvl_le (w : G.omega) (a : Fin d → O) {n k : ℕ} (h : n ≤ k)
    (hk : lvl c k a = w.1 k) : lvl c n a = w.1 n := by
  revert hk
  induction k, h using Nat.le_induction with
  | base => exact id
  | succ k hnk ih => exact fun hk => ih (by rw [← res_lvl c, hk, w.2 k])

theorem exists_level_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (m : ℕ) :
    ∃ n, ∀ a : Fin d → O, lvl c n a = 0 → ∀ i, (p : O) ^ m ∣ a i := by
  obtain ⟨n, hn⟩ := c.ker m 2
  refine ⟨n, fun a ha i => ?_⟩
  set y : G.A n := ∑ j, a j • c.x n j with hy0
  have hx : ∀ j, Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := fun j => by
    simpa using c.aug n j
  have hεy : Bialgebra.counitAlgHom O (G.A n) y = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hy0, map_sum, map_smul, hx]
  have hy : PDiv.dUnit (R := O) y = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy0, PDiv.dUnit, map_sum]
    simpa [map_smul, lvl_apply] using ha
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff, hεy, map_zero, sub_zero] at hy
  have hI : RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ≤
      Ideal.map (c.ev n) (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O)) := by
    intro z hz
    obtain ⟨g, rfl⟩ := c.surj n z
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, ← counit_ev c]
    exact hz
  have hy2 : y ∈ Ideal.map (c.ev n)
      (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hI 2 hy
  obtain ⟨h, hh, hev⟩ := (Ideal.mem_map_iff_of_surjective _ (c.surj n)).1 hy2
  have hz : c.ev n ((∑ j, a j • X j) - h) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hev, map_sum, hy0]
    simp [map_smul, (c.isEval n).1]
  have := hn _ hz (Finsupp.single i 1) (by simp)
  rw [map_sub, coeff_single_of_mem_sq hh, sub_zero] at this
  classical
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero] using this

theorem comb_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (Fintype.linearCombination O c.form) := by
  choose nm hnm using (exists_level_dvd c)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    funext i
    refine eq_zero_of_dvd _ fun m => hnm m a ?_ i
    rw [← val_comb c, ha]
    rfl
  · intro w
    have hb : ∀ k, ∃ b : Fin d → O, lvl c k b = w.1 k := by
      intro k
      obtain ⟨y, hy⟩ := AugCot.d_surjective _ (w.1 k)
      obtain ⟨g, rfl⟩ := c.surj k y
      exact ⟨lin g, by rw [lvl_apply, ← d_ev c]; exact hy⟩
    choose b hb using hb
    let K : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nm j
    have hK : ∀ {m n}, m ≤ n → K m ≤ K n := fun h =>
      add_le_add h (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h)))
    have hnK : ∀ m, nm m ≤ K m := fun m =>
      le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (nm j))
        (Finset.self_mem_range_succ m))
    have hnK' : ∀ m, m ≤ K m := fun m => Nat.le_add_right _ _
    have hcauchy : ∀ {m n}, m ≤ n → ∀ i, (p : O) ^ m ∣ b (K m) i - b (K n) i := by
      intro m n hmn i
      refine hnm m (b (K m) - b (K n)) ?_ i
      rw [map_sub, (lvl_le c) w _ (hnK m) (hb _), (lvl_le c) w _ ((hnK m).trans (hK hmn)) (hb _),
        sub_self]
    have hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ b (K n) i - L := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)})
        (fun m => b (K m) i) fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          exact hcauchy hmn i
      refine ⟨L, fun n => ?_⟩
      have h1 := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h1
      exact h1
    choose L hL using hL
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    change (Fintype.linearCombination O c.form L).1 n = w.1 n
    rw [(val_comb c)]
    choose v hv using fun i => hL i n
    have hLv : L = b (K n) - (p : O) ^ n • v := by
      funext i
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv i]
      ring
    rw [hLv, map_sub, map_smul, G.pow_smul_cot, sub_zero]
    exact (lvl_le c) w _ (hnK' n) (hb _)

end GlobalTheory.ChartForm

theorem GlobalTheory.chart_form_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c
  exact ⟨ChartForm.comb_bijective c, fun n f _ => ChartForm.d_ev c n f⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdEvalTruncOfHighOrder
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem trunc'_eval_dvd_of_order :
    ∀ (p : ℕ) (B : Type) [CommRing B] (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B),
      (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∃ L : ℕ, ∀ (k : ℕ) (h : MvPowerSeries σ B),
        (∀ α : σ →₀ ℕ, α.degree < L * k → coeff α h = 0) →
          ∀ n : σ →₀ ℕ, (p : B) ^ k ∣ MvPolynomial.eval z (trunc' B n h) := by
  intro p B _ σ _ _ z hz
  choose N hN using hz
  set N₀ : ℕ := ∑ i, N i + 1 with hN₀
  have hdiv : ∀ i, (p : B) ∣ z i ^ N₀ := by
    intro i
    have hle : N i ≤ N₀ := by
      have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    exact (hN i).trans (pow_dvd_pow _ hle)
  refine ⟨Fintype.card σ * N₀ + 1, ?_⟩
  intro k h hh n
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [MvPolynomial.eval_eq]
  apply Finset.dvd_sum
  intro β _
  rw [coeff_trunc']
  split_ifs with hβ
  · by_cases hc : coeff β h = 0
    · simp [hc]
    · have hdeg : ¬ β.degree < (Fintype.card σ * N₀ + 1) * k := fun hlt => hc (hh β hlt)
      have : ∃ i, N₀ * k ≤ β i := by
        by_contra hne
        push_neg at hne
        apply hdeg
        rw [Finsupp.degree_eq_sum]
        calc ∑ i, β i ≤ ∑ _i : σ, N₀ * k := Finset.sum_le_sum (fun i _ => (hne i).le)
          _ = Fintype.card σ * N₀ * k := by simp [Finset.sum_const, mul_assoc]
          _ < (Fintype.card σ * N₀ + 1) * k := by nlinarith
      obtain ⟨i, hi⟩ := this
      apply Dvd.dvd.mul_left
      have h1 : (p : B) ^ k ∣ z i ^ β i := by
        calc (p : B) ^ k ∣ (z i ^ N₀) ^ k := pow_dvd_pow_of_dvd (hdiv i) k
          _ = z i ^ (N₀ * k) := (pow_mul _ _ _).symm
          _ ∣ z i ^ β i := pow_dvd_pow _ hi
      have hmem : i ∈ β.support := by
        rw [Finsupp.mem_support_iff]
        have : 1 ≤ N₀ * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        omega
      exact h1.trans (Finset.dvd_prod_of_mem _ hmem)
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefects
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  intro Q q _ hqQ U u₁ u₂ hQ a b ha hb
  refine (_root_.GlobalTheory.EtC.sec_ext_glue _ ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  have h1 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₁
  have h2 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₂
  refine GlobalTheory.EtC.RedChern.loc_mono (GlobalTheory.EtC.RedChern.loc_and h1 h2) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  have hvq : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₁ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  have hwq : (w ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₂ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hw]
  have hvw : (v * w) ^ Q = Units.map g.appTop.hom.toMonoidHom (u₁ * u₂) := by
    rw [mul_pow, hv, hw, map_mul]
  have ea := ha V g v w hv hw
  have eb := hb V g _ _ hvq hwq
  have d1 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₁ hQ V g v hv
  have d2 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₂ hQ V g w hw
  have d3 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U (u₁ * u₂) hQ V g (v * w) hvw
  have en := (redMap Q q 1).nat g 0 a
  have hsub : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x - y) = Sec.res g x - Sec.res g y := fun x y => map_sub _ x y
  have hadd : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x + y) = Sec.res g x + Sec.res g y := fun x y => map_add _ x y
  rw [hsub, hadd, hsub, en, ea, eb, d1, d2, d3]
  simp only [GlobalTheory.EtC.RedChern.defect, map_sub, map_add (f := _), mul_pow]
  abel
end

