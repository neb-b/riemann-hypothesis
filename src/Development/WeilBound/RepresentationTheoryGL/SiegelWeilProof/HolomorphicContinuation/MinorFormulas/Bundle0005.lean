module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeH
section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem hasDerivAt_line (x v : MC n) : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x

theorem det_affine_eventually (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    ∀ᶠ t : ℂ in 𝓝 0, (M0 + t • A).det ≠ 0 := by
  have hc : Continuous fun t : ℂ => (M0 + t • A).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have : (fun t : ℂ => (M0 + t • A).det) 0 ≠ 0 := by simpa using h
  exact hc.continuousAt.eventually_ne this

theorem inv_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0)
    (hdiff : ∀ a d, DifferentiableAt ℂ (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0) (a d : Fin n) :
    HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) ((-(M0⁻¹ * A * M0⁻¹)) a d) 0 := by
  set D : Matrix (Fin n) (Fin n) ℂ := fun a d => deriv (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0 with hD
  have hY : ∀ a d, HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) (D a d) 0 := fun a d => (hdiff a d).hasDerivAt

  have hid : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) ((A * M0⁻¹ + M0 * D) i j) 0 := by
    intro i j
    have e : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =
        fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j := by
      funext t; simp [Matrix.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j)
        (∑ k, (A i k * M0⁻¹ k j + M0 i k * D k j)) 0 := by
      apply HasDerivAt.fun_sum
      intro k _
      have h1 : HasDerivAt (fun t : ℂ => M0 i k + t * A i k) (A i k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (A i k)).const_add (M0 i k)
      simpa using h1.fun_mul (hY k j)
    convert hs using 1
    simp [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]
  have hconst : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) 0 0 := by
    intro i j
    have hev : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =ᶠ[𝓝 0] fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      filter_upwards [det_affine_eventually M0 A h] with t ht
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]
    exact (hasDerivAt_const (0 : ℂ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq hev
  have hzero : A * M0⁻¹ + M0 * D = 0 := by
    ext i j
    exact (hid i j).unique (hconst i j)
  have hDv : D = -(M0⁻¹ * A * M0⁻¹) := by
    have h1 : M0⁻¹ * M0 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
    have h2 : M0 * D = -(A * M0⁻¹) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero
    calc D = M0⁻¹ * M0 * D := by rw [h1, Matrix.one_mul]
      _ = M0⁻¹ * (M0 * D) := by rw [Matrix.mul_assoc]
      _ = -(M0⁻¹ * A * M0⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← hDv]
  exact hY a d

theorem mX (s : ℂ) (x v : MC n) (t : ℂ) :
    1 - (Complex.I * s) • Matrix.of (x + t • v) = (1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mY (s : ℂ) (x v : MC n) (t : ℂ) :
    1 + (Complex.I * s) • Matrix.of (x + t • v) = (1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem diff_inv_X (s : ℂ) (x v : MC n) (h : (1 - (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_X (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mX s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt

theorem diff_inv_Y (s : ℂ) (x v : MC n) (h : (1 + (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_Y (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mY s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt

theorem hYm : HYm := by
  intro n s x v h a d
  have e : (fun t : ℂ => Ym s (x + t • v) a d) =
      fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Ym]
    rw [mX s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_X s x v h) a d
  convert this using 1
  simp only [Ym, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring

theorem hYp : HYp := by
  intro n s x v h a d
  have e : (fun t : ℂ => Yp s (x + t • v) a d) =
      fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Yp]
    rw [mY s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_Y s x v h) a d
  convert this using 1
  simp only [Yp, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDiv
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

def Sop (s : ℂ) (m n : ℕ) : Set (Module.End ℂ (Fm n)) :=
  Set.range fun x : Bool × Fin n × Fin n => opH s m x.1 x.2.1 x.2.2

theorem list_prod_eq_foldr {ρ : ℕ} (f : Fin ρ → Module.End ℂ (Fm n)) (L : List (Fin ρ)) :
    (L.map f).prod = L.foldr (fun k g => f k ∘ₗ g) LinearMap.id := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Module.End.mul_eq_comp]; rfl

theorem rcp_adjoin (s : ℂ) (m : ℕ) {T : Module.End ℂ (Fm n)} (hT : T ∈ Algebra.adjoin ℂ (Sop s m n)) : RCP T := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact opH_rcp s m _ _ _
  | algebraMap r =>
    intro R q
    simp only [Module.algebraMap_end_apply, smul_mul_assoc]
  | add x y _ _ hx hy => exact rcp_add hx hy
  | mul x y _ _ hx hy => rw [Module.End.mul_eq_comp]; exact rcp_comp hx hy

theorem divZ_mono {i j : ℕ} {Q : Fm n} (hQ : DivZ i Q) (h : j ≤ i) : DivZ j Q := fun e =>
  (pow_dvd_pow _ h).trans (hQ e)

theorem cayDiv_of : CayDivOf := by
  intro hC hMZ hMZ' hNull n m s hs hm
  classical
  have hcomm : ∀ a ∈ Sop s m n, ∀ b ∈ Sop s m n, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hC n s m x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2
  letI : IsMulCommutative (Algebra.adjoin ℂ (Sop s m n)) :=
    Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing (Algebra.adjoin ℂ (Sop s m n)) := by
    open scoped IsMulCommutative in exact inferInstance
  let g : Bool × Fin n × Fin n → Algebra.adjoin ℂ (Sop s m n) :=
    fun x => ⟨opH s m x.1 x.2.1 x.2.2, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let φ : PAB n →ₐ[ℂ] Algebra.adjoin ℂ (Sop s m n) := MvPolynomial.aeval g
  have hφX : ∀ x, ((φ (X x) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = opH s m x.1 x.2.1 x.2.2 :=
    fun x => by simp [φ, g]
  have hcoe_det : ∀ {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) (Algebra.adjoin ℂ (Sop s m n))),
      ((M.det : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) =
        ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (List.finRange ρ).foldr (fun k g => ((M k (σ k) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) ∘ₗ g)
            LinearMap.id := by
    intro ρ M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    change (Algebra.adjoin ℂ (Sop s m n)).val _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, Fin.prod_univ_def, map_list_prod, List.map_map,
      ← list_prod_eq_foldr]
    rfl
  have hcoe_minor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n),
      ((φ (minorPolynomial b I J) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = minorOp s m b I J := by
    intro b ρ I J
    rw [show minorPolynomial b I J = Matrix.det (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n)) from rfl,
      AlgHom.map_det, hcoe_det]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hφX]
    rfl
  have hcoe_cay : ((φ (Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))) :
      Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = cayF s m := by
    rw [show Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) =
        Matrix.det (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) from rfl,
      AlgHom.map_det, hcoe_det]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_add (f := _), Subalgebra.coe_add, hφX]
    rfl
  have hpow : ∀ (x : Algebra.adjoin ℂ (Sop s m n)) (N : ℕ) (Q : Fm n),
      ((x ^ N : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) Q = (x : Module.End ℂ (Fm n))^[N] Q := by
    intro x N Q
    rw [SubmonoidClass.coe_pow, Module.End.pow_apply]
  have hdivA : ∀ (x : Algebra.adjoin ℂ (Sop s m n)) {i : ℕ} {Q : Fm n}, DivZ i Q →
      DivZ i ((x : Module.End ℂ (Fm n)) Q) := fun x _ _ hQ => divZ_of_rcp (rcp_adjoin s m x.2) hQ
  have hr0 : 0 < n - m := Nat.sub_pos_of_lt hm
  obtain ⟨N₁, hN₁⟩ := hNull n m hm (n - m)
  refine ⟨N₁, fun N hN => ?_⟩
  have hmem := Ideal.mul_mem_left _
    ((Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))) ^ (N - N₁)) hN₁
  rw [pow_sub_mul_pow _ hN] at hmem
  have H := Submodule.span_induction
    (p := fun x _ => DivZ (n - m) (((φ x : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) 1))
    ?mem ?zero ?add ?smul hmem
  · rw [map_pow, hpow, hcoe_cay] at H
    exact H
  case mem =>
    intro x hx
    obtain ⟨i, j, hij, hcase⟩ := hx
    rcases hcase with ⟨hi, hj, rfl⟩ | ⟨hi, hj, I, J, rfl⟩ | ⟨hi, hj, I, J, rfl⟩ | ⟨hi, hj, I, J, I', J', rfl⟩
    · omega
    · rw [map_pow, hpow, hcoe_minor]
      exact divZ_mono (hMZ' n s hs m j (n - m) (by omega) I J) (by omega)
    · rw [map_pow, hpow, hcoe_minor]
      exact divZ_mono (hMZ n s hs m i (n - m) (by omega) I J) (by omega)
    · rw [map_mul, map_pow, map_pow, Subalgebra.coe_mul, Module.End.mul_apply, hpow, hpow, hcoe_minor, hcoe_minor]
      have hAT : (minorOp s m true I' J')^[n - m] 1 ∈ AT n :=
        iterate_AT (fun Q hQ => minorOp_true_AT s m I' J' hQ) _ (Subalgebra.one_mem _)
      have hpd := pderiv_false_AT hAT
      rw [← mul_one ((minorOp s m true I' J')^[n - m] 1), lcp_iterate (minorOp_false_lcp s m I J hpd)]
      exact divZ_mono (divZ_mul (hMZ' n s hs m j (n - m) (by omega) I' J') (hMZ n s hs m i (n - m) (by omega) I J))
        (by omega)
  case zero => simp [divZ_zero]
  case add =>
    intro x y _ _ hx hy
    rw [map_add (f := _), Subalgebra.coe_add, LinearMap.add_apply]
    exact divZ_add hx hy
  case smul =>
    intro a x _ hx
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]
    exact hdivA _ hx

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOf
section
noncomputable section

open MeasureTheory Matrix Filter Topology Metric

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z PositivityTheory.Rg.Sw.WR.T

theorem sPrime_of' (hB : ClsBound) (hGain : ClsGain) (hIBP : IBP) (hI : Integr) (hCh : Chain) (hE : Ext) :
    SPrimeOf := by
  intro hBr hCD n m s hs hmn t ht β hβ
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨N₁, hN₁⟩ := hCD n m s hs hmn
  have hGN := fun N => hGain n s hs m 0 N 1
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((m + 0 + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, cls s z m 0 1 y * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((m + 0 + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))
  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z m 0 1)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z m 0 1)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hgood : ∀ z : ℂ, (n : ℝ) ^ 2 / 2 < z.re → Good (cls (n := n) s z m 0 1) := by
    intro z hz
    have hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2 := by positivity
    refine ⟨(hB n s hs m 0 1 z).1, fun L => ?_⟩
    obtain ⟨C, hC⟩ := (hB n s hs m 0 1 z).2 L
    exact ⟨fun y => C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, cls s z m 0 1 y * chr t β y
    rw [ibp_iter hIBP (hgood z hz) t β ht hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((m + 0 + N : ℕ) : ℝ) ≤ ((m + 0 + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((m + 0 + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith

  set Ns : ℕ := max (n ^ 2 + 3) N₁ with hNs
  have hdiv : DivZ (n - m) ((cayF (n := n) s m)^[Ns] 1) := hN₁ Ns (le_max_right _ _)
  have hNs3 : ((n ^ 2 + 3 : ℕ) : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast le_max_left _ _
  set κ : ℝ := ((m + 0 + Ns : ℕ) : ℝ) / 2 with hκ
  have hκ1 : (n : ℝ) ^ 2 / 2 + 1 < κ := by
    rw [hκ]; push_cast at hNs3 ⊢
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hball : ball (0 : ℂ) 1 ⊆ U Ns := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    show (n : ℝ) ^ 2 / 2 < z.re + κ
    have := Complex.abs_re_le_norm z
    have := neg_abs_le z.re
    linarith

  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ w ∈ closedBall (0 : ℂ) 1, ‖∑ j, ‖(a Ns j).eval w‖‖ ≤ A :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (continuous_finsetSum _ fun j _ => (Polynomial.continuous _).norm).continuousOn
  set CGp : ℝ := max (CG Ns) 0 with hCGp
  set M : E n → ℝ := fun y => A * CGp * (dP y ^ (1 - κ) + dP y ^ (-1 - κ)) with hM
  have hMint : Integrable M := by
    have h1 := hint (κ - 1) (by linarith)
    have h2 := hint (κ + 1) (by linarith)
    refine ((h1.add h2).const_mul (A * CGp)).congr (ae_of_all _ fun y => ?_)
    simp only [hM, Pi.add_apply]
    congr 2 <;> congr 1 <;> ring
  have hpt : ∀ (y : E n) (z : ℂ), ‖z‖ ≤ 1 → ‖(Delta^[Ns] (cls s z m 0 1)) y‖ ≤ ‖z‖ ^ (n - m) * M y := by
    intro y z hz
    obtain ⟨q, hqd, hq⟩ := factor hE hCh hBr hs m Ns (n - m) hdiv y
    have hp := dP_pos hI y
    have hcircle : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ (n - m) * q w‖ ≤ M y := by
      intro w hw
      rw [← hq w, hGeq Ns w y, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
      have hre : |w.re - 0| ≤ 1 := by rw [sub_zero]; exact (Complex.abs_re_le_norm w).trans hw.le
      have r1 := rpow_neg_le_add (dP y) w.re 0 1 hp hre
      have hs1 : ‖∑ j, (a Ns j).eval w * G Ns j y‖ ≤ A * (CGp * dP y ^ (-κ)) := by
        refine (norm_sum_le _ _).trans ?_
        have hb1 : ∀ j, ‖(a Ns j).eval w * G Ns j y‖ ≤ ‖(a Ns j).eval w‖ * (CGp * dP y ^ (-κ)) := by
          intro j
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((hCG' Ns j y).trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _)
        refine (Finset.sum_le_sum fun j _ => hb1 j).trans ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hp.le _))
        have := hA w (by rw [mem_closedBall_zero_iff]; exact hw.le)
        rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at this
      calc dP y ^ (-w.re) * ‖∑ j, (a Ns j).eval w * G Ns j y‖
          ≤ (dP y ^ (-(0 - 1)) + dP y ^ (-(0 + 1))) * (A * (CGp * dP y ^ (-κ))) :=
            mul_le_mul r1 hs1 (norm_nonneg _) (by positivity)
        _ = M y := by
            rw [hM]
            have e1 : dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (1 - κ) := by
              rw [← Real.rpow_add hp]; congr 1; ring
            have e2 : dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (-1 - κ) := by
              rw [← Real.rpow_add hp]; congr 1; ring
            simp only []
            calc (dP y ^ (-(0 - 1 : ℝ)) + dP y ^ (-(0 + 1 : ℝ))) * (A * (CGp * dP y ^ (-κ)))
                = A * CGp * (dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) + dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ)) := by ring
              _ = _ := by rw [e1, e2]
    have hqz := norm_le_of_circle hqd hcircle hz
    rw [hq z, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hqz (by positivity)
  have hWbound : ∀ z ∈ ball (0 : ℂ) 1, ‖WN Ns z‖ ≤ (‖KK‖ ^ Ns * ∫ y, M y) * ‖z‖ ^ (n - m) := by
    intro z hz
    have hzU := hball hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have e : WN Ns z = KK ^ Ns * ∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y := by
      show KK ^ Ns * _ = _
      rw [hsum Ns z hzU]
    rw [e, norm_mul, norm_pow]
    have hi : ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ∫ y, ‖z‖ ^ (n - m) * M y := by
      refine norm_integral_le_of_norm_le (hMint.const_mul _) (ae_of_all _ fun y => ?_)
      rw [norm_mul, norm_chr, mul_one]
      exact hpt y z hz1
    rw [integral_const_mul] at hi
    calc ‖KK‖ ^ Ns * ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ‖KK‖ ^ Ns * (‖z‖ ^ (n - m) * ∫ y, M y) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · obtain ⟨C, hC⟩ := (hB n s hs m 0 1 z).2 []
    have hC0 : ∀ y : E n, ‖cls s z m 0 1 y‖ ≤ C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)) := by
      intro y
      have := hC y
      simpa using this
    have hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2 := by positivity
    refine Integrable.mono' ((hint (z.re + ((m : ℝ) + (0 : ℕ)) / 2) (by linarith)).const_mul C)
      (((hB n s hs m 0 1 z).1.continuous.mul (continuous_chr t β)).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, norm_chr, mul_one]
    exact hC0 y
  · exact hbig (Nf z) z hz
  · intro j hj
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 0] WN Ns :=
      Filter.eventuallyEq_of_mem ((hUopen Ns).mem_nhds (hball (mem_ball_self one_pos))) fun z hz =>
        agree' _ _ z (hNf z) hz
    rw [hev.iteratedDeriv_eq]
    exact iteratedDeriv_zero_of_bound one_pos ((hWdiff Ns).mono hball) hWbound hj

end PositivityTheory.Rg.Sw.SP
end
end

