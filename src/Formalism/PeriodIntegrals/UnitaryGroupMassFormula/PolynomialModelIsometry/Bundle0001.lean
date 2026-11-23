module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Assembly
section
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

lemma det_ne_zero_of_mem_K {N : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) :
    g.det ≠ 0 := by
  have h1 := hg.1
  rw [Matrix.mem_unitaryGroup_iff] at h1
  intro h0
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

lemma detPoly_ne_zero (N : ℕ) : detPoly N ≠ 0 := by
  intro h
  have := congrArg (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)) h
  rw [detPoly, RingHom.map_det, map_zero] at this
  have hm : (eval (fun ij : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2)).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext i j; simp
  rw [hm, det_one] at this
  exact one_ne_zero this

lemma rowAct_detPoly {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    rowAct ℂ (n := N) A (detPoly N) = C A.det * detPoly N := by
  have h1 : (rowAct ℂ (n := N) A).mapMatrix
      (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix A *
        Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ) := by
    ext i j
    simp [rowAct, Matrix.mul_apply]
  rw [detPoly, AlgHom.map_det, h1, Matrix.det_mul, ← RingHom.map_det]

theorem modelIso_of_steps (hA : PolyExt) (hI : LamInt) (hT : TorusEig) (hL : LowerInv)
    (hM : ModelMap) (hD : DetSplit) (hH : PI.HwIrred) : PI.ModelIso := by
  intro N Λ H _ _ σ S hU hK
  obtain ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩ := hK
  have hK' : IsKTypeOf (allPos N) σ Λ S := ⟨hfin, hstab, hirr, ⟨v0, hv0S, hv0ne, hv0w⟩, hdom⟩
  haveI := hfin
  obtain ⟨K, P, hP, hPσ⟩ := hA N H σ S hU hfin hstab
  choose μ hμ using hI N Λ H σ v0 hU hv0ne hv0w
  let w0 : S := ⟨v0, hv0S⟩
  have hw0ne : w0 ≠ 0 := by
    intro h; apply hv0ne
    have := congrArg Subtype.val h
    simpa [w0] using this
  have hT' := hT N Λ H σ S K P hU hstab hPσ w0 hv0w
  have hL' := hL N Λ H σ S K P hU hK' hP hPσ w0 hv0w
  have hT'' : ∀ (θ : Fin N → ℝ) (x : S), ⟪w0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪w0, x⟫_ℂ := by
    intro θ x; rw [hT' θ x]; simp only [hμ]
  obtain ⟨ν, F, hν, hFmem, hF0, hFint⟩ := hM N S P w0 μ K hP hw0ne hT'' hL'
  have hanti : Antitone ν := by
    intro l j hlj
    by_contra hlt
    push_neg at hlt
    rcases eq_or_lt_of_le hlj with h | h
    · subst h; exact lt_irrefl _ hlt
    · have hbot := dualWeylNonDom ℂ N N ν ⟨l, j, h, hlt⟩
      have := hFmem w0
      rw [hbot, Submodule.mem_bot] at this
      exact hF0 this
  have hμanti : Antitone μ := by
    intro a b hab
    have h1 := hν a
    have h2 := hν b
    have h3 : (ν b : ℤ) ≤ ν a := by exact_mod_cast hanti hab
    omega
  let lam : DomWeight N := ⟨μ, hμanti⟩
  refine ⟨lam, fun a => hμ a, ?_⟩
  let c : ℕ := if h : 0 < N then ν ⟨N - 1, by omega⟩ else 0
  have hnat : ∀ a, lam.natW a + c = ν a := by
    intro a
    have hN : 0 < N := a.pos
    have h1 := hν a
    have h2 := hν ⟨N - 1, by omega⟩
    have h3 : ν ⟨N - 1, by omega⟩ ≤ ν a := hanti (by rw [Fin.le_def]; simp; omega)
    have h3' : (ν ⟨N - 1, by omega⟩ : ℤ) ≤ ν a := by exact_mod_cast h3
    simp only [DomWeight.natW, DomWeight.detShift, c, dif_pos hN, lam]
    omega
  have hlast : ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 := by
    intro h; simp [DomWeight.natW, DomWeight.detShift, h, lam]
  have hsplit := hD N lam.natW c hlast
  have hνeq : (fun a => lam.natW a + c) = ν := funext hnat
  have hFmem' : ∀ x, F x ∈ dualWeyl ℂ N N (fun a => lam.natW a + c) := by
    intro x; rw [hνeq]; exact hFmem x
  let mulD : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ :=
    LinearMap.mulLeft ℂ (detPoly N ^ c)
  have hmulD_inj : Function.Injective mulD := by
    intro f g hfg
    simp only [mulD, LinearMap.mulLeft_apply] at hfg
    exact mul_left_cancel₀ (pow_ne_zero _ (detPoly_ne_zero N)) hfg
  let U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    nablaSq ℂ N lam ⊓ (LinearMap.range F).comap mulD
  have hUst : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U := by
    intro g f hf
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hf2)
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · unfold sqAct
      exact Submodule.smul_mem _ _ (dualWeylRowStable ℂ N N _ _ f hf1)
    · set dg := (g : Matrix (Fin N) (Fin N) ℂ).det with hdgdef
      have hdg : dg ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr
        ⟨(detPow ℂ N g lam.detShift * (dg ^ c)⁻¹) • P (g : Matrix (Fin N) (Fin N) ℂ) x, ?_⟩)
      rw [map_smul, hFint, hx]
      simp only [mulD, LinearMap.mulLeft_apply, sqAct]
      rw [map_mul, map_pow, rowAct_detPoly, Matrix.det_transpose]
      have key : C ((dg ^ c)⁻¹) * C dg ^ c = (1 : MvPolynomial (Fin N × Fin N) ℂ) := by
        rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdg), C_1]
      simp only [smul_eq_C_mul, C_mul]
      linear_combination (C (detPow ℂ N g lam.detShift) * detPoly N ^ c *
        rowAct ℂ (n := N) (g : Matrix (Fin N) (Fin N) ℂ)ᵀ f) * key
  obtain ⟨f0, hf0mem, hf0eq⟩ := hsplit (F w0) (hFmem' w0)
  have hf0U : f0 ∈ U := Submodule.mem_inf.mpr ⟨hf0mem, Submodule.mem_comap.mpr
    (LinearMap.mem_range.mpr ⟨w0, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf0eq⟩)⟩
  have hf0ne : f0 ≠ 0 := by
    intro h; apply hF0; rw [hf0eq, h, mul_zero]
  have hUeq : U = nablaSq ℂ N lam := by
    rcases (hH N lam).2.1 U inf_le_left hUst with h | h
    · exfalso; rw [h, Submodule.mem_bot] at hf0U; exact hf0ne hf0U
    · exact h
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ H := (LinearMap.ker F).map S.subtype
    have hS'le : S' ≤ S := by
      rintro _ ⟨y, _, rfl⟩; exact y.2
    have hS'st : IsKStableOn (allPos N) σ S' := by
      rintro g hg _ ⟨y, hy, rfl⟩
      have hd : g.det ^ K ≠ 0 := pow_ne_zero _ (det_ne_zero_of_mem_K hg)
      refine ⟨(g.det ^ K)⁻¹ • P g y, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker] at hy ⊢
        rw [map_smul, hFint, hy, map_zero, smul_zero]
      · simp only [Submodule.subtype_apply, Submodule.coe_smul, hPσ g hg y, smul_smul,
          inv_mul_cancel₀ hd, one_smul]
    rcases hirr S' hS'le hS'st with h | h
    · rw [eq_bot_iff]
      intro y hy
      have hyS : (y : H) ∈ S' := ⟨y, hy, rfl⟩
      rw [h, Submodule.mem_bot] at hyS
      rw [Submodule.mem_bot]
      exact Subtype.ext hyS
    · exfalso
      have hv : v0 ∈ S' := by rw [h]; exact hv0S
      obtain ⟨y, hy, hyv⟩ := hv
      have hyw : y = w0 := Subtype.ext hyv
      rw [hyw] at hy
      exact hF0 hy
  let φ : U →ₗ[ℂ] LinearMap.range F :=
    LinearMap.codRestrict (LinearMap.range F) (mulD ∘ₗ U.subtype)
      (fun u => Submodule.mem_comap.mp (Submodule.mem_inf.mp u.2).2)
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v huv
      have := congrArg Subtype.val huv
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
      exact Subtype.ext (hmulD_inj this)
    · rintro ⟨z, x, rfl⟩
      obtain ⟨f', hf'mem, hf'eq⟩ := hsplit (F x) (hFmem' x)
      refine ⟨⟨f', Submodule.mem_inf.mpr ⟨hf'mem, Submodule.mem_comap.mpr
        (LinearMap.mem_range.mpr ⟨x, by simp only [mulD, LinearMap.mulLeft_apply]; exact hf'eq⟩)⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, mulD,
        LinearMap.mulLeft_apply]
      exact hf'eq.symm
  calc Module.finrank ℂ S = Module.finrank ℂ (LinearMap.range F) :=
        (LinearMap.finrank_range_of_inj hFinj).symm
    _ = Module.finrank ℂ U := (LinearEquiv.ofBijective φ hφ).finrank_eq.symm
    _ = Module.finrank ℂ (nablaSq ℂ N lam) := (LinearEquiv.ofEq _ _ hUeq).finrank_eq

end PI.WMI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
section
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem detSplit_fullMinor {N : ℕ} (s : ℕ) (I : Fin s → Fin N) (hs : s ≤ N) (hN : s = N) :
    ∃ e : ℂ, initMinor ℂ (n := N) I hs = C e * detPoly N := by
  subst hN
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := (Fintype.bijective_iff_injective_and_card I).2 ⟨hI, rfl⟩
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective I hb) : ℤ) : ℂ), ?_⟩
    have h := Matrix.det_permute (Equiv.ofBijective I hb)
      (Matrix.of fun i j : Fin s => (X (i, j) : MvPolynomial (Fin s × Fin s) ℂ))
    have hM : initMinor ℂ (n := s) I hs =
        ((Matrix.of fun i j : Fin s => (X (i, j) : MvPolynomial (Fin s × Fin s) ℂ)).submatrix
          (Equiv.ofBijective I hb) id).det := by
      unfold initMinor
      congr 1
    rw [hM, h, detPoly, map_intCast]
  · refine ⟨0, ?_⟩
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨i, j, hij, hne⟩ := hI
    rw [map_zero, zero_mul]
    unfold initMinor
    exact Matrix.det_zero_of_row_eq hne (funext fun q => by simp [hij])

theorem detSplit_prodMem {N K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N)
    (s : Finset (Fin K)) :
    ∏ k ∈ s, initMinor ℂ (I k) (hsz k) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t => (s.filter fun k => t.val < sz k).card) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h := (Formalism.GradedWeylDivisibility.dualWeylMul ℂ N N 0 0 1 1).2
    convert h using 2
    · funext t; simp
    · simp
  · intro a s ha ih
    have h1 : initMinor ℂ (I a) (hsz a) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (shapeDeg (fun _ : Fin 1 => sz a)) := by
      have := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => sz a) (fun _ => hsz a) (fun _ => I a)
      simpa only [bideterminant, Fin.prod_univ_one] using this
    have h2 := (Formalism.GradedWeylDivisibility.dualWeylMul ℂ N N _ _ _ _).1 h1 ih
    rw [Finset.prod_insert ha]
    convert h2 using 2
    funext t
    by_cases ht : t.val < sz a
    · simp [shapeDeg, ht, ha, Finset.filter_insert, add_comm]
    · simp [shapeDeg, ht, Finset.filter_insert]

theorem determinant_splitting_formula : DetSplit := by
  intro N ν c hν f hf
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨f, ?_, ?_⟩
    · have : (fun a : Fin 0 => ν a + c) = ν := funext fun a => a.elim0
      rwa [this] at hf
    · simp [detPoly]
  · classical
    have h0 := hν hN
    let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
      (Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν).map (LinearMap.mulLeft ℂ (detPoly N ^ c))
    suffices hT : f ∈ T by
      obtain ⟨f', hf', hff⟩ := hT
      exact ⟨f', hf', hff.symm⟩
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N] at hf
    refine (Submodule.span_le.2 ?_) hf
    rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
    let A : Finset (Fin K) := Finset.univ.filter fun k => sz k = N
    have hcard : ∀ t : Fin N, (Finset.univ.filter fun k => t.val < sz k).card =
        (Aᶜ.filter fun k => t.val < sz k).card + A.card := by
      intro t
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_sum_compl A, add_comm,
        Finset.card_eq_sum_ones A]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have : sz k = N := by simpa [A] using hk
      simp [this, t.isLt]
    have hA : A.card = c := by
      have h1 := congrFun hshape ⟨N - 1, by omega⟩
      have h2 := hcard ⟨N - 1, by omega⟩
      have h3 : (Aᶜ.filter fun k => N - 1 < sz k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk hlt
        have hkA : ¬ sz k = N := by simpa [A] using hk
        have := hsz k
        omega
      simp only [shapeDeg] at h1
      rw [h0] at h1
      rw [h3] at h2
      simp at h2
      omega
    have hrest : (fun t : Fin N => (Aᶜ.filter fun k => t.val < sz k).card) = ν := by
      funext t
      have h1 := congrFun hshape t
      simp only [shapeDeg] at h1
      have := hcard t
      omega
    have hmem := detSplit_prodMem sz hsz I Aᶜ
    rw [hrest] at hmem
    have hfac : ∀ k : Fin K, ∃ e : ℂ, k ∈ A → initMinor ℂ (I k) (hsz k) = C e * detPoly N := by
      intro k
      by_cases hk : k ∈ A
      · obtain ⟨e, he⟩ := detSplit_fullMinor (sz k) (I k) (hsz k) (by simpa [A] using hk)
        exact ⟨e, fun _ => he⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose e he using hfac
    refine ⟨C (∏ k ∈ A, e k) * ∏ k ∈ Aᶜ, initMinor ℂ (I k) (hsz k), ?_, ?_⟩
    · rw [C_mul']
      exact Submodule.smul_mem _ _ hmem
    · simp only [LinearMap.mulLeft_apply]
      unfold bideterminant
      rw [← Finset.prod_mul_prod_compl A, Finset.prod_congr rfl fun k hk => he k hk,
        Finset.prod_mul_distrib, Finset.prod_const, hA, map_prod]
      ring

end PI.WMI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExtLem
section
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

lemma pe_evM_detPoly {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) : evM g (detPoly N) = g.det := by
  unfold evM detPoly
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

lemma pe_one_mem (N : ℕ) : (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) := by
  refine ⟨one_mem _, by simp⟩

lemma pe_mul_mem {N : ℕ} {g h : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) (hh : h ∈ Kset (allPos N)) :
    g * h ∈ Kset (allPos N) := by
  refine ⟨mul_mem hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

lemma pe_unitary_mem {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : uᴴ * u = 1) : u ∈ Kset (allPos N) := by
  have hJ : Jm (allPos N) = 1 := by
    unfold Jm allPos
    simp
  refine ⟨?_, by rw [hJ]; simp⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact hu

lemma pe_right {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ g, evM g Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, X (pq.1, r) * C (h r pq.2)) Q, fun g => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add (f := _), evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

lemma pe_left {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ h, evM h Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, C (g pq.1 r) * X (r, pq.2)) Q, fun h => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add (f := _), evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

end PI.WMI
end
end

