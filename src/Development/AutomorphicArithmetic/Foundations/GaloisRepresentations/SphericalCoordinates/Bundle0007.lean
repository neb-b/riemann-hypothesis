module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEvIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem evI_mulVec {L : Type} [AddCommGroup L] {g : ℕ} (P : L →+ (Fin g → ℂ)) (f : L →ₗ[ℤ] L)
    (H : Matrix (Fin g) (Fin g) ℂ) (h : ∀ x, P (f x) = H *ᵥ P x) (q : ℤ[X]) (x : L) :
    P (aeval f q x) = aeval H q *ᵥ P x := by
  induction q using Polynomial.induction_on generalizing x with
  | C a =>
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    ext j
    simp
  | add p r hp hr => simp only [map_add (f := _), LinearMap.add_apply, hp, hr, Matrix.add_mulVec]
  | monomial n a ih =>
    rw [pow_succ, ← _root_.mul_assoc, map_mul (aeval f) (C a * X ^ n) X, map_mul (aeval H) (C a * X ^ n) X,
      aeval_X, aeval_X, Module.End.mul_apply, ih, h, Matrix.mulVec_mulVec]

private theorem evI_diag {g : ℕ} (H Sb : Matrix (Fin g) (Fin g) ℂ) (ev : Fin g → ℂ)
    (h : H * Sb = Sb * Matrix.diagonal ev) (q : ℤ[X]) :
    aeval H q * Sb = Sb * Matrix.diagonal fun i => aeval (ev i) q := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C]
    simp only [Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
    rw [Matrix.diagonal_intCast, Int.cast_comm]
  | add p r hp hr => simp only [map_add (f := _), add_mul, hp, hr, ← Matrix.diagonal_add, mul_add, Pi.add_def]
  | monomial n a ih =>
    rw [pow_succ, ← _root_.mul_assoc, map_mul (aeval H) (C a * X ^ n) X, aeval_X, _root_.mul_assoc, h,
      ← _root_.mul_assoc, ih, _root_.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    rw [map_mul (aeval (ev i)) (C a * X ^ n) X, aeval_X]

theorem UpperTheory.Gal.W2.evIntegral_of :
    UpperTheory.Gal.W2.EvIntegral := by
  intro F _ _ O _ bar g ρ a D P₀ hP ga H hH Sb ty ev hD i x
  haveI := D.fin
  haveI := D.free
  let f : D.La →ₗ[ℤ] D.La := ga.toAddMonoidHom.toIntLinearMap
  have hf : ∀ y, P₀ (f y) = H *ᵥ P₀ y := hH
  have hv : ∀ y, aeval H f.charpoly *ᵥ P₀ y = 0 := fun y => by
    rw [← evI_mulVec P₀ f H hf f.charpoly y, LinearMap.aeval_self_charpoly]
    simp
  have hall : ∀ v, aeval H f.charpoly *ᵥ v = 0 := by
    intro v
    have hv' : v ∈ Submodule.span ℝ (Set.range P₀) := by
      rw [hP.2.2.2.1]
      trivial
    induction hv' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact hv y
    | zero => simp
    | add u w _ _ hu hw => rw [Matrix.mulVec_add, hu, hw, add_zero]
    | smul r u _ hu => rw [Matrix.mulVec_smul, hu, smul_zero]
  have hq0 : aeval H f.charpoly = 0 := by
    ext j k
    have hjk := congrFun (hall (Pi.single k 1)) j
    simpa [Matrix.mulVec_single] using hjk
  have hdiag := evI_diag H Sb ev hD.2.2 f.charpoly
  rw [hq0, zero_mul] at hdiag
  have hinv : IsUnit Sb := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hD.1)
  have hd : Matrix.diagonal (fun j => aeval (ev j) f.charpoly) = 0 :=
    hinv.mul_left_cancel (by rw [← hdiag, mul_zero])
  have hev0 : aeval (ev i) f.charpoly = 0 := by
    have hii := congrFun (congrFun hd i) i
    simpa using hii
  have hint_ev : IsIntegral ℤ (ev i) := ⟨f.charpoly, LinearMap.charpoly_monic f, by rw [← aeval_def]; exact hev0⟩
  have hint_t : IsIntegral ℤ (ty i (x : F)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (ty i).toIntAlgHom
  intro hzero
  have h2 : ty i ((2 * x : 𝓞 F) : F) = 2 * ty i (x : F) := by
    push_cast
    simp [map_mul, map_ofNat]
  rw [h2] at hzero
  have hprod : algebraMap ℚ ℂ (1 / 2) = ty i (x : F) * ev i := by
    simp only [map_div₀, map_one, map_ofNat]
    linear_combination (1 / 2 : ℂ) * hzero
  have hhalf : IsIntegral ℤ (algebraMap ℚ ℂ (1 / 2)) := by
    rw [hprod]
    exact hint_t.mul hint_ev
  rw [isIntegral_algebraMap_iff ] at hhalf
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hhalf
  have h2n : ((2 * n : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]
    norm_num
  have h2n' : 2 * n = 1 := by exact_mod_cast h2n
  omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFibDet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.fibDet_of :
    UpperTheory.Gal.W2.FibDet := by
  classical
  intro F _ _ O _ bar g ρ a H Sb ty ev hD k α y
  obtain ⟨hdet, hρ, hH⟩ := hD
  letI : Invertible Sb := Matrix.invertibleOfIsUnitDet Sb (isUnit_iff_ne_zero.2 hdet)
  let cb : Module.Basis (Fin g) ℂ (Fin g → ℂ) :=
    (Pi.basisFun ℂ (Fin g)).map (Matrix.toLinearEquiv' Sb this)
  have hcb : ∀ i, cb i = Sb *ᵥ Pi.single i 1 := by
    intro i
    simp only [cb, Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hdiag : ∀ (f : Fin g → ℂ) i, Sb *ᵥ (Matrix.diagonal f *ᵥ Pi.single i 1) = f i • cb i := by
    intro f i
    rw [hcb, ← Matrix.mulVec_smul]
    congr 1
    ext l
    by_cases h : l = i
    · subst h; simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, h]
  have hρv : ∀ (c : 𝓞 F) i, ρ (a c) *ᵥ cb i = ty i c • cb i := by
    intro c i
    rw [← hdiag (fun i => ty i c) i, hcb, Matrix.mulVec_mulVec, hρ c, Matrix.mulVec_mulVec]
  have hHv : ∀ i, H *ᵥ cb i = ev i • cb i := by
    intro i
    rw [← hdiag ev i, hcb, Matrix.mulVec_mulVec, hH, Matrix.mulVec_mulVec]
  let bb : Module.Basis ((_ : Fin k) × Fin g) ℂ (Fin k → Fin g → ℂ) := Pi.basis fun _ => cb
  let d : ((_ : Fin k) × Fin g) → ℂ := fun x => 1 - ty x.2 (α x.1) * (y * ev x.2)
  have hf : ∀ x, (1 - y • fibMap H (diagAct a ρ α)) (bb x) = d x • bb x := by
    intro x
    have hbb : bb x = Pi.single x.1 (cb x.2) := Pi.basis_apply _ x
    rw [hbb]
    funext l
    by_cases hl : l = x.1
    · subst hl
      have e1 := hρv (α x.1) x.2
      have e2 := hHv x.2
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, fibMap, diagAct,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj,
        Function.eval, Matrix.toLin'_apply, Pi.single_eq_same, Pi.sub_apply, Pi.smul_apply]
      rw [e1, Matrix.mulVec_smul, e2]
      simp only [d]
      module
    · simp [fibMap, diagAct, Matrix.toLin'_apply, Pi.single_eq_of_ne hl]
  rw [← LinearMap.det_toMatrix bb]
  have hmat : LinearMap.toMatrix bb bb (1 - y • fibMap H (diagAct a ρ α)) = Matrix.diagonal d := by
    ext x z
    rw [LinearMap.toMatrix_apply, hf, map_smul, bb.repr_self]
    by_cases h : x = z
    · subst h; simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, h, Ne.symm h]
  rw [hmat, Matrix.det_diagonal, Fintype.prod_sigma]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKillsMat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.killsMat_of :
    UpperTheory.Gal.W2.KillsMat := by
  intro F _ _ O _ bar g ρ a D P₀ hP ga H hH q
  have hpow : ∀ (i : ℕ) (x : D.La), P₀ ((ga ^ i) x) = (H ^ i) *ᵥ P₀ x := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, hH, Matrix.mulVec_mulVec, pow_succ]
  have hsum : ∀ x, P₀ (q.sum fun i b => a b • (ga ^ i) x) =
      (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ P₀ x := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.sum_def, map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP.1, hpow, Matrix.mulVec_mulVec]
  constructor
  · intro hk
    have hz : ∀ x, (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ P₀ x = 0 := fun x => by
      rw [← hsum, hk x, map_zero]
    have hlin : (Matrix.mulVecLin (q.sum fun i b => ρ (a b) * H ^ i)).restrictScalars ℝ = 0 :=
      GlobalTheory.PerCoordU.ext_per hP fun x => by simpa using hz x
    have hv : ∀ v, (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ v = 0 := fun v => by
      simpa using LinearMap.congr_fun hlin v
    exact Matrix.mulVec_injective (funext fun v => by rw [hv v, Matrix.zero_mulVec])
  · intro h x
    apply hP.2.1
    rw [hsum, h, map_zero, Matrix.zero_mulVec]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMarkDiag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem mulVec_mulVec_of_mul_eq_mul_diagonal {g : ℕ} (Sb A : Matrix (Fin g) (Fin g) ℂ) (d : Fin g → ℂ)
    (h : A * Sb = Sb * Matrix.diagonal d) (w : Fin g → ℂ) :
    A *ᵥ (Sb *ᵥ w) = Sb *ᵥ (fun j => d j * w j) := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  simp [Matrix.mulVec_diagonal]

theorem UpperTheory.Gal.W2.markDiag_of :
    UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.MarkDiag := by
  intro hTC F _ _ O _ bar g ρ a n t₀ ε hsig H Sb ty ev hD mu
  classical
  obtain ⟨hdet, hρ, hH⟩ := hD
  have hcard := (hTC F O bar g ρ a n t₀ ε hsig H Sb ty ev ⟨hdet, hρ, hH⟩ t₀).1
  rw [show typeMult n t₀ ε t₀ = 1 by simp [typeMult]] at hcard
  unfold evAt at hcard ⊢
  rw [Multiset.card_map, Finset.card_val, Finset.card_eq_one] at hcard
  obtain ⟨i₀, hi₀⟩ := hcard
  rw [hi₀, Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_inj]
  have hmemS : ∀ j, ty j = t₀ ↔ j = i₀ := by
    intro j
    have := congrArg (j ∈ ·) hi₀
    simpa using this
  have hcol := mulVec_mulVec_of_mul_eq_mul_diagonal Sb
  have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet
  constructor
  · rintro ⟨v, hv0, hvρ, hvH⟩
    have hunit : IsUnit Sb.det := isUnit_iff_ne_zero.2 hdet
    obtain ⟨w, hvw⟩ : ∃ w, v = Sb *ᵥ w :=
      ⟨Sb⁻¹ *ᵥ v, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]⟩
    subst hvw
    have hsupp : ∀ j, w j ≠ 0 → j = i₀ := by
      intro j hj
      rw [← hmemS]
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
      ext c
      have h1 := hvρ c
      rw [hcol _ _ (hρ c), ← Matrix.mulVec_smul] at h1
      have h2 := congr_fun (hinj h1) j
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      simp only [RingHom.comp_apply]
      exact mul_right_cancel₀ hj h2
    have hw0 : w ≠ 0 := by
      intro h; apply hv0; rw [h, Matrix.mulVec_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
    rw [hsupp j hj] at hj
    have h1 := hvH
    rw [hcol _ _ hH, ← Matrix.mulVec_smul] at h1
    have h2 := congr_fun (hinj h1) i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact mul_right_cancel₀ hj h2
  · intro h
    refine ⟨Sb *ᵥ Pi.single i₀ 1, ?_, fun c => ?_, ?_⟩
    · intro h0
      have : Pi.single i₀ (1 : ℂ) = 0 := hinj (by rw [h0, Matrix.mulVec_zero])
      simpa using congr_fun this i₀
    · rw [hcol _ _ (hρ c), ← Matrix.mulVec_smul]
      congr 1
      funext j
      by_cases hj : j = i₀
      · subst hj
        simp [(hmemS _).2 rfl]
      · simp [Pi.single_apply, hj]
    · rw [hcol _ _ hH, ← Matrix.mulVec_smul]
      congr 1
      funext j
      by_cases hj : j = i₀
      · subst hj
        simp [h]
      · simp [Pi.single_apply, hj]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PNewtonPoly
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma exists_fin_map (n : ℕ) (s : Multiset ℂ) (h : Multiset.card s = n) :
    ∃ r : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map r = s := by
  induction n generalizing s with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at h
    simp [h]
  | succ n ih =>
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    obtain ⟨r, hr⟩ := ih t (by simpa using h)
    refine ⟨Fin.cons a r, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ, ← Multiset.cons_coe]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Fin.univ_val_map, hr]

private lemma newton_step (n k : ℕ) (r : Fin n → ℂ) :
    (k : ℂ) * ((Finset.univ : Finset (Fin n)).val.map r).esymm k =
      (-1) ^ (k + 1) * ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * ((Finset.univ : Finset (Fin n)).val.map r).esymm a.1 *
          (((Finset.univ : Finset (Fin n)).val.map r).map fun x => x ^ a.2).sum := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) r) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, Multiset.map_map,
    Function.comp_def]
  rfl

private lemma esymm_descends (F : Type) [Field F] [NumberField F] (n : ℕ)
    (m : (F →+* ℂ) → Multiset ℂ) (hc : ∀ τ, Multiset.card (m τ) = n)
    (hpow : ∀ j : ℕ, ∃ b : F, ∀ τ, ((m τ).map fun r => r ^ j).sum = τ b) (k : ℕ) :
    ∃ b : F, ∀ τ, (m τ).esymm k = τ b := by
  choose p hp using hpow
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, fun τ => by simp [Multiset.esymm]⟩
    choose! e he using ih
    refine ⟨(k : F)⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * e a.1 * p a.2), fun τ => ?_⟩
    obtain ⟨r, hr⟩ := exists_fin_map n (m τ) (hc τ)
    have hs := newton_step n k r
    rw [hr] at hs
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_inv₀, map_natCast, map_pow, map_neg, map_one, map_sum]
    rw [eq_inv_mul_iff_mul_eq₀ hk', hs]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [he a.1 (Finset.mem_filter.1 ha).2 τ, hp]

theorem UpperTheory.Gal.W2.newtonPoly_of :
    UpperTheory.Gal.W2.NewtonPoly := by
  intro F _ _ n m hc hpow
  choose b hb using esymm_descends F n m hc hpow
  refine ⟨∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j)), ?_⟩
  have hmap : ∀ τ : F →+* ℂ, Polynomial.map τ
      (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j))) =
      ((m τ).map fun r => X - C r).prod := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc τ, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hb j τ]
  obtain ⟨τ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hmon : ((m τ).map fun r => X - C r).prod.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C r
  refine ⟨?_, ?_, hmap⟩
  · have h1 := Polynomial.leadingCoeff_map_of_injective τ.injective
      (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j)))
    rw [hmap τ, hmon.leadingCoeff] at h1
    exact τ.injective (by rw [← h1, map_one])
  · rw [← Polynomial.natDegree_map_eq_of_injective τ.injective, hmap τ,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hc τ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowSumRat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma trace_of_diag {g : ℕ} (M Sb : Matrix (Fin g) (Fin g) ℂ) (d : Fin g → ℂ) (hS : Sb.det ≠ 0)
    (h : M * Sb = Sb * Matrix.diagonal d) : M.trace = ∑ i, d i := by
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hS
  have hinv : Sb * Sb⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hM : M = Sb * Matrix.diagonal d * Sb⁻¹ := by
    rw [← h, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.trace_diagonal]

private lemma pow_mul_diag {g : ℕ} (H Sb : Matrix (Fin g) (Fin g) ℂ) (e : Fin g → ℂ)
    (h : H * Sb = Sb * Matrix.diagonal e) (j : ℕ) :
    H ^ j * Sb = Sb * Matrix.diagonal (fun i => e i ^ j) := by
  induction j with
  | zero =>
    have : (fun i => e i ^ 0) = fun _ => (1 : ℂ) := by funext i; simp
    rw [this]
    simp [Matrix.diagonal_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 2

private lemma per_pow {L : Type} {O : Type} [Ring O] [AddCommGroup L] [Module O L] {g : ℕ}
    (P : L →+ (Fin g → ℂ)) (ga : L →ₗ[O] L) (H : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x, P (ga x) = H *ᵥ P x) (j : ℕ) (x : L) : P ((ga ^ j) x) = (H ^ j) *ᵥ P x := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, h, ih, Matrix.mulVec_mulVec]

open scoped Classical in
private lemma sum_evAt {F : Type} [Field F] {g : ℕ} (ty : Fin g → (F →+* ℂ)) (e : Fin g → ℂ)
    (τ : F →+* ℂ) (u : ℂ → ℂ) :
    ((evAt ty e τ).map u).sum = ∑ i, if ty i = τ then u (e i) else 0 := by
  unfold evAt
  rw [Multiset.map_map, ← Finset.sum_filter]
  rfl

open scoped Classical in
private lemma sum_evFull {F : Type} [Field F] [NumberField F] {g : ℕ} (ty : Fin g → (F →+* ℂ))
    (e : Fin g → ℂ) (j : ℕ) (x : F) :
    ∑ τ : F →+* ℂ, τ x * ((evFull ty e τ).map fun r => r ^ j).sum =
      (∑ i, ty i x * e i ^ j) + (starRingEnd ℂ) (∑ i, ty i x * e i ^ j) := by
  have cc : ∀ φ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => RingHom.ext fun y => by simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ∑ τ : F →+* ℂ, τ x * ((evAt ty e τ).map fun r => r ^ j).sum = ∑ i, ty i x * e i ^ j := by
    simp_rw [sum_evAt, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∑ τ : F →+* ℂ, τ x *
      (((evAt ty e (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ)).map fun r => r ^ j).sum =
      (starRingEnd ℂ) (∑ i, ty i x * e i ^ j) := by
    simp_rw [Multiset.map_map, sum_evAt, Finset.mul_sum, mul_ite, mul_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (ComplexEmbedding.conjugate (ty i))]
    · rw [if_pos (cc _).symm, ComplexEmbedding.conjugate_coe_eq]
      simp
    · intro τ _ hτ
      rw [if_neg]
      intro hc
      apply hτ
      rw [hc, cc]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  simp_rw [evFull, Multiset.map_add (f := _), Multiset.sum_add, mul_add]
  rw [Finset.sum_add_distrib, h1, h2]

theorem UpperTheory.Gal.W2.powSumRat_of :
    UpperTheory.Gal.W2.TraceLat → UpperTheory.Gal.W2.TraceDual → UpperTheory.Gal.W2.PowSumRat := by
  intro hL hD F _ _ O _ bar g ρ a D P₀ hP ga H hga Sb ty ev hd j
  obtain ⟨hS, hρ, hH⟩ := hd
  refine hD F (fun τ => ((evFull ty ev τ).map fun r => r ^ j).sum) ?_
  intro c
  let f : D.La →ₗ[ℤ] D.La :=
    (AddMonoidHom.mk' (fun x => a c • (ga ^ j) x) (by intro x y; simp [smul_add])).toIntLinearMap
  have hf : ∀ x, P₀ (f x) = (ρ (a c) * H ^ j) *ᵥ P₀ x := by
    intro x
    show P₀ (a c • (ga ^ j) x) = _
    rw [hP.1, per_pow P₀ ga H hga, Matrix.mulVec_mulVec]
  refine ⟨LinearMap.trace ℤ D.La f, ?_⟩
  rw [hL D.La g P₀ hP.2.1 hP.2.2.1 hP.2.2.2.1 f _ hf]
  have htr : (ρ (a c) * H ^ j).trace = ∑ i, ty i (c : F) * ev i ^ j := by
    refine trace_of_diag _ Sb (fun i => ty i (c : F) * ev i ^ j) hS ?_
    rw [Matrix.mul_assoc, pow_mul_diag H Sb ev hH j, ← Matrix.mul_assoc, hρ c, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
  rw [htr]
  exact sum_evFull ty ev j (c : F)
end

