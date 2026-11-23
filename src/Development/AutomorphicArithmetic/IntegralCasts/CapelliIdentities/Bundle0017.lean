module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCharNeOne
section
open MeasureTheory WeakDual

namespace UpperTheory.Reformulated.B.CharactersSeparatePoints

private theorem comm_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CommCStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A) (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have h1 : gelfandTransform ℂ A (U g * T) ≠ gelfandTransform ℂ A T :=
    fun h => hg ((gelfandTransform_isometry A).injective h)
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.1 h1
  change φ (U g * T) ≠ φ T at hφ
  have hT0 : φ T ≠ 0 := by
    intro h0
    apply hφ
    rw [map_mul, h0, mul_zero]
  have hn : ∀ h, ‖φ (U h)‖ = 1 := by
    intro h
    have : star (φ (U h)) * φ (U h) = 1 := by
      rw [← map_star, ← map_mul, hU, ← map_mul, inv_mul_cancel, map_one, map_one]
    have h2 := congrArg norm this
    rw [norm_mul, norm_star, norm_one] at h2
    nlinarith [norm_nonneg (φ (U h))]
  have hc : Continuous fun h => φ (U h) := by
    have : (fun h => φ (U h)) = fun h => φ (U h * T) / φ T := by
      funext h
      rw [map_mul, mul_div_cancel_right₀ _ hT0]
    rw [this]
    exact ((map_continuous φ).comp hT).div_const _
  refine ⟨{ toFun := fun h => ⟨φ (U h), mem_sphere_zero_iff_norm.2 (hn h)⟩
            map_one' := Circle.ext (by simp)
            map_mul' := fun a b => Circle.ext (by
              change φ (U (a * b)) = φ (U a) * φ (U b)
              rw [map_mul, map_mul])
            continuous_toFun := hc.subtype_mk _ }, ?_⟩
  intro h
  apply hφ
  have : φ (U g) = 1 := congrArg (fun z : Circle => (z : ℂ)) h
  rw [map_mul, this, one_mul]

private theorem alg_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A)
    (hB : ∀ B : A, (∀ h, U h * B = B * U h) → B * T = T * B)
    (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  let S' : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (Set.range U)
  have mem' : ∀ B, B ∈ S' ↔ ∀ h, U h * B = B * U h := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H h
      exact (H _ ⟨h, rfl⟩).1
    · rintro H _ ⟨h, rfl⟩
      exact ⟨H h, by rw [hU]; exact H _⟩
  let S : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (S' : Set A)
  have mem : ∀ B, B ∈ S ↔ ∀ D ∈ S', D * B = B * D := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H D hD
      exact (H _ hD).1
    · intro H D hD
      exact ⟨H D hD, H _ (star_mem hD)⟩
  have hUS' : ∀ h, U h ∈ S' := fun h => (mem' _).2 fun k => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hUS : ∀ h, U h ∈ S := fun h => (mem _).2 fun D hD => ((mem' D).1 hD h).symm
  have hTS : T ∈ S := (mem _).2 fun D hD => hB D ((mem' D).1 hD)
  have hSS : ∀ B ∈ S, B ∈ S' := fun B hB => (mem' _).2 fun h => (mem _).1 hB _ (hUS' h)
  have hcl : IsClosed (S : Set A) := by
    have : (S : Set A) = ⋂ D ∈ S', {B | D * B = B * D} := by
      ext B
      simp only [SetLike.mem_coe, mem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun D _ => isClosed_eq (by fun_prop) (by fun_prop)
  let _ : CommCStarAlgebra S :=
    { (inferInstance : CStarAlgebra S) with
      mul_comm := fun a b => Subtype.ext ((mem _).1 b.2 _ (hSS _ a.2)) }
  refine comm_case (A := S) (U.codRestrict S hUS) (fun h => Subtype.ext (hU h)) ⟨T, hTS⟩
    (hT.subtype_mk _) (fun h => hg (congrArg Subtype.val h))

private theorem hilbert_case {C H : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
    (μ : Measure C) [μ.IsHaarMeasure]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : C →* (H →L[ℂ] H)) (hn : ∀ h v, ‖U h v‖ = ‖v‖) (hc : ∀ v, Continuous fun h => U h v)
    {g : C} {v : H} (hg : U g v ≠ v) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have happ : ∀ a b x, U a (U b x) = U (a * b) x := by
    intro a b x
    rw [map_mul]
    rfl
  have hstar : ∀ h, star (U h) = U h⁻¹ := by
    intro h
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have := (LinearIsometry.mk (U h).toLinearMap (hn h)).inner_map_map (U h⁻¹ x) y
    rw [← this]
    change inner ℂ (U h (U h⁻¹ x)) (U h y) = _
    rw [happ, mul_inv_cancel, map_one]
    rfl
  have hint : ∀ (f : C(C, ℂ)) (x : H), Integrable (fun h => f h • U h x) μ := fun f x =>
    (f.continuous.smul (hc x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T₀ : C(C, ℂ) →ₗ[ℂ] H →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun f x => ∫ h, f h • U h x ∂μ)
    (fun f f' x => by
      rw [← integral_add (hint f x) (hint f' x)]
      simp [add_smul])
    (fun c f x => by
      rw [← integral_smul]
      simp [mul_smul])
    (fun f x y => by
      rw [← integral_add (hint f x) (hint f y)]
      simp)
    (fun c f x => by
      rw [← integral_smul]
      simp [smul_comm c])
  let T : C(C, ℂ) →L[ℂ] H →L[ℂ] H := T₀.mkContinuous₂ (μ.real Set.univ) (fun f x => by
    have : ‖∫ h, f h • U h x ∂μ‖ ≤ (‖f‖ * ‖x‖) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun h => by
        rw [norm_smul, hn]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm h) (norm_nonneg _))
    calc ‖T₀ f x‖ ≤ _ := this
      _ = _ := by ring)
  have hT : ∀ f x, T f x = ∫ h, f h • U h x ∂μ := fun _ _ => rfl
  have hB : ∀ f, ∀ B : H →L[ℂ] H, (∀ h, U h * B = B * U h) → B * T f = T f * B := by
    intro f B hB
    ext x
    change B (T f x) = T f (B x)
    rw [hT, hT, ← B.integral_comp_comm (hint f x)]
    congr 1
    funext h
    rw [map_smul]
    congr 1
    exact (congrArg (fun L : H →L[ℂ] H => L x) (hB h)).symm
  let w : H := U g v - v
  have hw : w ≠ 0 := sub_ne_zero.2 hg
  let f : C(C, ℂ) := ⟨fun h => inner ℂ (U h w) w, (hc w).inner continuous_const⟩
  let F : C(C, C(C, ℂ)) :=
    (f.comp ⟨fun p : C × C => p.1⁻¹ * p.2, by fun_prop⟩).curry
  have hF : ∀ k, U k * T f = T (F k) := by
    intro k
    ext x
    change U k (T f x) = T (F k) x
    rw [hT, hT, ← (U k).integral_comp_comm (hint f x),
      ← integral_mul_left_eq_self (fun h => F k h • U h x) k]
    congr 1
    funext h
    rw [map_smul, happ]
    congr 1
    change f h = f (k⁻¹ * (k * h))
    rw [inv_mul_cancel_left]
  refine alg_case U hstar (T f) (hB f) ?_ ?_
  · simp_rw [hF]
    exact T.continuous.comp F.continuous
  · intro h0
    have h1 : T f w = 0 := by
      have h2 := hB f (U g) (fun h => by rw [← map_mul, ← map_mul, mul_comm])
      rw [h0] at h2
      have h3 : T f v = T f (U g v) := congrArg (fun L : H →L[ℂ] H => L v) h2
      rw [map_sub, ← h3, sub_self]
    have h2 : ∫ h, ((‖f h‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      have := integral_inner (𝕜 := ℂ) (hint f w) w
      rw [← hT, h1, inner_zero_right] at this
      rw [← this]
      congr 1
      funext h
      rw [inner_smul_right, ← inner_conj_symm w (U h w)]
      change _ = f h * (starRingEnd ℂ) (f h)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := 1)
      (f := fun h => ‖f h‖ ^ 2) (by fun_prop) (HasCompactSupport.of_compactSpace _)
      (fun h => by positivity) ?_).ne' h2
    have : f 1 = inner ℂ w w := by
      change inner ℂ (U 1 w) w = _
      rw [map_one]
      rfl
    simp only [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))

end UpperTheory.Reformulated.B.CharactersSeparatePoints

theorem UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one.{u_1} :
    ∀ {C : Type u_1} [inst : CommGroup C] [inst_1 : TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
      {g : C}, g ≠ (1 : C) → ∃ (χ : C →ₜ* Circle), (χ : C → Circle) g ≠ (1 : Circle) := by
  intro C _ _ _ _ _ g hg
  borelize C
  let μ : Measure C := Measure.haar
  let m : C(C, C(C, C)) := ContinuousMap.curry ⟨fun p : C × C => p.1 * p.2, by fun_prop⟩
  have hm : ∀ h, MeasurePreserving (m h) μ μ := fun h => measurePreserving_mul_left μ h
  let V : C → (Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ) := fun h => Lp.compMeasurePreservingₗᵢ ℂ (m h) (hm h)
  have hV : ∀ h x, V h x = Lp.compMeasurePreserving (m h) (hm h) x := fun _ _ => rfl
  let U : C →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := fun h => (V h).toContinuousLinearMap
      map_one' := by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m 1) (hm 1) x = x
        convert Lp.compMeasurePreserving_id_apply x
        funext a
        exact one_mul a
      map_mul' := fun a b => by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m (a * b)) (hm _) x =
          Lp.compMeasurePreserving (m a) (hm a) (Lp.compMeasurePreserving (m b) (hm b) x)
        rw [← Lp.compMeasurePreserving_comp_apply]
        congr 2
        funext c
        exact (mul_left_comm b a c).trans (mul_assoc a b c).symm |>.symm }
  obtain ⟨F, hF0, hF1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := g)) (isClosed_singleton (x := (1 : C)))
    (Set.disjoint_singleton.2 hg)
  let G : C(C, ℂ) := ⟨fun a => (F a : ℂ), by fun_prop⟩
  refine hilbert_case μ U (fun h x => (V h).norm_map x)
    (fun x => continuous_const.compMeasurePreservingLp m.continuous hm (by simp))
    (v := ContinuousMap.toLp 2 μ ℂ G) ?_
  intro h0
  have h0' : Lp.compMeasurePreserving (m g) (hm g) (ContinuousMap.toLp 2 μ ℂ G) =
      ContinuousMap.toLp 2 μ ℂ G := h0
  have h1 : ContinuousMap.toLp 2 μ ℂ (G.comp (m g)) = ContinuousMap.toLp 2 μ ℂ G := by
    refine Eq.trans (Lp.ext ?_) h0'
    have e1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (G.comp (m g))
    have e2 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 μ ℂ G) (hm g)
    have e3 := (hm g).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ G)
    exact e1.trans (e2.trans e3).symm
  have h2 : (F (g * 1) : ℂ) = F 1 :=
    congrArg (fun f : C(C, ℂ) => f 1) (ContinuousMap.toLp_injective μ h1)
  rw [mul_one, hF0 rfl, hF1 rfl] at h2
  simp at h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCyclic
section
open Matrix

private theorem eig_sum_zero {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O) (hal : Function.Injective al)
    (u : Fin n → Fin n → O) (hu : ∀ i, A.mulVec (u i) = al i • u i) (hs : ∑ i, u i = 0) :
    ∀ i, u i = 0 := by
  have hk : ∀ k : ℕ, ∑ i, al i ^ k • u i = 0 := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih =>
      have h := congrArg A.mulVec ih
      rw [Matrix.mulVec_zero, Matrix.mulVec_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hu, smul_smul, pow_succ]
  intro i
  funext j
  have h : (fun i => u i j) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hal
    intro k
    have := congrFun (hk k) j
    simpa [Finset.sum_apply, mul_comm] using this
  exact congrFun h i

theorem UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc :
    ∀ {O : Type} [inst : CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O),
      Function.Injective al →
        A.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : O → Polynomial O) (al i)) →
          ∃ (v : Fin n → O),
            ∀ (Y : Matrix (Fin n) (Fin n) O),
              A * Y = Y * A → Y.mulVec v = (0 : Fin n → O) → Y = (0 : Matrix (Fin n) (Fin n) O) := by
  intro O _ _ n A al hal hc
  have hw : ∀ i, ∃ w : Fin n → O, w ≠ 0 ∧ A.mulVec w = al i • w := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (al i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hc, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨w, hw0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hw
    rw [← hw]
    funext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose w hw0 hw using hw
  refine ⟨∑ i, w i, fun Y hY hv => ?_⟩
  have hYw : ∀ i, Y.mulVec (w i) = 0 := by
    apply eig_sum_zero A al hal (fun i => Y.mulVec (w i))
    · intro i
      rw [Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    · rw [← Matrix.mulVec_sum, hv]
  have hdet : (Matrix.of w).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have h := eig_sum_zero A al hal (fun i => c i • w i)
      (fun i => by rw [Matrix.mulVec_smul, hw, smul_comm])
      (by
        funext j
        have := congrFun hc j
        simpa [Matrix.vecMul, dotProduct, Finset.sum_apply] using this)
    funext i
    exact (smul_eq_zero.mp (h i)).resolve_right (hw0 i)
  ext r j
  have h : Y r = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have := congrFun (hYw i) r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact congrFun h j
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDiagonalization
section
theorem UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K),
    Function.Injective α →
      P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (α i)) →
        ∃ (V : Matrix (Fin n) (Fin n) K), IsUnit V ∧ P * V = V * Matrix.diagonal α := by
  intro K _ n P α hα hP
  have h1 : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧ P.mulVec v = α i • v := by
    intro i
    have h0 : P.charpoly.eval (α i) = 0 := by
      rw [hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using h1
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' P) α hα v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hv i
  refine ⟨(Matrix.of v).transpose, ?_, ?_⟩
  · exact Matrix.linearIndependent_cols_iff_isUnit.mp hli
  · ext j i
    have h := congrFun (hv i) j
    rw [Matrix.mul_diagonal]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEquivOfFinrank
section
open NumberField in
private theorem ext_hom {F : Type} [Field F] [NumberField F] {A : Type} [Ring A] [Algebra ℚ A]
    (φ : RingOfIntegers F →+* A) :
    ∃ ψ : F →+* A, ∀ c : RingOfIntegers F, ψ (algebraMap _ F c) = φ c := by
  haveI : Algebra.IsPushout ℤ (RingOfIntegers F) ℚ F :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ (RingOfIntegers F) F
  refine ⟨(Algebra.pushoutDesc F φ.toIntAlgHom (algebraMap ℚ A).toIntAlgHom
    (fun x y => (Algebra.commutes y (φ x)).symm)).toRingHom, fun c => ?_⟩
  exact Algebra.pushoutDesc_left F _ _ _ c

private theorem tower {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V]
    [Module ℚ V] (ψ : F →+* Module.End ℚ V) :
    letI : Module F V := Module.compHom V ψ
    IsScalarTower ℚ F V := by
  letI : Module F V := Module.compHom V ψ
  refine ⟨fun q a v => ?_⟩
  change ψ (q • a) v = q • ψ a v
  rw [map_rat_smul ψ q a]
  rfl

theorem UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    {V V' : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℚ V] [FiniteDimensional ℚ V]
    [inst_5 : AddCommGroup V'] [inst_6 : _root_.Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : NumberField.RingOfIntegers F →+* Module.End ℚ V) (φ' : NumberField.RingOfIntegers F →+* Module.End ℚ V'),
    Module.finrank ℚ V = Module.finrank ℚ V' →
      ∃ (e : V ≃ₗ[ℚ] V'),
        ∀ (c : NumberField.RingOfIntegers F) (v : V),
          (e : V → V') (((φ : NumberField.RingOfIntegers F → Module.End ℚ V) c : V → V) v) =
            ((φ' : NumberField.RingOfIntegers F → Module.End ℚ V') c : V' → V') ((e : V → V') v) := by
  intro F _ _ V V' _ _ _ _ _ _ φ φ' h
  obtain ⟨ψ, hψ⟩ := ext_hom φ
  obtain ⟨ψ', hψ'⟩ := ext_hom φ'
  letI : Module F V := Module.compHom V ψ
  letI : Module F V' := Module.compHom V' ψ'
  haveI := tower ψ
  haveI := tower ψ'
  haveI : Module.Finite F V := Module.Finite.of_restrictScalars_finite ℚ F V
  haveI : Module.Finite F V' := Module.Finite.of_restrictScalars_finite ℚ F V'
  have h2 : Module.finrank F V = Module.finrank F V' := by
    rw [← Module.finrank_mul_finrank ℚ F V, ← Module.finrank_mul_finrank ℚ F V'] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h
  let e : V ≃ₗ[F] V' := LinearEquiv.ofFinrankEq V V' h2
  refine ⟨e.restrictScalars ℚ, fun c v => ?_⟩
  rw [← hψ, ← hψ']
  exact e.map_smul (algebraMap _ F c) v
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEvaluation
section
theorem UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval :
    ∀ {C Ω J : Type}
    [inst : CommRing C] [inst_1 : Field Ω] [Fintype J] (f : (J → C) →+* Ω),
    ∃ (j : J),
      ∀ (v : J → C), (f : (J → C) → Ω) v = (f : (J → C) → Ω) ((Algebra.algebraMap C (J → C) : C → J → C) (v j)) := by
  intro C Ω J _ _ _ f
  classical
  have hsum : ∑ j : J, f (Pi.single j 1) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have h : (∑ j : J, (Pi.single j (1 : C) : J → C)) = 1 := by
      simpa using Finset.univ_sum_single (1 : J → C)
    rw [h, map_one]
  obtain ⟨j, hj⟩ : ∃ j : J, f (Pi.single j 1) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun j _ => hne j)] at hsum
    exact zero_ne_one hsum
  have hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
    rw [← map_mul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  have hone : f (Pi.single j 1) = 1 := by
    exact mul_left_cancel₀ hj (by rw [hidem, mul_one])
  refine ⟨j, fun v => ?_⟩
  have hmul : v * Pi.single j 1 =
      (Algebra.algebraMap C (J → C) : C → J → C) (v j) * Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hi]
  have h2 := congrArg f hmul
  simpa [map_mul, hone] using h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsExpansion
section
private lemma UpperTheory.Reformulated.B.Qn12.step {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (y c : ι → R) (p e x a : R) (j : ι) (hy : y j = x - a) (hc : p = e + ∑ i, c i * y i) :
    p * x = e * a + ∑ i, (c i * a + if i = j then p else 0) * y i := by
  have h1 : ∑ i, (c i * a + if i = j then p else 0) * y i = (∑ i, c i * y i) * a + p * y j := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_mul, mul_right_comm]
  rw [h1, hy]
  linear_combination a * hc

private lemma UpperTheory.Reformulated.B.Qn12.step_add {R ι : Type*} [CommRing R] [Fintype ι]
    (y c d : ι → R) (p r e f : R) (hc : p = e + ∑ i, c i * y i) (hd : r = f + ∑ i, d i * y i) :
    p + r = (e + f) + ∑ i, (c i + d i) * y i := by
  simp only [add_mul, Finset.sum_add_distrib]
  linear_combination hc + hd

theorem UpperTheory.Reformulated.B.Qn12.exists_expansion :
    ∀ {n : ℕ} (q : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ),
    ∃ (c : Fin n → MvPolynomial (Fin n) ℂ),
      p =
        (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) ((MvPolynomial.eval q : MvPolynomial (Fin n) ℂ → ℂ) p) +
          ∑ i : Fin n, c i * (MvPolynomial.X i - (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) (q i)) := by
  intro n q p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p r hp hr =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hr
    refine ⟨fun i => c i + d i, ?_⟩
    rw [map_add (f := _), map_add (f := _)]
    exact UpperTheory.Reformulated.B.Qn12.step_add _ c d p r _ _ hc hd
  | mul_X p j hp =>
    obtain ⟨c, hc⟩ := hp
    refine ⟨fun i => c i * MvPolynomial.C (q j) + if i = j then p else 0, ?_⟩
    rw [map_mul, MvPolynomial.eval_X, map_mul]
    exact UpperTheory.Reformulated.B.Qn12.step (fun i => MvPolynomial.X i - MvPolynomial.C (q i)) c p _ _ _ j rfl hc
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LowerIff
section
theorem UpperTheory.Reformulated.B.Re1.lower_iff :
    ∀ {n : ℕ} (P : Fin n → Prop) [inst : DecidablePred P],
    (∀ (a b : Fin n), a ≤ b → P b → P a) → ∀ (b : Fin n), P b ↔ (↑b : ℕ) < (Finset.filter P Finset.univ).card := by
  intro n P _ h b
  exact (Fin.lt_card_filter_univ_iff_apply_of_imp P (fun i j hij => h j i hij)).symm
end

