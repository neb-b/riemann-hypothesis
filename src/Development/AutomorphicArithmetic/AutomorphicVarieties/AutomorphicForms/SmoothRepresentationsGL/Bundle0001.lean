module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ArchKir
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem lmul_lmul {E : Type} [Field E] [NumberField E] {n : ℕ} (a b : Matrix (Fin n) (Fin n) (Rinf E))
    (x : Lie E n) : lmul (toL a) (lmul (toL b) x) = lmul (toL (a * b)) x := by
  change toL (a * (b * Matrix.of x)) = toL (a * b * Matrix.of x)
  rw [Matrix.mul_assoc]

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

theorem UpperTheory.V.Af.Smo.archKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.ArchStep → UpperTheory.V.Af.Smo.LinChange → UpperTheory.V.Af.Smo.ArchKir := by
  classical
  intro hC hR hA hL E _ _ n m
  induction m with
  | zero =>
    intro _
    refine ⟨fun p => psiR E (supN p.val), ?_, fun α => ⟨α, fun w _ _ hw p hp => ?_⟩⟩
    · have : supN (1 : GL (Fin n) (Rinf E)).val = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with h
        · exact Matrix.one_apply_ne (fun e => by subst e; omega)
        · rfl
      simp only [this]
      simp [psiR]
    · simp only [hw p hp, mul_assoc]
      exact integral_const_mul _ _
  | succ m ih =>
    intro hm
    obtain ⟨H, H1, hH⟩ := ih (by omega)
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨h, h1, hu, hh⟩ := hA E n m' hm
    obtain ⟨c, c1, hc⟩ := hL E n
    refine ⟨fun p => if hs : IsUnit (rowM m' (p.val m')) then h (p.val m') * (c hs.unit * H (p * hs.unit⁻¹)) else 0, ?_,
      fun α => ?_⟩
    · have hs : IsUnit (rowM m' ((1 : GL (Fin n) (Rinf E)).val m')) := by
        rw [Units.val_one, rowM_one]; exact isUnit_one
      have e : hs.unit = 1 := Units.ext (by rw [hs.unit_spec, Units.val_one, rowM_one])
      simp only [dif_pos hs, e]
      simp [h1, c1, H1]
    · obtain ⟨β₀, hβ₀⟩ := hH α
      obtain ⟨β, hβ⟩ := hh β₀
      refine ⟨β, fun w wm wb hw p hp => ?_⟩
      obtain ⟨C, hCb⟩ := wb
      have key := hβ (fun x => w (lmul (toL p.val) x)) (p.val m')
        (wm.comp (lmul (toL p.val)).continuous.measurable) ⟨C, fun x => hCb _⟩ (fun u x => by
          obtain ⟨ν, hν, hs, e⟩ := hC (Rinf E) n m' hm p hp u
          simp only [lmul_lmul]
          rw [e, ← lmul_lmul, hw ν hν, hs])
      rw [key]
      by_cases h0 : h (p.val m') = 0
      · simp [h0]
      have hs := hu _ h0
      simp only [dif_pos hs]
      have hy := hR (Rinf E) n m' p hs.unit hp hs.unit_spec
      have e1 := hβ₀ w wm ⟨C, hCb⟩ hw _ hy
      have e2 := hc hs.unit (fun y => w (lmul (toL (p * hs.unit⁻¹).val) y) * β₀ y)
      have e3 : (p * hs.unit⁻¹).val * hs.unit.val = p.val := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      simp only [lmul_lmul, e3] at e2
      rw [hs.unit_spec] at e2
      rw [e2, e1]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ArchStep
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem of_lmul (a : Matrix (Fin n) (Fin n) (Rinf E)) (x : Lie E n) :
    lmul (toL a) x = toL (a * Matrix.of x) := rfl

private theorem lmul_one_add (a : Matrix (Fin n) (Fin n) (Rinf E)) (x : Lie E n) :
    lmul (toL (1 + a)) x = x + lmul (toL a) x := by
  rw [of_lmul, of_lmul, add_mul, one_mul]; rfl

private theorem exists_bil {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] Matrix (Fin n) (Fin n) (Rinf E)) :
    ∃ B : V →L[ℝ] Lie E n →L[ℝ] Lie E n, ∀ u x, B u x = lmul (toL (L u)) x := by
  let B0 : V →ₗ[ℝ] Lie E n →L[ℝ] Lie E n :=
    { toFun := fun u => lmul (toL (L u))
      map_add' := fun u v => by
        ext1 x
        rw [ContinuousLinearMap.add_apply, of_lmul, of_lmul, of_lmul, map_add (f := _), add_mul]; rfl
      map_smul' := fun c u => by
        ext1 x
        rw [ContinuousLinearMap.smul_apply, of_lmul, of_lmul, map_smul, smul_mul_assoc]; rfl }
  exact ⟨LinearMap.toContinuousLinearMap B0, fun _ _ => rfl⟩

private theorem isUnit_of_inj (a : Matrix (Fin n) (Fin n) (Rinf E)) (h : ∀ y : Lie E n, lmul (toL a) y = 0 → y = 0) :
    IsUnit a := by
  have hi : Function.Injective (LinearMap.mulLeft ℝ a) :=
    (injective_iff_map_eq_zero _).2 fun y hy => h (toL y) hy
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.1 hi 1
  exact IsUnit.of_mul_eq_one b hb

private noncomputable def colL (m : Fin n) : EuclideanSpace ℝ (Fin n × InfinitePlace E) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Rinf E) where
  toFun u := Matrix.of fun i j => if i ≤ m ∧ j.val = m.val + 1 then (fun v => u (i, v)) else 0
  map_add' u v := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def rowL (m : Fin n) : EuclideanSpace ℝ (Fin n × InfinitePlace E) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Rinf E) where
  toFun u := Matrix.of fun i j => if i = m ∧ j ≤ m then (fun v => -u (j, v)) else 0
  map_add' u v := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' c u := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def eta (m : Fin n) (ξ : Fin n → Rinf E) : EuclideanSpace ℝ (Fin n × InfinitePlace E) :=
  WithLp.toLp 2 fun z => if z.1 ≤ m then -ξ z.1 z.2 else 0

private theorem colL_sq (m : Fin n) (u : EuclideanSpace ℝ (Fin n × InfinitePlace E)) : colL m u * colL m u = 0 := by
  ext1 i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  by_cases h : k ≤ m
  · rw [if_neg, zero_mul]
    rintro ⟨-, h'⟩
    rw [Fin.le_def] at h
    omega
  · rw [if_neg (fun h' : k ≤ m ∧ _ => h h'.1), mul_zero]

private theorem rowM_eq (m : Fin n) (ξ : Fin n → Rinf E) :
    rowM m ξ = 1 + rowL m (eta m ξ - eta m ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m)) := by
  ext i j w
  simp only [rowM, rowL, eta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply]
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    simp [h]
  · simp

private theorem inner_eta (m : Fin n) (ξ : Fin n → Rinf E) (u : EuclideanSpace ℝ (Fin n × InfinitePlace E)) :
    ⟪eta m ξ, u⟫ = -∑ v, dotLe m ξ (fun j v => u (j, v)) v := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dotLe, Finset.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ m <;> simp [eta, h, mul_comm]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Smo.archStep :
    UpperTheory.V.Af.Smo.SchTw → UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch → UpperTheory.V.Af.Smo.BetaInt → UpperTheory.V.Af.Smo.ArchStep := by
  intro h1 h2 h3 h4 E _ _ n m _
  obtain ⟨B, hB⟩ := exists_bil (colL (E := E) m)
  obtain ⟨A, hA⟩ := exists_bil (rowL (E := E) m)
  have hBB : ∀ u x, B u (B u x) = 0 := fun u x => by
    rw [hB, hB, of_lmul, of_lmul]
    change toL (colL m u * (colL m u * Matrix.of x)) = 0
    rw [← mul_assoc, colL_sq, zero_mul]; rfl
  obtain ⟨h, he, hu, hG⟩ := h1 _ _ A (eta m ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m))
  have hrow : ∀ ξ y, y + A (eta m ξ - eta m ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m)) y = lmul (toL (rowM m ξ)) y :=
    fun ξ y => by rw [rowM_eq, lmul_one_add, hA]
  refine ⟨fun ξ => h (eta m ξ), he, fun ξ hξ => isUnit_of_inj _ fun y hy => hu _ hξ y (by rw [hrow, hy]), fun α => ?_⟩
  obtain ⟨G, hG⟩ := hG α
  obtain ⟨K, hK⟩ := h2 _ _ G
  obtain ⟨K', β, hK', hβ⟩ := h3 _ _ B hBB K
  refine ⟨β, fun w ξ hw hb hw' => ?_⟩
  haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := h4 _ _ (volume : Measure (Lie E n)) B hBB G K K' hK hK' w (eta m ξ) hw hb fun u x => by
    rw [hB, ← lmul_one_add, inner_eta]
    exact hw' (fun j v => u (j, v)) x
  simp only [hβ]
  rw [this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hG, hrow]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.AvgChar
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.avgChar :
    UpperTheory.V.Af.Smo.AvgChar := by
  intro A _ L₀ L _ hidx
  classical
  let H : AddSubgroup L := L₀.addSubgroupOf L
  haveI : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero hidx
  let r : L ⧸ H → A := fun q => ((Quotient.out q : L) : A)
  have hr : Function.Injective r := Subtype.coe_injective.comp Quotient.out_injective
  refine ⟨Finset.univ.image r, Finset.univ_nonempty.image r, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).2
  · intro χ hχ ⟨x, hxL, hx⟩
    have hχeq : ∀ a b : L, (a : L ⧸ H) = b → χ a = χ b := by
      intro a b hab
      have hm : -a + b ∈ H := QuotientAddGroup.eq.mp hab
      have hm' : ((-a + b : L) : A) ∈ L₀ := AddSubgroup.mem_addSubgroupOf.mp hm
      have h1 : χ ((-a + b : L) : A) = 1 := hχ _ hm'
      have h2 : (b : A) = a + ((-a + b : L) : A) := by simp
      rw [h2, AddChar.map_add_eq_mul, h1, mul_one]
    rw [Finset.sum_image (fun q _ q' _ h => hr h)]
    let xL : L := ⟨x, hxL⟩
    have hshift : ∀ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) = χ (r q) * χ x := by
      intro q
      have h3 : ((Quotient.out (q + (xL : L ⧸ H)) : L) : L ⧸ H) = ((Quotient.out q + xL : L) : L ⧸ H) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have h4 := hχeq _ _ h3
      simp only [r]
      rw [h4, AddSubgroup.coe_add, AddChar.map_add_eq_mul]
    have hS : ∑ q : L ⧸ H, χ (r q) = (∑ q : L ⧸ H, χ (r q)) * χ x := by
      calc ∑ q : L ⧸ H, χ (r q) = ∑ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) :=
            (Equiv.sum_comp (Equiv.addRight (xL : L ⧸ H)) (fun q => χ (r q))).symm
        _ = ∑ q : L ⧸ H, χ (r q) * χ x := Finset.sum_congr rfl (fun q _ => hshift q)
        _ = (∑ q : L ⧸ H, χ (r q)) * χ x := (Finset.sum_mul _ _ _).symm
    have h5 : (∑ q : L ⧸ H, χ (r q)) * (χ x - 1) = 0 := by
      rw [mul_sub, mul_one, ← hS, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h6
    · exact absurd (sub_eq_zero.mp h6) hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.AwayInd
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem fin_bad {E : Type} [Field E] [NumberField E] {n : ℕ} (k : GL (Fin n) (Af E)) :
    {w | cmp w k ∉ GlobalTheory.LFun.KGL w (n := n)}.Finite := by
  have h : ∀ x : Af E, ∀ᶠ w in Filter.cofinite, pLoc E w x ∈ Formalism.UG.Ov E w := fun x => x.2
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w (k.val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w ((k⁻¹).val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h3 : ∀ᶠ w in Filter.cofinite, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w a b
    rw [GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv]
    exact ⟨a, b⟩
  exact h3

theorem UpperTheory.V.Af.Smo.awayInd :
    UpperTheory.V.Af.Smo.AwayInd := by
  intro E _ _ n S P h0 h1
  classical
  suffices H : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, Away S k → (∀ w ∉ T, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n)) → P k by
    intro k hk
    refine H (fin_bad k).toFinset k hk fun w hw => ?_
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 h)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun k hk h => h0 k ⟨hk, fun w => h w (Finset.notMem_empty w)⟩
  | insert w T hw ih =>
    intro k hk h
    by_cases hS : w ∈ S
    · refine ih k hk fun v hv => ?_
      by_cases e : v = w
      · subst e; rw [hk v hS]; exact one_mem _
      · exact h v (by simp [e, hv])
    · have e1 : cmp w (k * (locGL E n w (cmp w k))⁻¹) = 1 := by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL, mul_inv_cancel]
      have e2 : ∀ v, v ≠ w → cmp v (k * (locGL E n w (cmp w k))⁻¹) = cmp v k := fun v e => by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL_of_ne e, inv_one, mul_one]
      have a : Away S (k * (locGL E n w (cmp w k))⁻¹) := fun v hv => by
        rw [e2 v (fun e => hS (e ▸ hv)), hk v hv]
      have p := ih _ a fun v hv => by
        by_cases e : v = w
        · subst e; rw [e1]; exact one_mem _
        · rw [e2 v e]; exact h v (by simp [e, hv])
      have q := h1 w hS _ a e1 p (cmp w k)
      rwa [inv_mul_cancel_right] at q
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.BetaInt
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem slice_int {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup M] [NormedSpace ℝ M] (G : 𝓢(V × M, ℂ)) (y : M) :
    Integrable (fun ξ : V => G (ξ, y)) := by
  have h1 : Function.HasTemperateGrowth (fun ξ : V => (ξ, y)) := by
    have := (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : V), y))
    convert this using 1
    ext ξ <;> simp
  have h2 : AntilipschitzWith 1 (fun ξ : V => (ξ, y)) := (Isometry.antilipschitz (by
    refine Isometry.of_dist_eq fun a b => ?_
    simp [Prod.dist_eq]))
  exact (SchwartzMap.compCLMOfAntilipschitz ℝ h1 h2 G).integrable

private theorem shear_int {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [μ.IsAddHaarMeasure] (N : M →L[ℝ] M)
    (hN : ∀ x, N (N x) = 0) (f : M → ℂ) : ∫ x, f (x + N x) ∂μ = ∫ x, f x ∂μ := by
  let L : M →ₗ[ℝ] M := 1 + (N : M →ₗ[ℝ] M)
  have hnil : IsNilpotent (-(N : M →ₗ[ℝ] M) : Module.End ℝ M) := ⟨2, by
    ext x
    simp [pow_two, hN]⟩
  have hdet : LinearMap.det L = 1 := by
    have := LinearMap.eval_charpoly (-(N : M →ₗ[ℝ] M)) 1
    rw [(LinearMap.isNilpotent_iff_charpoly _).1 hnil] at this
    simpa [L] using this.symm
  have hmap : Measure.map L μ = μ := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let e : M ≃ₜ M :=
    { toFun := fun x => x + N x
      invFun := fun x => x - N x
      left_inv := fun x => by simp [hN]
      right_inv := fun x => by simp [hN]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hp : MeasurePreserving e.toMeasurableEquiv μ μ := ⟨e.toMeasurableEquiv.measurable, hmap⟩
  exact hp.integral_comp' f

theorem UpperTheory.V.Af.Smo.betaInt :
    UpperTheory.V.Af.Smo.BetaInt := by
  intro V M _ _ _ _ _ _ _ _ _ _ μ _ B hB G K K' hK hK' w η hw ⟨C, hC⟩ hwB
  have hint : ∀ (F : 𝓢(V × M, ℂ)) (a : V × M → ℂ), Measurable a → (∀ z, ‖a z‖ ≤ C) →
      ∫ u, ∫ x, a (u, x) * F (u, x) ∂μ = ∫ x, (∫ u, a (u, x) * F (u, x)) ∂μ := by
    intro F a ha haC
    refine integral_integral_swap (f := fun u x => a (u, x) * F (u, x)) ?_
    have : Integrable F ((volume : Measure V).prod μ) := F.integrable
    exact this.bdd_mul ha.aestronglyMeasurable (Filter.Eventually.of_forall haC)
  have h1 := hint K' (fun z => w z.2) (hw.comp measurable_snd) (fun z => hC _)
  have h2 := hint K (fun z => (𝐞 ⟪η, z.1⟫ : ℂ) * w z.2)
    (Measurable.mul (Continuous.measurable (by fun_prop)) (hw.comp measurable_snd)) (fun z => by rw [norm_mul, Circle.norm_coe, one_mul]; exact hC _)
  simp only [integral_const_mul] at h1
  rw [← h1]
  have h3 : ∀ u, ∫ x, w x * K' (u, x) ∂μ = ∫ x, (𝐞 ⟪η, u⟫ : ℂ) * w x * K (u, x) ∂μ := by
    intro u
    rw [← shear_int μ (B u) (hB u)]
    congr 1
    ext x
    rw [hwB, hK']
    simp [hB]
  simp only [h3]
  rw [h2]
  congr 1
  ext x
  have hF : 𝓕 (fun ξ => G (ξ, x)) = fun u => K (u, x) := by
    ext u
    rw [hK]; rfl
  have h4 := Continuous.fourierInv_fourier_eq (f := fun ξ => G (ξ, x)) (by fun_prop) (slice_int G x)
    (by rw [hF]; exact slice_int K x)
  have h5 := congrFun h4 η
  rw [hF, Real.fourierInv_eq] at h5
  rw [← h5, ← integral_const_mul]
  congr 1
  ext u
  rw [Circle.smul_def, smul_eq_mul, real_inner_comm]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.BetaSch
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.betaSch :
    UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch := by
  intro hP V M _ _ _ _ _ _ _ _ B hB K
  set Φ : V × M → V × M := fun z => (z.1, z.2 - B z.1 z.2) with hΦdef
  have hΦ : Function.HasTemperateGrowth Φ := by
    let B2 : V →L[ℝ] M →L[ℝ] V × M :=
      (ContinuousLinearMap.compL ℝ M M (V × M) (ContinuousLinearMap.inr ℝ V M)).comp B
    have h1 : Function.HasTemperateGrowth (fun z : V × M => B2 z.1 z.2) :=
      B2.bilinear_hasTemperateGrowth (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
        (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
    have h2 := (ContinuousLinearMap.id ℝ (V × M)).hasTemperateGrowth.add h1.neg
    convert h2 using 1
    funext z
    ext <;> simp [Φ, B2, sub_eq_add_neg]
  have hbd : ∃ (k : ℕ) (C : ℝ), ∀ z : V × M, ‖z‖ ≤ C * (1 + ‖Φ z‖) ^ k := by
    refine ⟨2, 1 + ‖B‖, fun z => ?_⟩
    obtain ⟨u, x⟩ := z
    set t := ‖Φ (u, x)‖ with ht
    have hu : ‖u‖ ≤ t := norm_fst_le (Φ (u, x))
    have hy : ‖x - B u x‖ ≤ t := norm_snd_le (Φ (u, x))
    have hx : x = (x - B u x) + B u (x - B u x) := by
      rw [map_sub, hB, sub_zero, sub_add_cancel]
    have hBu : ‖B u (x - B u x)‖ ≤ ‖B‖ * ‖u‖ * ‖x - B u x‖ := B.le_opNorm₂ _ _
    have hxle : ‖x‖ ≤ t + ‖B‖ * t * t := by
      calc ‖x‖ = ‖(x - B u x) + B u (x - B u x)‖ := by rw [← hx]
        _ ≤ ‖x - B u x‖ + ‖B u (x - B u x)‖ := norm_add_le _ _
        _ ≤ t + ‖B‖ * t * t := by
          have := norm_nonneg B
          have := norm_nonneg u
          have := norm_nonneg (x - B u x)
          nlinarith [mul_le_mul hu hy (norm_nonneg _) (le_trans (norm_nonneg _) hu)]
    have ht0 : 0 ≤ t := norm_nonneg _
    have hB0 := norm_nonneg B
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  let K' : 𝓢(V × M, ℂ) := SchwartzMap.compCLM ℂ hΦ hbd K
  obtain ⟨L, hL⟩ := hP V M K'
  have hι : Function.HasTemperateGrowth (fun x : M => ((0 : V), x)) := by
    convert (ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth using 1
    funext x
    rfl
  have hιb : ∃ (k : ℕ) (C : ℝ), ∀ x : M, ‖x‖ ≤ C * (1 + ‖((0 : V), x)‖) ^ k := by
    refine ⟨1, 1, fun x => ?_⟩
    have h := norm_snd_le ((0 : V), x)
    simp only [pow_one, one_mul]
    linarith
  refine ⟨K', SchwartzMap.compCLM ℂ hι hιb L, fun u x => rfl, fun x => ?_⟩
  change L ((0 : V), x) = _
  rw [hL]
  simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
end

