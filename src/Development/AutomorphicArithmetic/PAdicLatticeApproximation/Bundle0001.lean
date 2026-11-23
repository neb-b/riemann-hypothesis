module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0052
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0051
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRationalEquivOfRank
section
open NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.PELU GlobalTheory.UPel.HT
open scoped Matrix TensorProduct Classical

private theorem exists_equiv_of_finrank {F : Type} [Field F] [NumberField F] {V V' : Type}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : 𝓞 F →+* Module.End ℚ V) (φ' : 𝓞 F →+* Module.End ℚ V')
    (h : Module.finrank ℚ V = Module.finrank ℚ V') :
    ∃ e : V ≃ₗ[ℚ] V', ∀ (c : 𝓞 F) (v : V), e (φ c v) = φ' c (e v) :=
  _root_.UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank φ φ' h

private def repOn {O M : Type} [Ring O] [AddCommGroup M] [Module O M] :
    O →+* Module.End ℚ (ℚ ⊗[ℤ] M) :=
  ((Module.End.baseChangeHom ℤ ℚ M).toRingHom).comp (Module.toModuleEnd ℤ M)

private theorem repOn_apply {O M : Type} [Ring O] [AddCommGroup M] [Module O M] (b : O) :
    (repOn b : Module.End ℚ (ℚ ⊗[ℤ] M)) = (DistribSMul.toLinearMap ℤ M b).baseChange ℚ := rfl

theorem UpperTheory.exists_rational_equiv_of_rank :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Y : PLat D.O D.inv), Function.Surjective (algebraMap (𝓞 D.F) D.O) → Module.finrank ℤ Y.La = Module.finrank ℤ D.La → ∃ e : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D, ∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), e ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (e u) := by
  intro p _ D Y hs hr
  haveI := D.freeLa
  haveI := D.finLa
  have hfin : Module.finrank ℚ (ℚ ⊗[ℤ] Y.La) = Module.finrank ℚ (VQ D) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hr]
  obtain ⟨e, he⟩ := exists_equiv_of_finrank (F := D.F)
    ((repOn (O := D.O) (M := Y.La)).comp (algebraMap (𝓞 D.F) D.O))
    ((repOn (O := D.O) (M := D.La)).comp (algebraMap (𝓞 D.F) D.O)) hfin
  refine ⟨e, fun c u => ?_⟩
  obtain ⟨c, rfl⟩ := hs c
  exact he c u
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRealPeriodIsoOfPolarizedLattice
section
open NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.PELU GlobalTheory.UPel.HT
open scoped Matrix TensorProduct Classical

private theorem herm_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (x y : Fin n → ℂ) :
    star (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm A x y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm A y x := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hA.eq,
    Matrix.dotProduct_mulVec]

private theorem herm_I {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm A (Complex.I • x) y).im =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm A x y).re := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct]

private noncomputable def hermIm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm A x y).im)
    (fun x x' y => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct])
    (fun r x y => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct])
    (fun x y y' => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_add, Matrix.mulVec_add, dotProduct_add])
    (fun r x y => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul])

private theorem exists_ext {W La V : Type} [AddCommGroup W] [Module ℚ W] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup La] [Module.Finite ℤ La] [Module.Free ℤ La] (j : La →+ V)
    (hj : Function.Injective j) (hs : Submodule.span ℚ (Set.range j) = ⊤) (P : La →+ W) :
    ∃ Pq : V →ₗ[ℚ] W, ∀ z, Pq (j z) = P z := by
  let b := Module.Free.chooseBasis ℤ La
  have h0 : LinearIndependent ℤ (j ∘ b) :=
    b.linearIndependent.map' j.toIntLinearMap (LinearMap.ker_eq_bot.2 hj)
  have hli : LinearIndependent ℚ (j ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h0
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range (j ∘ b)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bq := Module.Basis.mk hli hsp
  let Pq : V →ₗ[ℚ] W := bq.constr ℚ (fun i => P (b i))
  have hb : ∀ i, Pq (j (b i)) = P (b i) := fun i => by
    have h1 : j (b i) = bq i := by simp [bq]
    rw [h1]
    exact bq.constr_basis ℚ _ i
  have hext : (Pq.restrictScalars ℤ).comp j.toIntLinearMap = P.toIntLinearMap :=
    b.ext fun i => hb i
  exact ⟨Pq, fun z => LinearMap.congr_fun hext z⟩

private theorem span_gen {La V : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup La] (j : La →+ V)
    (hs : Submodule.span ℚ (Set.range j) = ⊤) :
    Submodule.span ℝ (Set.range fun z => (1 : ℝ) ⊗ₜ[ℚ] j z) = ⊤ := by
  have h1 : ∀ v : V, (1 : ℝ) ⊗ₜ[ℚ] v ∈ Submodule.span ℝ (Set.range fun z => (1 : ℝ) ⊗ₜ[ℚ] j z) := by
    intro v
    have hv : v ∈ Submodule.span ℚ (Set.range j) := hs ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact Submodule.subset_span ⟨z, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
    | smul q x _ hx =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_of_tower_mem _ q hx
  refine eq_top_iff.2 fun u _ => ?_
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul r v =>
    have : r ⊗ₜ[ℚ] v = r • ((1 : ℝ) ⊗ₜ[ℚ] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ r (h1 v)

private theorem actOn_tg {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ[ℚ] c) (s ⊗ₜ[ℚ] v) = (r * s) ⊗ₜ[ℚ] rep c v := by
  have hl : actOn rep R (r ⊗ₜ[ℚ] c) =
      Algebra.ofId R (Module.End R (R ⊗[ℚ] V)) r * ((Module.End.baseChangeHom ℚ R V).comp rep) c :=
    Algebra.TensorProduct.lift_tmul _ _ _ r c
  rw [hl, Module.End.mul_eq_comp, LinearMap.comp_apply]
  change r • ((rep c).baseChange R (s ⊗ₜ[ℚ] v)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private theorem actOn_tt {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : ℝ) (c : C) (v : V) :
    actOn rep ℝ (r ⊗ₜ[ℚ] c) (s ⊗ₜ[ℚ] v) = (r * s) ⊗ₜ[ℚ] rep c v :=
  actOn_tg rep r s c v

private theorem bc_anti {R A M : Type} [CommRing R] [CommRing A] [AddCommGroup M] [Algebra R A]
    [Module R M] (B : LinearMap.BilinForm R M) (h : ∀ x y, B x y = -B y x) (x y : A ⊗[R] M) :
    B.baseChange A x y = -B.baseChange A y x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, neg_add]
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd, neg_add]
    | tmul c n =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h m n, mul_comm a,
        neg_smul]

private theorem E_anti {p : ℕ} [Fact p.Prime] (D : Datum p) (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ x y = -(D.EF.baseChange ℚ).baseChange ℝ y x := by
  refine bc_anti _ (bc_anti _ fun a b => ?_) x y
  have h := D.alt (a + b)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt a, D.alt b, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

private theorem E_adj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    (c : ℝ ⊗[ℚ] G.C) (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ c x) y =
      (D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ (starT G.star ℝ c).unop y) := by
  induction c using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add (f := _), LinearMap.add_apply, MulOpposite.unop_add, ha, hb]
  | tmul r d =>
    rw [starT_tmul]
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | tmul s u =>
      induction y using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul t v =>
        rw [actOn_tt, actOn_tt, LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, L.adj d u v]
        congr 1
        ring

theorem UpperTheory.exists_real_period_iso_of_polarized_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Y : PLat D.O D.inv) (P : Y.La →+ (Fin D.g → ℂ)), IsPeriod Y ρ P → ∀ (j : Y.La →+ VQ D), Function.Injective j → Submodule.span ℚ (Set.range j) = ⊤ → (∀ (c : D.O) z, j (c • z) = actQ D c (j z)) → ∀ β : G.Cˣ, (∀ z z', (Y.EF z z' : ℚ) = 2 * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j z)) (j z')) →
      ∃ (Φ : (ℝ ⊗[ℚ] VQ D) ≃ₗ[ℝ] (Fin D.g → ℂ)) (Jc : ℝ ⊗[ℚ] G.C), Jc * Jc = -1 ∧
        (∀ u, Φ (actOn L.rep ℝ Jc u) = Complex.I • Φ u) ∧
        (∀ (b : D.O) u, Φ ((actQ D b).baseChange ℝ u) = ρ b *ᵥ Φ u) ∧
        (starT G.star ℝ (inC G ℝ ((β⁻¹ : G.Cˣ) : G.C) * Jc)).unop = -(inC G ℝ ((β⁻¹ : G.Cˣ) : G.C) * Jc) ∧
        ∀ x : ℝ ⊗[ℚ] VQ D, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ (inC G ℝ ((β⁻¹ : G.Cˣ) : G.C) * Jc) x) x := by
  intro p _ D G L ρ Y P hP j hj hs hjO β hβ
  obtain ⟨hPO, hPinj, hPd, hPs, Hm, hHm, hpos, hIm⟩ := hP
  obtain ⟨Pq, hPq⟩ := exists_ext j hj hs P
  have hbij := UpperTheory.liftBaseChange_real_bijective_of_lattice D.g (VQ D) Y.La j hj hs P hPinj hPd hPs Pq hPq
  let Φ : (ℝ ⊗[ℚ] VQ D) ≃ₗ[ℝ] (Fin D.g → ℂ) :=
    LinearEquiv.ofBijective (LinearMap.liftBaseChange ℝ Pq) hbij
  have hΦt : ∀ (r : ℝ) (v : VQ D), Φ (r ⊗ₜ[ℚ] v) = r • Pq v := fun r v =>
    LinearMap.liftBaseChange_tmul ℝ Pq r v
  have hΦ1 : ∀ z, Φ ((1 : ℝ) ⊗ₜ[ℚ] j z) = P z := fun z => by rw [hΦt, one_smul, hPq]
  have hPqO : ∀ (b : D.O) (v : VQ D), Pq (actQ D b v) = ρ b *ᵥ Pq v := fun b v => by
    have h : Pq ∘ₗ actQ D b = ((Matrix.mulVecLin (ρ b)).restrictScalars ℚ) ∘ₗ Pq := by
      refine LinearMap.ext_on hs ?_
      rintro _ ⟨z, rfl⟩
      change Pq (actQ D b (j z)) = ρ b *ᵥ Pq (j z)
      rw [← hjO, hPq, hPq, hPO]
    exact LinearMap.congr_fun h v
  have hΦO : ∀ (b : D.O) u, Φ ((actQ D b).baseChange ℝ u) = ρ b *ᵥ Φ u := fun b u => by
    induction u using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.mulVec_add]
    | tmul r v => rw [LinearMap.baseChange_tmul, hΦt, hΦt, hPqO, Matrix.mulVec_smul]
  let A : Module.End ℝ (ℝ ⊗[ℚ] VQ D) :=
    Φ.symm.toLinearMap ∘ₗ (Algebra.lsmul ℝ ℝ (Fin D.g → ℂ) Complex.I) ∘ₗ Φ.toLinearMap
  have hA : ∀ u, Φ (A u) = Complex.I • Φ u := fun u => by simp [A]
  obtain ⟨hcomm, hinj⟩ := UpperTheory.commutant_eq_range_actOn_and_injective p D G L ℝ
  obtain ⟨Jc, hJc⟩ := hcomm A fun b => LinearMap.ext fun u => Φ.injective (by
    simp only [LinearMap.comp_apply]
    rw [hA, hΦO, hΦO, hA, Matrix.mulVec_smul])
  have hJ : ∀ u, Φ (actOn L.rep ℝ Jc u) = Complex.I • Φ u := fun u => by rw [hJc, hA]
  have hJJ : Jc * Jc = -1 := hinj (by
    refine LinearMap.ext fun u => Φ.injective ?_
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply, hJ, hJ, map_neg, map_one,
      LinearMap.neg_apply, one_apply_eq_self, map_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul])
  let T : Module.End ℝ (ℝ ⊗[ℚ] VQ D) := actOn L.rep ℝ (inC G ℝ ((β⁻¹ : G.Cˣ) : G.C))
  let E : (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ := (D.EF.baseChange ℚ).baseChange ℝ
  have hT : ∀ v : VQ D, T ((1 : ℝ) ⊗ₜ[ℚ] v) = (1 : ℝ) ⊗ₜ[ℚ] L.rep ((β⁻¹ : G.Cˣ) : G.C) v := fun v => by
    have := actOn_tt L.rep (1 : ℝ) 1 ((β⁻¹ : G.Cˣ) : G.C) v
    rwa [mul_one] at this
  have key : ((hermIm Hm).compl₁₂ Φ.toLinearMap Φ.toLinearMap) = (2 : ℝ) • (E ∘ₗ T) := by
    refine LinearMap.ext_on (span_gen j hs) ?_
    rintro _ ⟨z, rfl⟩
    refine LinearMap.ext_on (span_gen j hs) ?_
    rintro _ ⟨z', rfl⟩
    have h1 : ((Y.EF z z' : ℤ) : ℝ) =
        2 * ((D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j z)) (j z') : ℚ) : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hβ z z')
      simpa using this
    have h2 : E ((1 : ℝ) ⊗ₜ[ℚ] L.rep ((β⁻¹ : G.Cˣ) : G.C) (j z)) ((1 : ℝ) ⊗ₜ[ℚ] j z') =
        ((D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j z)) (j z') : ℚ) : ℝ) := by
      simp [E, LinearMap.BilinForm.baseChange_tmul, Rat.smul_one_eq_cast]
    have h3 : hermIm Hm (P z) (P z') = ((Y.EF z z' : ℤ) : ℝ) := hIm z z'
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.comp_apply, hΦ1, smul_eq_mul, hT]
    rw [h2, h3, h1]
  have key' : ∀ x y, hermIm Hm (Φ x) (Φ y) = 2 * E (T x) y := fun x y => by
    have := LinearMap.congr_fun (LinearMap.congr_fun key x) y
    simpa using this
  have hb : ∀ x, actOn L.rep ℝ (inC G ℝ ((β⁻¹ : G.Cˣ) : G.C) * Jc) x = T (actOn L.rep ℝ Jc x) := fun x => by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply]
  have sym : ∀ x y, 2 * E (actOn L.rep ℝ (inC G ℝ ((β⁻¹ : G.Cˣ) : G.C) * Jc) x) y =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Φ x) (Φ y)).re := fun x y => by
    rw [hb, ← key', hJ, ← herm_I]
    rfl
  have symm' : ∀ x y, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Φ x) (Φ y)).re =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Φ y) (Φ x)).re := fun x y => by
    rw [← herm_swap Hm hHm (Φ y) (Φ x)]
    simp
  obtain ⟨J₀, -, -, hJ₀, -⟩ := L.orient
  have hnd : ∀ w, (∀ x, E x w = 0) → w = 0 := fun w hw => by
    by_contra hne
    have h := hJ₀ w hne
    rw [show (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J₀ w) w = 0 from hw _] at h
    exact lt_irrefl _ h
  refine ⟨Φ, Jc, hJJ, hJ, hΦO, ?_, fun x hx => ?_⟩
  · set b := inC G ℝ ((β⁻¹ : G.Cˣ) : G.C) * Jc with hbdef
    have h0 : ∀ x y, E x (actOn L.rep ℝ ((starT G.star ℝ b).unop + b) y) = 0 := fun x y => by
      have a0 : E (actOn L.rep ℝ b x) y = E x (actOn L.rep ℝ (starT G.star ℝ b).unop y) := E_adj L b x y
      have a1 : E (actOn L.rep ℝ b y) x = -E x (actOn L.rep ℝ b y) := E_anti D _ _
      have a2 := sym x y
      have a3 := sym y x
      have a4 := symm' x y
      rw [map_add (f := _), LinearMap.add_apply, map_add (f := _)]
      linarith
    have h1 : (starT G.star ℝ b).unop + b = 0 := hinj (by
      rw [map_zero]
      exact LinearMap.ext fun y => hnd _ fun x => h0 x y)
    exact eq_neg_of_add_eq_zero_left h1
  · have h1 : Φ x ≠ 0 := fun h => hx (by simpa using h)
    have h2 := hpos (Φ x) h1
    have h3 := sym x x
    change 0 < E _ x
    linarith
end

