module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsPres

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpVars
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

open MvPowerSeries in
private theorem ev_decomp {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O) :
    ∃ h : σ → MvPowerSeries σ O, f = C (constantCoeff f) + ∑ i, MvPowerSeries.X i * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) f :=
  _root_.UpperTheory.Reformulated.B.Qf39.ev_decomp f

private theorem ev_max {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R} :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem ev_sg_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (f : A →ₐ[O] B) (j : ZMod 2) : f (sg A j) = sg B j := by
  simp [sg]

private theorem ev_sg_sq (A : Type) [CommRing A] (j : ZMod 2) : sg A j * sg A j = 1 := by
  rw [sg, ← mul_pow]; simp

theorem UpperTheory.V.Fr.ep_vars :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∃ (a g : ℕ) (p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R), Function.Surjective p ∧ (∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R) ∧ (∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j) ∧ IsHomog O (Space.Loc.par a g) (RingHom.ker p) ∧ ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨a, g, z, hz, hspan, hind⟩ := ep_basis O h2 R σ hσ (maximalIdeal R)
    ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2) (fun y hy => (ev_max σ).2 hy)
    (by
      have : (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ≤
          ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2).comap σ := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)
        · refine le_trans ?_ (Ideal.comap_mono le_sup_right)
          refine le_trans (Ideal.pow_right_mono ?_ 2) (Ideal.le_comap_pow σ 2)
          exact fun y hy => (ev_max σ).2 hy
      exact fun y hy => this hy)
    (by rw [← pow_two]; exact le_sup_right)
  obtain ⟨τ, -, hτe, hτw⟩ := ep_ps O h2 (Fin a ⊕ Fin g) (Space.Loc.par a g)
  haveI := co_mvps O O (Fin a ⊕ Fin g)
  obtain ⟨p, ⟨-, hpX⟩, -⟩ := co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) z fun s => (hz s).1
  have hC : ∀ (H : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R) (x : O),
      H (MvPowerSeries.C x) = Algebra.ofId O R x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hsurj : Function.Surjective p := by
    refine co_surj O _ R p (hspan.trans (sup_le (le_sup_of_le_left ?_) (sup_le_sup_right ?_ _)))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hpX]
      refine Ideal.mem_map_of_mem p ((ev_max p).1 ?_)
      rw [hpX]
      exact (hz s).1
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← p.commutes]
      refine Ideal.mem_map_of_mem p ?_
      exact (ev_max (Algebra.ofId O _)).2 hc
  have heq : p.comp τ = σ.comp p := by
    refine (co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) (fun s => σ (z s))
      fun s => (ev_max σ).2 (hz s).1).unique ⟨hC _, fun s => ?_⟩ ⟨hC _, fun s => ?_⟩
    · have h1 : (MvPowerSeries.X s : MvPowerSeries (Fin a ⊕ Fin g) O) ∈ evp τ (Space.Loc.par a g s) := by
        rw [hτe]; exact X_mem_wtPart O _ s
      have h3 : τ (MvPowerSeries.X s) = _ := h1
      have h4 : σ (z s) = _ := (hz s).2
      rw [AlgHom.comp_apply, h3, h4, map_mul, ev_sg_map, hpX]
    · rw [AlgHom.comp_apply, hpX]
  have heq' : ∀ y, p (τ y) = σ (p y) := fun y => DFunLike.congr_fun heq y
  have hw : ∀ j y, 2 * p (wcomp O (Space.Loc.par a g) j y) = p y + sg R j * σ (p y) := fun j y => by
    have := congrArg p (hτw j y)
    rwa [map_mul, map_ofNat, map_add, map_mul, ev_sg_map, heq'] at this
  refine ⟨a, g, p, hsurj, fun s => by rw [hpX]; exact (hz s).1, fun j => le_antisymm ?_ fun x hx => ?_,
    fun f hf j => ?_, fun h hh => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ evp τ j := by rw [hτe]; exact hf
    have h3 : τ f = _ := h1
    show σ (p f) = sg R j * p f
    rw [← heq', h3, map_mul, ev_sg_map]
  · obtain ⟨y, rfl⟩ := hsurj x
    have h1 : σ (p y) = _ := hx
    refine ⟨_, wcomp_mem O _ j y, ?_⟩
    show p _ = p y
    refine h2R.mul_left_cancel ?_
    rw [hw, h1, ← mul_assoc, ev_sg_sq, one_mul, two_mul]
  · have h1 : p f = 0 := hf
    show p _ = 0
    refine h2R.mul_left_cancel ?_
    rw [hw, h1]
    simp
  · obtain ⟨u, hu, hu0⟩ := ev_decomp h
    have h0 : p h = 0 := hh
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff h) + ∑ i, z i * p (u i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hu, map_add (f := _), map_sum, hC] at h0
      simp only [map_mul, hpX] at h0
      exact h0
    have h3 : MvPowerSeries.constantCoeff h ∈ maximalIdeal O := by
      rw [← ev_max (Algebra.ofId O R)]
      show algebraMap O R _ ∈ _
      rw [eq_neg_of_add_eq_zero_left h1]
      exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hz i).1)
    refine hind (fun s => MvPowerSeries.coeff (Finsupp.single s 1) h) ?_
    have h4 : ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) h • z s =
        -algebraMap O R (MvPowerSeries.constantCoeff h) +
          ∑ s, z s * p (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single s 1) h) - u s) := by
      rw [eq_neg_of_add_eq_zero_left h1, neg_neg, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_sub, hC, Algebra.smul_def, Algebra.ofId_apply]
      ring
    rw [h4]
    refine Submodule.add_mem_sup (neg_mem (Ideal.mem_map_of_mem _ h3)) (Ideal.sum_mem _ fun s _ => ?_)
    rw [pow_two]
    refine Ideal.mul_mem_mul (hz s).1 ((ev_max p).2 fun hU => ?_)
    have h5 := MvPowerSeries.isUnit_constantCoeff _ hU
    rw [map_sub, hu0, MvPowerSeries.constantCoeff_C, sub_self] at h5
    exact not_isUnit_zero h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsFrobeniusCorner
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cor_mul {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : A 0 1 = 0) (h2 : A 2 1 = 0) :
    (A * B).submatrix cor cor = A.submatrix cor cor * B.submatrix cor cor := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [cor, h0, h2]

private theorem mid_mul' {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : B 0 1 = 0) (h2 : B 2 1 = 0) :
    (A * B) 1 1 = A 1 1 * B 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h2]

private theorem cor_one' {K : Type} [CommRing K] :
    (1 : Matrix (Fin 3) (Fin 3) K).submatrix cor cor = 1 :=
  Matrix.submatrix_one _ (by decide)

private theorem cor_sub {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) (t : K) :
    (A - t • (1 : Matrix (Fin 3) (Fin 3) K)).submatrix cor cor = A.submatrix cor cor - t • 1 := by
  simp [Matrix.submatrix_sub, Matrix.submatrix_smul, cor_one']

private theorem cor_J {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) :
    (Jmat (R := K) 3 * Aᵀ * Jmat (R := K) 3).submatrix cor cor =
      Jmat (R := K) 2 * (A.submatrix cor cor)ᵀ * Jmat (R := K) 2 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, cor, Fin.rev]

private theorem ordProd_three {H K : Type} [CommRing K] (r : H → Matrix (Fin 3) (Fin 3) K) (ψ : Fin 3 → H → K)
    (x y z : H) : ordProd r ψ ![x, y, z] =
      (r x - ψ 0 x • 1) * (r y - ψ 1 y • 1) * (r z - ψ 2 z • 1) := by
  simp [ordProd, List.ofFn_succ, mul_assoc]

private theorem ordProd_two {H K : Type} [CommRing K] (r : H → Matrix (Fin 2) (Fin 2) K) (ψ : Fin 2 → H → K)
    (g : Fin 2 → H) : ordProd r ψ g = (r (g 0) - ψ 0 (g 0) • 1) * (r (g 1) - ψ 1 (g 1) • 1) := by
  simp [ordProd, List.ofFn_succ]

theorem UpperTheory.V.Fr.exists_frobenius_corner :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K), (∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) → CornerUnits ρ → ∃ σ : NRep F 2 K, IsCorner ρ σ := by
  intro l _ k _ F K _ ρ hodd hU
  have hc : ∀ g (i : Fin 3), i ≠ 1 → ρ.r g i 1 = 0 := by
    intro g i hi
    apply hodd
    fin_cases i <;> simp_all [w, Int.odd_iff]
  have hcs : ∀ g (t : K) (i : Fin 3), i ≠ 1 → (ρ.r g - t • 1) i 1 = 0 := by
    intro g t i hi
    rw [Matrix.sub_apply, Matrix.smul_apply, hc g i hi, Matrix.one_apply_ne hi, smul_zero, sub_zero]
  have hinj : Function.Injective cor := by decide
  let s : F.G0 →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => (ρ.r g).submatrix cor cor
      map_one' := by simp only [map_one, cor_one']
      map_mul' := fun a b => by
        simp only [map_mul]
        exact cor_mul _ _ (hc a 0 (by decide)) (hc a 2 (by decide)) }
  refine ⟨⟨s, fun v i => ρ.ψ v (cor i), ?_, ?_, ?_⟩, ?_⟩
  · intro g
    show (ρ.r (F.star g)).submatrix cor cor =
      Jmat (R := K) 2 * ((ρ.r g).submatrix cor cor)ᵀ * Jmat (R := K) 2
    rw [ρ.pol, cor_J]
  · intro i j hij
    have hd := ρ.diag (cor i) (cor j) (hinj.ne hij)
    rw [Matrix.sub_apply] at hd ⊢
    exact hd
  · intro v g
    obtain ⟨g₁, -, -, u1⟩ := hU v
    have key := frobenius_corner_order_skips (s.comp (F.loc0 v)) (fun x => (ρ.ψ v 0 x : K)) ((Units.coeHom K).comp (ρ.ψ v 2)) g₁ (ρ.ψ v 1 g₁ : K) ?det ?three (g 0) (g 1)
    · rw [ordProd_two]
      exact key
    · show IsUnit ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1).det
      rw [← cor_sub, Matrix.det_fin_two]
      simpa [cor, Matrix.one_apply] using u1
    · intro x y
      show ((ρ.r (F.loc0 v x)).submatrix cor cor - (ρ.ψ v 0 x : K) • 1) * ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1) * ((ρ.r (F.loc0 v y)).submatrix cor cor - (ρ.ψ v 2 y : K) • 1) = 0
      have h3 := ρ.ord v ![x, g₁, y]
      rw [ordProd_three] at h3
      beta_reduce at h3
      rw [← cor_sub, ← cor_sub, ← cor_sub, mul_assoc, ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← mul_assoc, h3, Matrix.submatrix_zero]
      rfl
  · refine ⟨hodd, fun g i j => rfl, fun v i g => rfl, fun v g => ?_⟩
    obtain ⟨g₁, u0, u2, -⟩ := hU v
    have h3 := ρ.ord v ![g₁, g, g₁]
    rw [ordProd_three] at h3
    beta_reduce at h3
    have h11 := congrFun (congrFun h3 1) 1
    rw [mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide))] at h11
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h11
    rw [u2.mul_left_eq_zero, u0.mul_right_eq_zero, sub_eq_zero] at h11
    exact h11
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapSRange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.finrank_structMapS_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strS k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h')
  set χ := F.Ψ⁻¹ ^ 2 * F.delK k with hχ
  have hc : ((χ F.c : kˣ) : k) = -1 := by
    simp [hχ, Frame.delK, hF.del_c, hF.Ψ_c]
  let Z := Z1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)
  let f : Z →ₗ[k] (F.G0 → k) :=
    { toFun := fun x g => (x.1.1 g + ((χ g : k) * x.1.1 F.c - x.1.1 F.c) * 2⁻¹) * (F.Ψ g : k)
      map_add' := by
        intro x y
        funext g
        simp
        ring
      map_smul' := by
        intro r x
        funext g
        simp
        ring }
  have hker : Submodule.comap Z.subtype (continuousCoboundaries1 (chRep χ) fun _ => (⊥ : Submodule k k)) ≤ LinearMap.ker f := by
    rintro ⟨x, hx⟩ hb
    rw [Submodule.mem_comap] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [LinearMap.mem_ker]
    funext g
    have e1 := hX (g : F.Γ)
    have e2 := hX F.c
    simp only [Submodule.subtype_apply, chRep_apply, hc] at e1 e2
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [e1, e2]
    field_simp
    ring
  let L := Submodule.liftQ _ f hker
  have hle : F.strS k ≤ LinearMap.range L := by
    intro a ha
    obtain ⟨x, hx, hx0, hax⟩ := frame_extension_of_locallyConstant hF a ha
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    funext g
    simp [f, hx0, hax]
  calc Module.rank k (F.strS k) ≤ Module.rank k (LinearMap.range L) := Submodule.rank_mono hle
    _ ≤ Module.rank k (H1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)) := rank_range_le L
    _ ≤ C₀ := hF.b1p
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GrMIff
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have h : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have s0 : sg R 0 = 1 := pow_zero _
  have s1 : sg R 1 = -1 := pow_one _
  have e : (0 : ZMod 2) - 1 = 1 := by decide
  rcases h i with rfl | rfl <;> rcases h j with rfl | rfl
  · rw [sub_self, s0, one_mul]
  · rw [e, s0, one_mul]
  · rw [sub_zero, s0, mul_one]
  · rw [sub_self, s0, s1, neg_mul_neg, one_mul]

private theorem sg_sq (R : Type) [CommRing R] (i : ZMod 2) : sg R i * sg R i = 1 := by
  rw [← sg_sub, sub_self]
  exact pow_zero _

private def sgM (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal fun a => sg R (α a)

private theorem sgM_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : sgM R α * sgM R α = 1 := by
  simp only [sgM, Matrix.diagonal_mul_diagonal, sg_sq, Matrix.diagonal_one]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ (σ : R →+* R).mapMatrix M = sgM R α * M * sgM R β := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [sgM, sgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  show σ (M a b) = sg R (α a - β b) * M a b ↔ σ (M a b) = _
  rw [sg_sub, mul_right_comm]

private theorem grM_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) (h' : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff] at h h' ⊢
  rw [map_mul, h, h']
  calc sgM R α * M * sgM R β * (sgM R β * N * sgM R γ)
      = sgM R α * M * (sgM R β * sgM R β) * N * sgM R γ := by simp only [Matrix.mul_assoc]
    _ = sgM R α * (M * N) * sgM R γ := by rw [sgM_sq, Matrix.mul_one, Matrix.mul_assoc _ M]

private theorem grM_inv {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (h : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff] at h ⊢
  have h1 : (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) *
      (σ : R →+* R).mapMatrix ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : sgM R β * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * sgM R α *
      (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [h]
    calc _ = sgM R β * (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (sgM R α * sgM R α) *
          (g : Matrix (Fin 3) (Fin 3) R)) * sgM R β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [sgM_sq, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, sgM_sq]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem grM_J {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) :
    GrM σ pq pq (Jmat (R := R) 3) := by
  intro a b
  unfold Jmat
  split_ifs with e
  · have : pq a - pq b = 0 := by
      subst e
      revert a
      decide
    rw [this]
    show σ 1 = sg R 0 * 1
    rw [map_one, mul_one]
    exact (pow_zero _).symm
  · exact Submodule.zero_mem _

private theorem grM_tr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) : GrM σ β α Mᵀ := by
  intro a b
  have e : σ (M b a) = sg R (α b - β a) * M b a := h b a
  show σ (M b a) = sg R (β a - α b) * M b a
  rw [e, sg_sub, sg_sub, mul_comm (sg R (α b))]

theorem UpperTheory.V.Fr.ep_grm :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R), (∀ α, GrM σ α α 1) ∧ (∀ α β M N, GrM σ α β M → GrM σ α β N → GrM σ α β (M - N)) ∧ (∀ α β γ M N, GrM σ α β M → GrM σ β γ N → GrM σ α γ (M * N)) ∧ (∀ α β (g : GL (Fin 3) R), GrM σ α β (g : Matrix (Fin 3) (Fin 3) R) → GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) ∧ ∀ (e : ℤˣ) (g : GL (Fin 3) R), GrM σ pq pq (g : Matrix (Fin 3) (Fin 3) R) → GrM σ pq pq ((sgnAct (m := 3) (R := R) e g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O R _ _ _ σ
  refine ⟨fun α => ?_, fun α β M N h h' a b => Submodule.sub_mem _ (h a b) (h' a b), grM_mul σ, grM_inv σ,
    fun e g h => ?_⟩
  · rw [grM_iff, map_one, Matrix.mul_one, sgM_sq]
  · rcases Int.units_eq_one_or e with rfl | rfl
    · rwa [sgnAct_one]
    · rw [sgnAct_neg_one, theta_val]
      exact grM_mul σ _ pq _ _ _ (grM_mul σ _ pq _ _ _ (grM_J σ) (grM_tr σ _ _ _ (grM_inv σ _ _ g h))) (grM_J σ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IwahoriFactorizationLowerDiagUpper
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.iwahori_factorization_lower_diag_upper :
    ∀ {H Q : Type} [CommRing Q] (r : H → Matrix (Fin 3) (Fin 3) Q) (ψ : Fin 3 → H → Q) (s₀ : H), (∀ i j, i ≠ j → IsUnit (ψ i s₀ - ψ j s₀)) → (∀ s i j, i < j → r s i j = 0) → (∀ s i, r s i i = ψ i s) → (∀ g, ordProd r ψ g = 0) → ∃ α β γ : Q, ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * α ∧ r s 2 1 = (ψ 1 s - ψ 2 s) * β ∧ r s 2 0 = (ψ 0 s - ψ 2 s) * γ - (ψ 1 s - ψ 2 s) * (α * β) := by
  intro H Q _ r ψ s₀ hu hup hd h0
  have key : ∀ a b c : H, (r a - ψ 0 a • 1) * ((r b - ψ 1 b • 1) * (r c - ψ 2 c • 1)) = 0 := by
    intro a b c
    simpa [ordProd, List.ofFn_succ] using h0 ![a, b, c]
  obtain ⟨u', e1⟩ : ∃ u' : Q, (ψ 0 s₀ - ψ 1 s₀) * u' = 1 := ⟨_, (hu 0 1 (by decide)).mul_val_inv⟩
  obtain ⟨v', e2⟩ : ∃ v' : Q, (ψ 1 s₀ - ψ 2 s₀) * v' = 1 := ⟨_, (hu 1 2 (by decide)).mul_val_inv⟩
  obtain ⟨w', e3⟩ : ∃ w' : Q, (ψ 0 s₀ - ψ 2 s₀) * w' = 1 := ⟨_, (hu 0 2 (by decide)).mul_val_inv⟩
  have hx : ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * (r s₀ 1 0 * u') := by
    intro s
    have e := congrFun (congrFun (key s₀ s s₀) 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have F : r s₀ 1 0 * (ψ 0 s - ψ 1 s) = (ψ 0 s₀ - ψ 1 s₀) * r s 1 0 := by
      linear_combination w' * e - (r s₀ 1 0 * (ψ 0 s - ψ 1 s) - (ψ 0 s₀ - ψ 1 s₀) * r s 1 0) * e3
    linear_combination (-(r s 1 0)) * e1 - u' * F
  have hy : ∀ s, r s 2 1 = (ψ 1 s - ψ 2 s) * (r s₀ 2 1 * v') := by
    intro s
    have e := congrFun (congrFun (key s₀ s₀ s) 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have G : r s₀ 2 1 * (ψ 1 s - ψ 2 s) = (ψ 1 s₀ - ψ 2 s₀) * r s 2 1 := by
      linear_combination (-w') * e - (r s₀ 2 1 * (ψ 1 s - ψ 2 s) - (ψ 1 s₀ - ψ 2 s₀) * r s 2 1) * e3
    linear_combination (-(r s 2 1)) * e2 - v' * G
  refine ⟨r s₀ 1 0 * u', r s₀ 2 1 * v',
    r s₀ 1 0 * u' * (r s₀ 2 1 * v') +
      ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) * w' * v', fun s => ⟨hx s, hy s, ?_⟩⟩
  have e := congrFun (congrFun (key s₀ s₀ s) 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
    hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
  have Z : (ψ 0 s₀ - ψ 2 s₀) * (ψ 1 s₀ - ψ 2 s₀) * r s 2 0 =
      (ψ 0 s₀ - ψ 2 s₀) * r s₀ 2 1 * r s 1 0 +
        (ψ 0 s - ψ 2 s) * ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) := by
    linear_combination e
  linear_combination w' * v' * Z + r s₀ 2 1 * v' * hx s +
    (r s₀ 2 1 * v' * r s 1 0 - r s 2 0) * e3 - (ψ 0 s₀ - ψ 2 s₀) * w' * r s 2 0 * e2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMazur
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mazur :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] [Module.Finite (ResidueField O) H], HasObs (O := O) R H → ∃ (p : MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O →ₐ[O] R) (f : Fin (Module.finrank (ResidueField O) H) → MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O), Function.Surjective p ∧ RingHom.ker p = Ideal.span (Set.range f) := by
  intro O _ _ _ _ _ R _ _ _ H _ _ _ hob
  obtain ⟨a, π, f, hπ, hker, hcard⟩ := obs_pres O R H (by
    intro A _ _ _ p hp hK κ _ ε hspan hmin
    obtain ⟨ob, hob'⟩ := hob A p hp hK
    obtain ⟨co, hco⟩ := pr_dualb O A (RingHom.ker p) κ ε hK hspan hmin
    refine ⟨fun u => ob (co u), ?_⟩
    intro c hc A' _ _ _ p' p'' η hp' hcomp hη hη0 hε
    have hw0 : ob (∑ u, residue O (c u) • co u) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
      exact hc
    refine hob' _ hw0 A' p' p'' hcomp hp' ?_
    intro y hy
    obtain ⟨b, hb, hy'⟩ := hco y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy', map_sum]
    simp only [map_smul, hε, smul_smul]
    rw [← Finset.sum_smul]
    have hm : ∑ u, b u * c u ∈ maximalIdeal O := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← residue_eq_zero_iff, map_sum]
      simp only [map_mul, hb]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hy
      rw [← hy]
      exact Finset.sum_congr rfl (fun u _ => mul_comm _ _)
    haveI := IsCO.isLocalHom (O := O) (R := A')
    rw [Algebra.smul_def]
    exact hη _ (map_nonunit (algebraMap O A') _ hm))
  have hT := (pr_tan O R).2
  haveI := (pr_tan O R).1
  classical
  haveI := Fintype.ofFinite (ResidueField O)
  haveI : Finite (Tan O R) := Module.finite_of_finite (ResidueField O)
  haveI := Fintype.ofFinite (Tan O R)
  have h2 : 2 ≤ Fintype.card (ResidueField O) := Fintype.one_lt_card
  have hTc : Nat.card (Tan O R) =
      Fintype.card (ResidueField O) ^ Module.finrank (ResidueField O) (Tan O R) := by
    rw [Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have ha : a = Module.finrank (ResidueField O) (Tan O R) := by
    apply Nat.pow_right_injective h2
    change Fintype.card (ResidueField O) ^ a = Fintype.card (ResidueField O) ^ _
    rw [← hTc, ← hT, hcard, Nat.card_eq_fintype_card]
  subst ha
  exact ⟨π, f, hπ, hker⟩
end

