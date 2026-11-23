module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeProperties.LeftMulMatrixEmbeddingDetEqNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinBetween
section
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem fin_between {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
    (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (x : Etau K τ) (hx : x.im ≠ 0) :
    {S : Set (Etau K τ) | IsLat O τ S ∧ 1 ∈ S ∧ x ∈ S ∧ ∀ w ∈ S, IsIntegral O w}.Finite := by
  haveI := L.frac
  classical
  obtain ⟨N, hN, hden⟩ := int_denom L hτ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) ({-x.re / x.im, 1 / x.im} : Finset K)
  obtain ⟨p, hp⟩ := hr _ (Finset.mem_insert_self _ _)
  obtain ⟨q, hq⟩ := hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [Algebra.smul_def] at hp hq
  haveI := finite_quot_span L (mul_ne_zero hN (nonZeroDivisors.coe_ne_zero r))
  let M := integralClosure O (Etau K τ)
  haveI : Module.Finite O M := Module.Finite.iff_fg (N := Subalgebra.toSubmodule M).2 (intE_fg L hτ)
  let I : Submodule O M := Ideal.span {N * r} • ⊤
  haveI : Finite (M ⧸ I) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  let f : Set (M ⧸ I) → Set (Etau K τ) := fun A => Subtype.val '' (I.mkQ ⁻¹' A)
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨⟨⟨g, rfl⟩, -⟩, h1, h2, h3⟩
  set T := Submodule.span O (g : Set (Etau K τ))
  refine ⟨I.mkQ '' (Subtype.val ⁻¹' (T : Set (Etau K τ))), ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
    have h4 : y - z ∈ (Ideal.span {N * r} • ⊤ : Submodule O M) := (Submodule.Quotient.eq _).1 e.symm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h4
    obtain ⟨m, -, hm⟩ := h4
    have hm' : (N * r) • (m : Etau K τ) = y - z := congrArg Subtype.val hm
    obtain ⟨a, b, ha, hb⟩ := hden _ m.2
    have e2 : (y : Etau K τ) = z + ((r * a + b * p) • (1 : Etau K τ) + (b * q) • x) := by
      rw [← sub_eq_iff_eq_add', ← hm', ← algebraMap_smul K (N * r), ← algebraMap_smul K (r * a + b * p), ← algebraMap_smul K (b * q)]
      simp only [map_mul, map_add (f := _), hp, hq, ← ha, ← hb]
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, - algebraMap_smul] <;> field_simp <;> ring
    rw [e2]
    exact T.add_mem hz (T.add_mem (T.smul_mem _ h1) (T.smul_mem _ h2))
  · intro hw
    exact ⟨⟨w, h3 w hw⟩, ⟨⟨w, h3 w hw⟩, hw, rfl⟩, rfl⟩

open UpperTheory.V.Z.Sym.Loc.GL in
theorem UpperTheory.V.Z.Sym.Loc.finG : UpperTheory.V.Z.Sym.Loc.FinG := by
  intro O K _ _ _ _ _ Δ τ L hτ j hj z hz
  haveI := L.frac
  classical
  obtain ⟨g, hg⟩ := (gConj O K Δ τ L hτ (j0 τ) j leftMulMatrixEmbedding_omega_trace hj).1
  have det : ∀ (y : GL (Fin 2) K) (s : Kˣ) (k : GL (Fin 2) K), k ∈ KG O K → y⁻¹ * jU j z * y = sc s * k →
      ∃ e : Oˣ, QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K e * (s : K) ^ 2 := fun y s k hk e => by
    obtain ⟨u, hu⟩ := kg_det hk
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) e
    simp only [Units.val_mul] at this
    rw [Matrix.det_units_conj', Matrix.det_mul, hu, sc_val, Matrix.det_smul] at this
    exact ⟨u, by rw [← j_det j hj]; exact this.trans (by simp [mul_comm])⟩
  by_cases h0 : ∃ y₀ : GL (Fin 2) K, y₀⁻¹ * jU j z * y₀ ∈ ZK O K
  swap
  · exact ⟨∅, fun y hy => absurd ⟨y, hy⟩ h0⟩
  obtain ⟨y₀, hy₀⟩ := h0
  obtain ⟨s, k₀, hk₀, e₀⟩ := zk_iff.1 hy₀
  obtain ⟨ε, hε⟩ := det y₀ s k₀ hk₀ e₀
  let u : (Etau K τ)ˣ := su τ s⁻¹ * z
  have hun : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε := by
    rw [Units.val_mul, su_mul, Algebra.smul_def, map_mul, QuadraticAlgebra.norm_algebraMap, hε, Units.val_inv_eq_inv_val]
    field_simp
  have hui : (u : Etau K τ).im ≠ 0 := by
    rw [Units.val_mul, su_mul]
    simpa using hz
  have fin := fin_between L hτ u hui
  choose! rep hrep using fun S (h : IsLat O τ S) => isLat_lat h
  refine ⟨fin.toFinset.image fun S => g⁻¹ * rep S, fun y hy => ?_⟩
  have h1 : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) ∈ ZK O K := by
    have : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) = sc s⁻¹ * (y⁻¹ * jU j z * y) := by
      rw [map_mul, jU_su, hg, mul_assoc (sc s⁻¹), ← mul_assoc, ← sc_comm]; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) hy
  have h2 := ent_of_zk ε (by
    rw [← mul_assoc, Units.val_mul, Units.val_mul, Matrix.det_units_conj', ← hun]; exact leftMulMatrixEmbedding_det_eq_norm _) h1
  have h3 := lat_le (τ := τ).2 h2
  rw [lat_mul] at h3
  obtain ⟨t, ht⟩ := PS.gen_ex L hτ (lat_isLat (O := O) (g * y))
  have hl := PS.lat_ml (lat_isLat (O := O) (τ := τ) (g * y)) t⁻¹
  have hm : PS.ml t⁻¹ (LL O τ (g * y)) ∈ fin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨hl, PS.mem_ml.2 (by simpa using ht.1), PS.mem_ml.2 ?_, ?_⟩
    · rw [inv_inv, mul_comm]; exact h3 ⟨_, ht.1, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ht.2 w hw
  refine ⟨t, _, Finset.mem_image_of_mem _ hm, (jU j t * (g⁻¹ * rep (PS.ml t⁻¹ (LL O τ (g * y)))))⁻¹ * y, ?_, by group⟩
  have : cls τ (LL O τ (jU (j0 τ) t * rep (PS.ml t⁻¹ (LL O τ (g * y))))) = cls τ (LL O τ (g * y)) := by
    rw [lat_mul, ← hrep _ hl]
    change cls τ (PS.ml _ _) = _
    rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  rw [cls_lat] at this
  rw [hg]
  simpa [mul_assoc] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.MemRangeIff
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private lemma mem_range_iff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    (g : GL (Fin 2) S) : g ∈ (Matrix.GeneralLinearGroup.map f).range ↔
      ∀ i j, (g : Matrix (Fin 2) (Fin 2) S) i j ∈ f.range ∧ ((g⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) i j ∈ f.range := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    refine ⟨⟨(h : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩, ?_⟩
    rw [← map_inv]
    exact ⟨((h⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩
  · intro h
    choose A hA using fun i j => (h i j).1
    choose B hB using fun i j => (h i j).2
    have eA : (Matrix.of A).map f = (g : Matrix (Fin 2) (Fin 2) S) := by ext i j; exact hA i j
    have eB : (Matrix.of B).map f = ((g⁻¹ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by ext i j; exact hB i j
    have inj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) R => M.map f) := Matrix.map_injective hf
    refine ⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, ?_⟩
    · simp only [Matrix.map_mul, eA, eB, Matrix.map_one _ (map_zero f) (map_one f), Units.mul_inv]
    · simp only [Matrix.map_mul, eA, eB, Matrix.map_one _ (map_zero f) (map_one f), Units.inv_mul]
    · exact Units.ext eA

private lemma mem_DX {K : Type} [Field K] {Δ : K} (g : GL (Fin 2) (Lsq K Δ)) :
    g ∈ DX Δ ↔ !![0, 1; -1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star = (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
  change Matrix.GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹ ↔ _
  rw [inv_inv, mul_assoc, eq_inv_mul_iff_mul_eq, Units.ext_iff]
  rfl

private lemma star_fix {K : Type} [Field K] {Δ : K} (h2 : (2 : K) ≠ 0) (x : Lsq K Δ) :
    star x = x ↔ x ∈ (algebraMap K (Lsq K Δ)).range := by
  constructor
  · intro h
    have := congrArg QuadraticAlgebra.im h
    simp only [QuadraticAlgebra.im_star] at this
    have h0 : x.im = 0 := by
      have : 2 * x.im = 0 := by linear_combination -this
      exact (mul_eq_zero.1 this).resolve_left h2
    exact ⟨x.re, by ext <;> simp [h0]⟩
  · rintro ⟨y, rfl⟩
    ext <;> simp

private lemma exists_phi {K : Type} [Field K] {Δ : K} (h2 : (2 : K) ≠ 0) (P : GL (Fin 2) (Lsq K Δ))
    (hP : ∀ X : Matrix (Fin 2) (Fin 2) (Lsq K Δ), !![0, 1; -1, 0] * X.map star = X * !![0, 1; -1, 0] ↔
        ((P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))).map star = (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))) :
    ∃ φ : DX Δ ≃* GL (Fin 2) K, ∀ g, Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)) (φ g) = P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹ := by
  have hinj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective
  have key : ∀ g : GL (Fin 2) (Lsq K Δ), g ∈ DX Δ ↔
      ∀ i j, ((P * g * P⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j ∈ (algebraMap K (Lsq K Δ)).range := by
    intro g
    rw [mem_DX, hP, ← Matrix.ext_iff]
    simp only [← star_fix h2, Units.val_mul, Matrix.map_apply]
  let ψ : GL (Fin 2) K →* GL (Fin 2) (Lsq K Δ) :=
    (MulAut.conj P⁻¹).toMonoidHom.comp (Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)))
  have hψ : ∀ h, P * ψ h * P⁻¹ = Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)) h := by
    intro h
    change P * (P⁻¹ * _ * P⁻¹⁻¹) * P⁻¹ = _
    group
  have hmem : ∀ h, ψ h ∈ DX Δ := by
    intro h
    rw [key, hψ]
    exact fun i j => ⟨(h : Matrix (Fin 2) (Fin 2) K) i j, rfl⟩
  have hbij : Function.Bijective (ψ.codRestrict (DX Δ) hmem) := by
    constructor
    · intro a b hab
      have e : ψ a = ψ b := congrArg Subtype.val hab
      have e' := hψ a
      rw [e, hψ, Units.ext_iff] at e'
      exact (Units.ext (Matrix.map_injective hinj e')).symm
    · intro g
      obtain ⟨h, hh⟩ := (mem_range_iff _ hinj (P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹)).2 fun i j => ⟨(key _).1 g.2 i j, by
        have e : (P * (g : GL (Fin 2) (Lsq K Δ)) * P⁻¹)⁻¹ = P * (g : GL (Fin 2) (Lsq K Δ))⁻¹ * P⁻¹ := by group
        rw [e]
        exact (key _).1 (inv_mem g.2) i j⟩
      refine ⟨h, Subtype.ext ?_⟩
      have e := hψ h
      rw [hh] at e
      exact mul_left_cancel (mul_right_cancel e)
  refine ⟨(MulEquiv.ofBijective _ hbij).symm, fun g => ?_⟩
  rw [← hψ]
  have := congrArg Subtype.val ((MulEquiv.ofBijective _ hbij).apply_symm_apply g)
  exact congrArg (fun x => P * x * P⁻¹) this

theorem UpperTheory.V.Z.Sym.Loc.dIso :
    UpperTheory.V.Z.Sym.Loc.DIso := by
  intro O K _ _ _ _ _ Δ hl
  haveI := hl.frac
  have h2 : (2 : K) ≠ 0 := by
    have := (hl.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨P, hPi, hP⟩ := UpperTheory.V.Z.Sym.Loc.splitJ O K Δ hl
  obtain ⟨φ, hφ⟩ := exists_phi h2 P hP
  have hinj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective
  have minj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) K => M.map (algebraMap K (Lsq K Δ))) :=
    Matrix.map_injective hinj
  have hm : ∀ g, (φ g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Lsq K Δ)) =
      (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt g * (P⁻¹ : GL (Fin 2) (Lsq K Δ)) := fun g => congrArg Units.val (hφ g)
  have hdet : ∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).det = (mt g).det := by
    intro g
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_units_conj]
  have htr : ∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).trace = (mt g).trace := by
    intro g
    rw [← Matrix.trace_units_conj P, ← hm]
    simp [Matrix.trace_fin_two]
  refine ⟨φ, fun g => ?_, fun z g => ?_, hdet, fun τ γ j hγ hj => ?_⟩
  · let H := (Matrix.GeneralLinearGroup.map (n := Fin 2)
      ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ)).range
    have hr : ∀ x : Lsq K Δ, x ∈ ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).range ↔
        IsIntegral O x := fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    have hH : ∀ x : GL (Fin 2) (Lsq K Δ), x ∈ H ↔ ∀ i j, IsIntegral O ((x : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) ∧
        IsIntegral O (((x⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j) := by
      intro x
      rw [mem_range_iff _ Subtype.val_injective]
      simp only [hr]
    have hPH : P ∈ H := (hH P).2 hPi
    have hr' : ∀ x : K, IsIntegral O (algebraMap K (Lsq K Δ) x) ↔ x ∈ (algebraMap O K).range := by
      intro x
      rw [isIntegral_algebraMap_iff , IsIntegrallyClosed.isIntegral_iff]
      rfl
    change φ g ∈ (Matrix.GeneralLinearGroup.map (algebraMap O K)).range ↔ (g : GL (Fin 2) (Lsq K Δ)) ∈ H
    rw [← H.mul_mem_cancel_left hPH, ← H.mul_mem_cancel_right (inv_mem hPH), ← hφ, hH,
      mem_range_iff _ (IsFractionRing.injective O K), ← map_inv (Matrix.GeneralLinearGroup.map (algebraMap K (Lsq K Δ)))]
    simp only [← hr']
    rfl
  · rw [Units.ext_iff, ← minj.eq_iff]
    beta_reduce
    rw [hm, Units.mul_inv_eq_iff_eq_mul]
    have e : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (Lsq K Δ)) =
        Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := by
      ext i j : 1
      by_cases h : i = j <;> simp [h]
    rw [e, (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq, Units.mul_right_inj]
    rfl
  · have hd : (φ γ : Matrix (Fin 2) (Fin 2) K).det = 1 := hinj (by rw [hdet, hγ.1, map_one])
    have ht : (φ γ : Matrix (Fin 2) (Fin 2) K).trace = τ := hinj (by rw [htr, hγ.2])
    have hu : (φ γ : Matrix (Fin 2) (Fin 2) K) * (φ γ : Matrix (Fin 2) (Fin 2) K) =
        (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) + τ • (φ γ : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.det_fin_two] at hd
      rw [Matrix.trace_fin_two] at ht
      rw [← ht]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination -hd
    have hω : QuadraticAlgebra.lift ⟨_, hu⟩ (ω : Etau K τ) = (φ γ : Matrix (Fin 2) (Fin 2) K) := by
      change (ω : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) K) + (ω : Etau K τ).im • _ = _
      simp
    refine ⟨QuadraticAlgebra.lift ⟨_, hu⟩, hω, by rw [hω, ht], fun z => Units.ext (minj ?_)⟩
    change _ = ((z : Etau K τ).re • (1 : Matrix (Fin 2) (Fin 2) K) + (z : Etau K τ).im • (φ γ : Matrix (Fin 2) (Fin 2) K)).map _
    beta_reduce
    rw [hm, hj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, ← hm,
      mul_one, Units.mul_inv]
    ext a b : 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply]
    by_cases h : a = b <;> simp [h, Algebra.smul_def]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.sumShift : UpperTheory.V.Z.Sym.Loc.SumShift := by
  intro O K _ _ _ _ _ Δ τ L hτ f hf g
  have pm : ∀ x : K, hs (τ ^ 2 - 4) x = 1 ∨ hs (τ ^ 2 - 4) x = -1 := by
    intro x
    unfold hs
    split_ifs <;> simp
  have hmul : ∀ a b : Kˣ, hs (τ ^ 2 - 4) ((a * b : Kˣ) : K) = hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (b : K) := by
    intro a b
    rw [Units.val_mul]
    exact hsMul O K Δ L _ a b hτ a.ne_zero b.ne_zero
  have hone : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1 := by
    unfold hs
    rw [if_pos]
    exact ⟨1, 0, by simp⟩
  have hsq : ∀ a : Kˣ, hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (a : K) = 1 := by
    intro a
    rcases pm (a : K) with h | h <;> rw [h] <;> norm_num
  have hinv : ∀ a : Kˣ, hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K) = hs (τ ^ 2 - 4) (a : K) := by
    intro a
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    calc hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K)
        = hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) ((a⁻¹ : Kˣ) : K) := by
          rw [hsq, one_mul]
      _ = hs (τ ^ 2 - 4) (a : K) := by rw [mul_assoc, ← h, mul_one]
  have hmk : ∀ a b : Kˣ, (a : Kˣ ⧸ NE τ) = b ↔ hs (τ ^ 2 - 4) (a : K) = hs (τ ^ 2 - 4) (b : K) := by
    intro a b
    rw [QuotientGroup.eq, hsNE O K Δ τ L hτ, hmul, hinv]
    constructor
    · intro h
      calc hs (τ ^ 2 - 4) (a : K) = hs (τ ^ 2 - 4) (a : K) * (hs (τ ^ 2 - 4) (a : K) * hs (τ ^ 2 - 4) (b : K)) := by
            rw [h, mul_one]
        _ = hs (τ ^ 2 - 4) (b : K) := by rw [← mul_assoc, hsq, one_mul]
    · intro h
      rw [h, hsq]
  have inv_of : ∀ φ : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, φ (t * x) = φ x) →
      ∀ a b : Kˣ, (a : Kˣ ⧸ NE τ) = b → φ a = φ b := by
    intro φ hφ a b h
    have h' := QuotientGroup.eq.1 h
    have e : b = (a⁻¹ * b) * a := ((mul_comm _ _).trans (mul_inv_cancel_left a b)).symm
    rw [e, hφ _ h']
  haveI : Finite (Kˣ ⧸ NE τ) := by
    refine Finite.of_injective (fun q : Kˣ ⧸ NE τ => decide (hs (τ ^ 2 - 4) ((Quotient.out q : Kˣ) : K) = 1)) ?_
    intro p q hpq
    have key : ((Quotient.out p : Kˣ) : Kˣ ⧸ NE τ) = (Quotient.out q : Kˣ) := by
      rw [hmk]
      simp only [decide_eq_decide] at hpq
      rcases pm ((Quotient.out p : Kˣ) : K) with h1 | h1 <;> rcases pm ((Quotient.out q : Kˣ) : K) with h2 | h2 <;>
        (rw [h1, h2] at hpq ⊢; try norm_num at hpq)
    simpa using key
  have shift : ∀ φ : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, φ (t * x) = φ x) →
      ∑ᶠ t : Kˣ ⧸ NE τ, φ (Quotient.out t * g) = ∑ᶠ t : Kˣ ⧸ NE τ, φ (Quotient.out t) := by
    intro φ hφ
    have e : ∀ t : Kˣ ⧸ NE τ, φ (Quotient.out t * g) = φ (Quotient.out (t * (g : Kˣ ⧸ NE τ))) := by
      intro t
      apply inv_of φ hφ
      simp
    rw [finsum_congr e]
    exact finsum_comp_equiv (f := fun q : Kˣ ⧸ NE τ => φ (Quotient.out q)) (Equiv.mulRight (g : Kˣ ⧸ NE τ))
  refine ⟨shift f hf, ?_, ?_⟩
  · have hφ : ∀ t ∈ NE τ, ∀ x : Kˣ, hs (τ ^ 2 - 4) ((t * x : Kˣ) : K) * f (t * x) = hs (τ ^ 2 - 4) (x : K) * f x := by
      intro t ht x
      rw [hmul, (hsNE O K Δ τ L hτ t).1 ht, one_mul, hf t ht]
    have e : ∀ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K) * f (Quotient.out t * g) =
        hs (τ ^ 2 - 4) (g : K) * (hs (τ ^ 2 - 4) ((Quotient.out t * g : Kˣ) : K) * f (Quotient.out t * g)) := by
      intro t
      rw [hmul]
      linear_combination (-(hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K) * f (Quotient.out t * g))) * hsq g
    rw [finsum_congr e, ← mul_finsum,
      shift (fun x : Kˣ => hs (τ ^ 2 - 4) (x : K) * f x) hφ]
  · intro e x hfx ⟨t0, ht0⟩
    have hq : ∀ q : Kˣ ⧸ NE τ, q ≠ (t0 : Kˣ ⧸ NE τ) → hs (τ ^ 2 - 4) ((Quotient.out q : Kˣ) : K) ≠ e := by
      intro q hq h
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (hmk _ _).2 (h.trans ht0.symm)
    have h0 : hs (τ ^ 2 - 4) ((Quotient.out (t0 : Kˣ ⧸ NE τ) : Kˣ) : K) = e := by
      rw [← ht0]
      exact (hmk _ _).1 (by simp)
    constructor
    · rw [finsum_eq_single _ (t0 : Kˣ ⧸ NE τ)]
      · rw [hfx, if_pos h0]
      · intro q hq'
        rw [hfx, if_neg (hq q hq')]
    · rw [finsum_eq_single _ (t0 : Kˣ ⧸ NE τ)]
      · rw [hfx, if_pos h0, h0]
      · intro q hq'
        rw [hfx, if_neg (hq q hq'), mul_zero]
end

