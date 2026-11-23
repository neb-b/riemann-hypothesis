module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.ExistsSeparatingElement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Pu.exists_separating_element {O A k : Type} [CommRing O] [Ring A] [Field k] [Algebra O A] [Algebra O k]
    {n : ℕ} (f g : Fin n → A →ₐ[O] k) (e : Fin n → Fin n → A)
    (h1 : ∀ a b, f a (e a b) = 1) (h0 : ∀ a b, g b (e a b) = 0) :
    ∃ y : A, (∀ a, f a y = 1) ∧ ∀ b, g b y = 0 := by
  let ya : Fin n → A := fun a => ((List.finRange n).map (e a)).prod
  have hf : ∀ a, f a (ya a) = 1 := by
    intro a
    simp only [ya, map_list_prod, List.map_map]
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact h1 a b
  have hg : ∀ a b, g b (ya a) = 0 := by
    intro a b
    simp only [ya, map_list_prod, List.map_map]
    apply List.prod_eq_zero
    rw [List.mem_map]
    exact ⟨b, List.mem_finRange b, h0 a b⟩
  refine ⟨1 - ((List.finRange n).map (fun a => 1 - ya a)).prod, ?_, ?_⟩
  · intro a
    rw [map_sub, map_one, map_list_prod, List.map_map, List.prod_eq_zero, sub_zero]
    rw [List.mem_map]
    exact ⟨a, List.mem_finRange a, by simp [hf a]⟩
  · intro b
    rw [map_sub, map_one, map_list_prod, List.map_map, List.prod_eq_one, sub_self]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    simp [hg a b]

theorem UpperTheory.V.Ws.Pu.sepEl :
    ∀ {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] {n : ℕ} (χ ψ : Fin n → Γ →* (ResidueField O)ˣ), (∀ a b, χ a ≠ ψ b) →
      ∃ y : MonoidAlgebra O Γ, (∀ a, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a)) y = 1) ∧
        ∀ b, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b)) y = 0 := by
  intro O Γ _ _ _ n χ ψ hne
  have key : ∀ a b, ∃ e : MonoidAlgebra O Γ, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a)) e = 1 ∧ MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b)) e = 0 := by
    intro a b
    obtain ⟨γ, hγ⟩ : ∃ γ, χ a γ ≠ ψ b γ := by
      by_contra hc
      push_neg at hc
      exact hne a b (MonoidHom.ext hc)
    have hu : ((χ a γ : ResidueField O) - (ψ b γ : ResidueField O)) ≠ 0 := sub_ne_zero.2 (fun h => hγ (Units.ext h))
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (ψ b γ : ResidueField O)
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective ((χ a γ : ResidueField O) - (ψ b γ : ResidueField O))⁻¹
    refine ⟨MonoidAlgebra.single γ s - MonoidAlgebra.single 1 (s * r), ?_, ?_⟩
    · simp only [map_sub, MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, map_one, Units.val_one, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, map_mul, hr, hs, mul_one]
      rw [← mul_sub, inv_mul_cancel₀ hu]
    · simp only [map_sub, MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, map_one, Units.val_one, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, map_mul, hr, hs, mul_one, sub_self]
  choose e he using key
  exact UpperTheory.V.Ws.Pu.exists_separating_element (fun a => MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a))) (fun b => MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b))) e (fun a b => (he a b).1) (fun a b => (he a b).2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.FrobEigEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open Pointwise in
private theorem frob_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g σ : G F Ω} (hσ : IsFrob (F := F) (g • A) q σ) : IsFrob (F := F) A q (g⁻¹ * σ * g) := by
  have key : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation (g⁻¹ y) < 1 := by
    intro y
    rw [valuation_lt_one_iff', valuation_lt_one_iff',
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp [AlgEquiv.smul_def, map_inv₀]
  refine ⟨?_, fun x hx => ?_⟩
  · have hs : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, hs, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [AlgEquiv.smul_def] using hx
    have h := hσ.2 (g x) hx'
    rw [key] at h
    convert h using 2
    simp [map_sub, map_pow, AlgEquiv.mul_apply]

private theorem frob_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {q : ℕ}
    {σ τ : G F Ω} (hσ : IsFrob (F := F) A q σ) (hτ : IsFrob (F := F) A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hσ.1) hτ.1, fun x hx => ?_⟩
  have h1 : A.valuation (τ x - σ x) < 1 := by
    have h := Valuation.map_sub_lt A.valuation (hτ.2 x hx) (hσ.2 x hx)
    rwa [sub_sub_sub_cancel_right] at h
  have hd : σ⁻¹ ∈ Dec (F := F) A := Subgroup.inv_mem _ hσ.1
  rw [← valuation_apply_lt_one_iff hd] at h1
  convert h1 using 2
  simp [map_sub, AlgEquiv.mul_apply]

theorem UpperTheory.V.Ws.Pu.frobEigEx :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} (ι : PadicAlgCl l ≃+* ℂ) (ρ : G F Ω →* GL (Fin n) (PadicAlgCl l)) (w : HeightOneSpectrum (𝓞 F)), (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := F) A, ρ s = 1) → ∃ b, Af.FrobEig ι ρ w b := by
  intro F Ω _ _ _ _ _ l _ n ι ρ w hI
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ₀, hσ₀⟩ := exists_isFrob (F := F) hA₀
  set p := ((ρ σ₀⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)).charpoly.map
    ι.toRingHom with hp
  refine ⟨p.roots, fun A hA => ⟨hI A hA, fun σ hσ => ?_⟩⟩
  have hpm : p.Monic := (Matrix.charpoly_monic _).map _
  rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm IsAlgClosed.card_roots_eq_natDegree]
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  have hb := frob_back hσ
  have h1 := hI A₀ hA₀ _ (frob_ine hσ₀ hb)
  rw [map_mul, map_inv] at h1
  have h2 : ρ (g⁻¹ * σ * g) = ρ σ₀ := (inv_mul_eq_one.mp h1).symm
  have h3 : ρ σ⁻¹ = ρ g * ρ σ₀⁻¹ * (ρ g)⁻¹ := by
    have e : σ⁻¹ = g * (g⁻¹ * σ * g)⁻¹ * g⁻¹ := by group
    rw [e, map_mul, map_mul, map_inv, map_inv, h2, map_inv]
  rw [hp, h3, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LevFin
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ine_dies {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (HeightOneSpectrum (𝓞 k))} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem fiber_fin {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    (v : HeightOneSpectrum (𝓞 k)) : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 k) = v}.Finite := by
  have hne : v.asIdeal.map (algebraMap (𝓞 k) (𝓞 L)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 L))]
    exact v.ne_bot
  refine (Ideal.finite_factors hne).subset fun w hw => ?_
  have hw' : w.under (𝓞 k) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hw']
  exact le_rfl

theorem UpperTheory.V.Ws.Pu.levFin :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), ∃ Z : Set (HeightOneSpectrum (𝓞 L)), Z.Finite ∧ ∀ w ∉ Z, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, V.pr g = 1 := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨(fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 (W.Lp L))) ⁻¹' V.S',
    V.fin.preimage' fun v _ => fiber_fin v, fun w hw => ⟨fun hl => hw (V.sub (Or.inl ?_)), fun A hA g hg => ?_⟩⟩
  · show algebraMap (𝓞 (W.Lp L)) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]
  · have hv : IsPlaceOver A (w.under (𝓞 (W.Lp L))) := fun x => hA (algebraMap (𝓞 (W.Lp L)) (𝓞 L) x)
    have hg' : W.resP L Ω g ∈ Ine (F := W.Lp L) A := hg
    have hw' : w.under (𝓞 (W.Lp L)) ∉ V.S' := hw
    exact Subtype.ext (ine_dies hw' hv hg')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LiftDiag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem chi_map_eq_map_chi_mapRingHom {n : ℕ} {B K Γ : Type} [CommRing B] [CommRing K] [Group Γ]
    (D : W.GDet n B Γ) (f : B →+* K) (z : MonoidAlgebra B Γ) :
    (D.chi z).map f = (D.map f).chi (MonoidAlgebra.mapRingHom Γ f z) := by
  letI : Algebra B K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  let φ : B[X] →ₐ[B] K[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have e : (MonoidAlgebra.mapRingHom Γ (φ : B[X] →+* K[X]))
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.mapRingHom Γ f z) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · congr 1
      change Polynomial.map f X = X
      simp only [Polynomial.map_X]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g b =>
        simp only [MonoidAlgebra.mapRingHom_single]
        change MonoidAlgebra.single g ((C b).map f) = MonoidAlgebra.single g (C (f b))
        rw [Polynomial.map_C]
  have h := D.nat B[X] K[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C z)
  rw [e] at h
  exact h.symm

private theorem chi_ofRep_eq_charpoly_lift {n : ℕ} {K Γ : Type} [CommRing K] [Group Γ]
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (w : MonoidAlgebra K Γ) :
    (W.GDet.ofRep σ).chi w = (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w).charpoly := by
  have e : W.GDet.repAlg σ K[X] (MonoidAlgebra.mapRingHom Γ C w) =
      (C : K →+* K[X]).mapMatrix (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) Γ σ w) := by
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]
      ext i j
      simp [Polynomial.smul_eq_C_mul, Polynomial.algebraMap_apply]
  have e1 : W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X) = Matrix.scalar (Fin n) (X : K[X]) := by
    simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, map_one]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  show Matrix.det (W.GDet.repAlg σ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C w)) = _
  rw [map_sub, e, e1]
  rfl

private theorem chi_map {n : ℕ} {O B K Γ : Type} [CommRing O] [CommRing B] [CommRing K] [Algebra O B] [Algebra O K]
    [Group Γ] (D : W.GDet n B Γ) (f : B →ₐ[O] K) (σ : Γ →* Matrix (Fin n) (Fin n) K)
    (h : D.map (f : B →+* K) = W.GDet.ofRep σ) (y : MonoidAlgebra O Γ) :
    (D.chi (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y)).map (f : B →+* K) =
      (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ σ y).charpoly := by
  rw [chi_map_eq_map_chi_mapRingHom, h, chi_ofRep_eq_charpoly_lift]
  have e : MonoidAlgebra.mapRingHom Γ (f : B →+* K) (MonoidAlgebra.mapRingHom Γ (algebraMap O B) y) =
      MonoidAlgebra.mapRingHom Γ (algebraMap O K) y := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g b => simp [MonoidAlgebra.mapRingHom_single]
  rw [e, MonoidAlgebra.lift_mapRingHom_algebraMap]

private theorem lift_diag {n : ℕ} {O K Γ : Type} [CommRing O] [CommRing K] [Algebra O K]
    [Group Γ] (χ : Fin n → Γ →* Kˣ) (y : MonoidAlgebra O Γ) :
    MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.diagRep χ) y =
      Matrix.diagonal fun i => MonoidAlgebra.lift O K Γ ((Units.coeHom _).comp (χ i)) y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
    congr 1
    funext i
    rw [map_add (f := _)]
  | single g b =>
    ext i j
    simp [W.diagRep, MonoidAlgebra.lift_single, Matrix.diagonal_apply]

private theorem near {n : ℕ} {B K : Type} [CommRing B] [NormedField K] [IsUltrametricDist K] (I : Ideal B)
    (x : B →+* K) (h1 : ∀ b, ‖x b‖ ≤ 1) (hm : ∀ b ∈ I, ‖x b‖ < 1) (P : B[X]) (hP : (P.map x).Monic) (a : Fin n → B)
    (ha : ∀ k, (P - ∏ i, (X - C (a i))).coeff k ∈ I) (z : K) (hz : (P.map x).IsRoot z) : ∃ i, ‖z - x (a i)‖ < 1 := by
  classical
  have hcoef : ∀ k, ‖(P.map x).coeff k‖ ≤ 1 := fun k => by rw [Polynomial.coeff_map]; exact h1 _
  have hz1 : ‖z‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hev := hz.eq_zero
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at hev
    set d := (P.map x).natDegree
    have hzd : z ^ d = -∑ i ∈ Finset.range d, (P.map x).coeff i * z ^ i := by
      linear_combination hev
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd] at hzd
      simp at hzd
    have hpos : 0 < ‖z‖ ^ (d - 1) := pow_pos (by linarith) _
    have hle : ‖z‖ ^ d ≤ ‖z‖ ^ (d - 1) := by
      rw [← norm_pow, hzd, norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos.le fun i hi => ?_
      rw [norm_mul, norm_pow]
      have hi' : i ≤ d - 1 := by
        have := Finset.mem_range.mp hi
        omega
      calc ‖(P.map x).coeff i‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
            mul_le_mul_of_nonneg_right (hcoef i) (by positivity)
        _ = ‖z‖ ^ i := one_mul _
        _ ≤ ‖z‖ ^ (d - 1) := pow_le_pow_right₀ hlt.le hi'
    have : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this] at hle
    nlinarith
  have hE : ‖((P - ∏ i, (X - C (a i))).map x).eval z‖ < 1 := by
    rw [Polynomial.eval_eq_sum_range]
    obtain ⟨k, -, hle⟩ :=
      IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
        (fun i => ((P - ∏ i, (X - C (a i))).map x).coeff i * z ^ i)
    refine hle.trans_lt ?_
    rw [norm_mul, norm_pow, Polynomial.coeff_map]
    calc ‖x ((P - ∏ i, (X - C (a i))).coeff k)‖ * ‖z‖ ^ k
        ≤ ‖x ((P - ∏ i, (X - C (a i))).coeff k)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hm _ (ha k)
  have hsum : (P.map x).eval z = (∏ i, (z - x (a i))) + ((P - ∏ i, (X - C (a i))).map x).eval z := by
    rw [Polynomial.map_sub, Polynomial.eval_sub, Polynomial.map_prod, Polynomial.eval_prod]
    simp
  have hprod : ‖∏ i, (z - x (a i))‖ < 1 := by
    have : ∏ i, (z - x (a i)) = -((P - ∏ i, (X - C (a i))).map x).eval z := by
      rw [hz.eq_zero] at hsum
      linear_combination (-1 : K) * hsum
    rw [this, norm_neg]
    exact hE
  by_contra hne
  push_neg at hne
  have : (1 : ℝ) ≤ ‖∏ i, (z - x (a i))‖ := by
    rw [norm_prod]
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∏ i, ‖z - x (a i)‖ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hne i)
  linarith

theorem UpperTheory.V.Ws.Pu.ptRed :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → RedTo c ρ fun i => (r.chib i).comp V.pr := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx
  intro y z hz
  letI := B.ring
  letI := B.alg
  haveI := B.co
  set D := B.u.D.comap V.pr with hD
  have hxD : D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) := hx
  have hrD : D.map (res c.O B.B : B.B →+* ResidueField c.O) =
      W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp V.pr) := by
    have h0 : (B.u.D.map (res c.O B.B : B.B →+* ResidueField c.O)).comap V.pr =
        (r.Dbar).comap V.pr := by rw [B.u.red]
    refine h0.trans ?_
    rw [W.Resid.Dbar]
    refine ((AlgebraTools.Det.repApi (W.diagRep r.chib)).2.2.2.2.2.2.1 V.pr).trans ?_
    exact congrArg W.GDet.ofRep (MonoidHom.ext fun g => rfl)
  set P := D.chi (MonoidAlgebra.mapRingHom _ (algebraMap c.O B.B) y) with hP
  have hPx := chi_map D (x : B.B →ₐ[c.O] PadicAlgCl l) (W.mat ρ) hxD y
  have hPr := chi_map D (res c.O B.B) (W.diagRep fun i => (r.chib i).comp V.pr) hrD y
  rw [lift_diag, Matrix.charpoly_diagonal] at hPr
  set d : Fin n → ResidueField c.O := fun i =>
    MonoidAlgebra.lift c.O (ResidueField c.O) _ ((Units.coeHom _).comp ((r.chib i).comp V.pr)) y with hd
  choose a' ha' using fun i => IsLocalRing.residue_surjective (d i)
  have hco := (GradeZeroInterpolatingElement.coPt c B.B).1 x
  obtain ⟨-, e, he1, he0, hen⟩ := hco
  have h1 : ∀ b, ‖(x : B.B →+* PadicAlgCl l) b‖ ≤ 1 := fun b => by
    have := hen 0 b (by simp)
    simpa using this
  have hm : ∀ b ∈ IsLocalRing.maximalIdeal B.B, ‖(x : B.B →+* PadicAlgCl l) b‖ < 1 := fun b hb => by
    have := hen 1 b (by simpa using hb)
    simp only [pow_one] at this
    exact lt_of_le_of_lt this he1
  have hmon : (P.map (x : B.B →+* PadicAlgCl l)).Monic := by
    rw [hPx]
    exact Matrix.charpoly_monic _
  have hroot : (P.map (x : B.B →+* PadicAlgCl l)).IsRoot z := by
    rw [hPx]
    exact Polynomial.isRoot_of_mem_roots hz
  have hres : ∀ i, (res c.O B.B) (algebraMap c.O B.B (a' i)) = d i := fun i => by
    rw [AlgHom.commutes, ← ha' i]
    rfl
  have hcoef : ∀ k, (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).coeff k ∈ IsLocalRing.maximalIdeal B.B := by
    intro k
    rw [← res_eq_zero_iff c.O B.B]
    show (res c.O B.B : B.B →+* ResidueField c.O) _ = 0
    rw [← Polynomial.coeff_map]
    have : (P - ∏ i, (X - C (algebraMap c.O B.B (a' i)))).map (res c.O B.B : B.B →+* ResidueField c.O) = 0 := by
      rw [Polynomial.map_sub, hPr, Polynomial.map_prod, sub_eq_zero]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      exact (hres i).symm
    rw [this, Polynomial.coeff_zero]
  obtain ⟨i, hi⟩ := near (IsLocalRing.maximalIdeal B.B) (x : B.B →+* PadicAlgCl l) h1 hm P hmon
    (fun i => algebraMap c.O B.B (a' i)) hcoef z hroot
  refine ⟨i, a' i, ha' i, ?_⟩
  have : (x : B.B →+* PadicAlgCl l) (algebraMap c.O B.B (a' i)) = (a' i : PadicAlgCl l) := by
    show x (algebraMap c.O B.B (a' i)) = _
    rw [AlgHom.commutes]
    rfl
  rwa [this] at hi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.MemRootsIffSpec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mem_roots_iff_spec {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : K) :
    z ∈ M.charpoly.roots ↔ z ∈ spectrum K M := by
  rw [mem_roots M.charpoly_monic.ne_zero, Matrix.mem_spectrum_iff_isRoot_charpoly]

private theorem roots_aeval {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) (w : K)
    (hw : w ∈ (aeval M p).charpoly.roots) : ∃ z ∈ M.charpoly.roots, p.eval z = w := by
  rw [mem_roots_iff_spec] at hw
  have hnt : Nontrivial (Matrix (Fin n) (Fin n) K) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hw (isUnit_of_subsingleton _)
  rw [spectrum.map_polynomial_aeval_of_nonempty M p (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K M)] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, (mem_roots_iff_spec M z).2 hz, rfl⟩

private theorem sum_eq_count {K : Type} [Field K] [DecidableEq K] (c : K) (hc : c ≠ 0) (s : Multiset K)
    (h : ∀ w ∈ s, w = 0 ∨ w = c) : s.sum = (s.count c : K) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))]
    rcases h a (Multiset.mem_cons_self _ _) with rfl | rfl
    · rw [Multiset.count_cons_of_ne hc]; simp
    · rw [Multiset.count_cons_self]; push_cast; ring

theorem UpperTheory.V.Ws.Pu.cpAlg :
    ∀ {O K Γ S : Type} [CommRing O] [Field K] [CharZero K] [IsAlgClosed K] [Algebra O K] [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (t : Finset S) (d : S → ℕ) (σ : ∀ i, Γ →* GL (Fin (d i)) K),
      (∀ g, (W.mat ρ g).charpoly = ∏ i ∈ t, (W.mat (σ i) g).charpoly) → ∀ (y : MonoidAlgebra O Γ), ∀ i ∈ t,
        ∀ z ∈ (MonoidAlgebra.lift O (Matrix (Fin (d i)) (Fin (d i)) K) Γ (W.mat (σ i)) y).charpoly.roots,
          z ∈ (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) y).charpoly.roots := by
  intro O K Γ S _ _ _ _ _ _ n ρ t d σ hcp y i hi z hz
  classical
  have h1 : ∀ g, (W.mat ρ g).trace = ∑ j ∈ t, (W.mat (σ j) g).trace := by
    intro g
    simp only [Matrix.trace_eq_sum_roots_charpoly]
    rw [hcp g, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun j _ => (Matrix.charpoly_monic _).ne_zero), Multiset.sum_bind]
    rfl
  have h2 : ∀ x : MonoidAlgebra O Γ, (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) x).trace =
      ∑ j ∈ t, (MonoidAlgebra.lift O (Matrix (Fin (d j)) (Fin (d j)) K) Γ (W.mat (σ j)) x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Matrix.trace_add, ha, hb, Finset.sum_add_distrib]
    | single g a => simp only [MonoidAlgebra.lift_single, Matrix.trace_smul, h1, Finset.smul_sum]
  set M := MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) y with hM
  set N := fun j => MonoidAlgebra.lift O (Matrix (Fin (d j)) (Fin (d j)) K) Γ (W.mat (σ j)) y with hN
  have h3 : ∀ p : K[X], (aeval M p).trace = ∑ j ∈ t, (aeval (N j) p).trace := by
    intro p
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add (f := _), Matrix.trace_add, ha, hb, Finset.sum_add_distrib]
    | monomial k a =>
      have := h2 (y ^ k)
      simp only [map_pow] at this
      simp only [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, hM, hN, this, Finset.smul_sum]
  by_contra hzM
  let T : Finset K := (M.charpoly.roots.toFinset ∪ t.biUnion fun j => (N j).charpoly.roots.toFinset).erase z
  let p : K[X] := ∏ w ∈ T, (X - C w)
  have hpz : p.eval z ≠ 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.2 fun w hw => sub_ne_zero.2 (Finset.ne_of_mem_erase hw).symm
  have hpT : ∀ w ∈ T, p.eval w = 0 := by
    intro w hw
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hw (sub_self _)
  have hM0 : (aeval M p).trace = 0 := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine Multiset.sum_eq_zero fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := roots_aeval M p w hw
    refine hpT u (Finset.mem_erase.2 ⟨?_, Finset.mem_union_left _ (Multiset.mem_toFinset.2 hu)⟩)
    rintro rfl
    exact hzM hu
  have hNj : ∀ j ∈ t, (aeval (N j) p).trace = ((aeval (N j) p).charpoly.roots.count (p.eval z) : K) * p.eval z := by
    intro j hj
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine sum_eq_count _ hpz _ fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := roots_aeval (N j) p w hw
    by_cases huz : u = z
    · exact Or.inr (by rw [huz])
    · exact Or.inl (hpT u (Finset.mem_erase.2 ⟨huz, Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, hj, Multiset.mem_toFinset.2 hu⟩)⟩))
  have h4 := h3 p
  rw [hM0, Finset.sum_congr rfl hNj, ← Finset.sum_mul, ← Nat.cast_sum] at h4
  have h5 := (mul_eq_zero.1 h4.symm).resolve_right hpz
  rw [Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at h5
  have h6 := h5 i hi
  rw [Multiset.count_eq_zero] at h6
  apply h6
  rw [mem_roots_iff_spec]
  exact spectrum.subset_polynomial_aeval (N i) p ⟨z, (mem_roots_iff_spec _ z).1 hz, rfl⟩
end

