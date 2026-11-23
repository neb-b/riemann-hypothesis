module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameConditionAlt
section
open IsLocalRing Matrix Polynomial UpperTheory.V.W

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  simp only [GDet.chi, GDet.map, GDet.ofRep]
  rw [Matrix.charpoly]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Matrix.coe_detMonoidHom]
  congr 1
  simp only [MonoidAlgebra.mapRingHom_single, map_one, GDet.repAlg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_sub, MonoidAlgebra.lift_single]
  refine Matrix.ext fun i k => ?_
  simp [Matrix.charmatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [Matrix.diagonal_apply]
  rfl

private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Polynomial.map_add (f := _), hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, RingHom.mapMatrix_apply, apply_ite f]

private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial]
    have hpow : N ^ k * Y = Y * M ^ k := by
      induction k with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]
    rw [mul_assoc, hpow, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem key {n : ℕ} {A K F : Type} [CommRing A] [Field K] [Field F] (f : A →+* K) (j : A →+* F)
    (hj : Function.Injective j) (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) F)
    (hY : j x • (j.mapMatrix M * Y) = Y * j.mapMatrix M) : Y = 0 := by
  classical
  set p := M.charpoly with hp
  set Mf := f.mapMatrix M with hMf
  set Mj := j.mapMatrix M with hMj
  have hint : aeval (j x • Mj) (p.map j) * Y = Y * aeval Mj (p.map j) :=
    aeval_inter Mj (j x • Mj) Y (by rw [smul_mul_assoc]; exact hY) _
  have hCH : aeval Mj (p.map j) = 0 := by
    rw [hp, ← Matrix.charpoly_map]
    exact Matrix.aeval_self_charpoly _
  rw [hCH, mul_zero] at hint
  have hfc : Mf.charpoly = (X - C c) ^ n := by
    rw [hMf, RingHom.mapMatrix_apply, Matrix.charpoly_map]
    exact hM
  set Nl := Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c with hNl
  have hnil : IsNilpotent Nl := by
    refine ⟨n, ?_⟩
    have h0 := Matrix.aeval_self_charpoly Mf
    rw [hfc, map_pow, map_sub, aeval_X, aeval_C] at h0
    exact h0
  set s : K := (f x - 1) * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hx) hc
  have hunitF : IsUnit (aeval (f x • Mf) (p.map f)) := by
    rw [hp, hM, map_pow, map_sub, aeval_X, aeval_C]
    apply IsUnit.pow
    have heq : f x • Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c =
        algebraMap K (Matrix (Fin n) (Fin n) K) s * ((s⁻¹ * f x) • Nl + 1) := by
      rw [← Algebra.smul_def, smul_add, smul_smul, mul_inv_cancel_left₀ hs0, hNl, hs,
        Algebra.algebraMap_eq_smul_one]
      module
    rw [heq]
    exact (IsUnit.map _ (Ne.isUnit hs0)).mul (hnil.smul _).isUnit_add_one
  set D : A := (aeval (x • M) p).det with hD
  have hfD : f D ≠ 0 := by
    have hsm : f.mapMatrix (x • M) = f x • Mf := by
      ext i k
      simp [hMf]
    have h1 : f D = (aeval (f x • Mf) (p.map f)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunitF).ne_zero
  have hD0 : D ≠ 0 := fun h => hfD (by rw [h, map_zero])
  have hjD : (aeval (j x • Mj) (p.map j)).det ≠ 0 := by
    have hsm : j.mapMatrix (x • M) = j x • Mj := by
      ext i k
      simp [hMj]
    have h1 : j D = (aeval (j x • Mj) (p.map j)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [← h1]
    exact fun h => hD0 (hj (by rw [h, map_zero]))
  have hU : IsUnit (aeval (j x • Mj) (p.map j)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hjD)
  exact (hU.mul_right_eq_zero).mp hint

private theorem absolute_irreducible_rank_four {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} {r : Resid F O n} (h : r.V0ok) (y : Point r) : y.N4 := by
  intro X hX
  obtain ⟨-, hchi, g, hg, heps⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    ext i
    exact i.elim0
  letI := y.field
  haveI := y.fin
  letI := y.algk
  letI := y.algO
  haveI := y.tower
  let i0 : Fin n := ⟨0, hn⟩
  let z : O := algebraMap ℤ_[l] O (F.ε g)
  let c : y.K := algebraMap (ResidueField O) y.K (r.chib i0 g)
  refine key (PowerSeries.constantCoeff) (algebraMap y.A y.Fr) (IsFractionRing.injective _ _) (mat y.ρ g)
    (algebraMap O y.A z) c ?_ ?_ ?_ X ?_
  · exact (_root_.map_ne_zero _).mpr (Units.ne_zero _)
  · intro h1
    apply heps
    apply Units.ext
    apply (algebraMap (ResidueField O) y.K).injective
    rw [Units.val_one, map_one, ← h1]
    show algebraMap (ResidueField O) y.K (algebraMap O (ResidueField O) z) =
      PowerSeries.constantCoeff (algebraMap O y.A z)
    rw [← IsScalarTower.algebraMap_apply]
    first
    | rfl
    | simp [PowerSeries.algebraMap_apply']
  · have hred := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at hred
    rw [hred]
    show Polynomial.map _ (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).charpoly = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hall : ∀ i : Fin n, (Polynomial.X - C (algebraMap (ResidueField O) y.K ↑((r.chib i) g))) =
        Polynomial.X - C c := fun i => by rw [hchi g hg i i0]
    simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have := hX g hg
    exact this

theorem UpperTheory.V.Pr.n4Of :
    UpperTheory.V.Pr.EveryPointSatisfiesFrameCondition := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M _ L _ _ _ _ _ Φ k c₁ _ f n ka R y
  exact absolute_irreducible_rank_four R.v0 y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsFrameFactorizationOfTrivialOnInertia
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix
set_option linter.overlappingInstances false

private theorem fac_conj {Ω : Type} [Field Ω] [CharZero Ω] (l : ℕ) (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hl : ¬ A.valuation (l : Ω) < 1) (hx : x ∈ Ine (F := ℚ) A) :
    ∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g * x * g⁻¹ ∈ Ine (F := ℚ) A' := by
  have h : IsLift (RingEquiv.refl ℚ) ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω) := fun q => g.symm.commutes q
  let σ : Ω ≃+* Ω := ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)
  have hA : ∀ y : Ω, σ y ∈ A ↔ y ∈ A.comap (σ : Ω →+* Ω) := fun y => by
    rw [ValuationSubring.mem_comap]
    rfl
  refine ⟨A.comap (σ : Ω →+* Ω), ?_, ?_⟩
  · rw [← val_lt_one hA (l : Ω), map_natCast]
    exact hl
  · have hc := conjGal_mem_Ine h hA hx
    convert hc using 1
    ext z
    rfl

theorem UpperTheory.exists_frame_factorization_of_trivial_on_inertia :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, Ψ (galEmb ℚ L Ω s) = 1 → r s = 1) → ∃ r' : Φ.G0 →* GL (Fin n) (Qbar l), Continuous r' ∧ (∀ s, r' (k.p0 s) = r s) ∧ ∀ P : GL (Fin n) (Qbar l), Sd.IsPair σ r 1 P → ∀ g, (r' g).valᵀ * P.val * (r' (Φ.conj g)).val = P.val := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k n r hr hine
  have hgal : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := fun s => by
    have h := galEmb_mem ℚ L Ω s
    rwa [k.gal] at h
  have hmem : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L := fun s => (hgal s).1
  have hq : ∀ s, (k.p0 s : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  let q : G L Ω →* Φ.G0 :=
    { toFun := k.p0
      map_one' := by
        apply Subtype.ext
        rw [hq]
        rw [show (⟨galEmb ℚ L Ω 1, hmem 1⟩ : upl Ω L) = 1 from Subtype.ext (map_one _), map_one]
        rfl
      map_mul' := fun s t => by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hq, hq, hq, ← map_mul]
        exact congrArg k.p (Subtype.ext (map_mul _ _ _)) }
  have hqv : ∀ s, ((q s : Φ.G0) : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨u, hu⟩ := k.p_surj x.val
    have hu1 : (u : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      refine ⟨u.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [← k.del u, hu]
      exact MonoidHom.mem_ker.mp x.2
    rw [← range_galEmb ℚ L Ω] at hu1
    obtain ⟨s, hs⟩ := hu1
    refine ⟨s, Subtype.ext ?_⟩
    rw [hqv, ← hu]
    exact congrArg k.p (Subtype.ext hs)
  have hgc : Continuous (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.continuous
  have hqc : Continuous q := by
    refine continuous_induced_rng.2 ?_
    exact k.p_cont.comp (hgc.subtype_mk hmem)
  have hinj : Function.Injective (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.injective
  have hker : ∀ s, q s = 1 → r s = 1 := by
    intro s hs
    have h1 : (⟨galEmb ℚ L Ω s, hmem s⟩ : upl Ω L) ∈ k.p.ker := by
      rw [MonoidHom.mem_ker, ← hqv, hs]
      rfl
    rw [k.p_ker] at h1
    let H' : Subgroup (upl Ω L) := (r.ker.map (galEmb ℚ L Ω)).comap (upl Ω L).subtype
    have hcl : IsClosed (H' : Set (upl Ω L)) := by
      have hk : IsClosed (r.ker : Set (G L Ω)) := by
        haveI : T2Space (Qbar l) := inferInstance
        haveI : T2Space (Matrix (Fin n) (Fin n) (Qbar l)) :=
          (inferInstance : T2Space (Fin n → Fin n → Qbar l))
        haveI h2 : T2Space (GL (Fin n) (Qbar l)) := inferInstance
        haveI : T1Space (GL (Fin n) (Qbar l)) := @T2Space.t1Space _ _ h2
        exact isClosed_singleton.preimage hr
      have hi : IsClosed ((galEmb ℚ L Ω) '' (r.ker : Set (G L Ω))) :=
        (hk.isCompact.image hgc).isClosed
      exact hi.preimage continuous_subtype_val
    have hX : Subgroup.normalClosure
        {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ barChar O Ψ s = 1} ≤ H' := by
      unfold Subgroup.normalClosure
      refine (Subgroup.closure_le _).2 ?_
      intro c hc
      rw [Group.mem_conjugatesOfSet_iff] at hc
      obtain ⟨x, ⟨B', hB'l, hxI, hxη, hxbar⟩, hconj⟩ := hc
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hcv : (c : G ℚ Ω) = u * x * (u : G ℚ Ω)⁻¹ := by
        rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨A', hA'l, hcI⟩ := fac_conj l B' u x hB'l hxI
      rw [← hcv] at hcI
      have hcη : η c = 1 := by
        rw [hcv, map_mul, map_mul, hxη, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcbar : barChar O Ψ c = 1 := by
        rw [hcv, map_mul, map_mul, hxbar, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcgal : (c : G ℚ Ω) ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨c.2, hcη⟩
      rw [← range_galEmb ℚ L Ω] at hcgal
      obtain ⟨t, ht⟩ := hcgal
      have hΨ : Ψ c = 1 := k.teich A' hA'l c ⟨hcI, c.2⟩ hcbar
      show (c : G ℚ Ω) ∈ r.ker.map (galEmb ℚ L Ω)
      refine ⟨t, ?_, ht⟩
      show r t = 1
      refine hine A' hA'l t ?_ ?_
      · show galEmb ℚ L Ω t ∈ Ine (F := ℚ) A'
        rw [ht]
        exact hcI
      · rw [ht]
        exact hΨ
    have h2 := (Subgroup.topologicalClosure_minimal _ hX hcl) h1
    obtain ⟨t, ht, hts⟩ := h2
    rw [hinj hts] at ht
    exact ht
  have hle : q.ker ≤ r.ker := fun s hs => hker s hs
  let e := QuotientGroup.quotientKerEquivOfSurjective q hqs
  let r' : Φ.G0 →* GL (Fin n) (Qbar l) := (QuotientGroup.lift q.ker r hle).comp e.symm.toMonoidHom
  have hr'q : ∀ s, r' (q s) = r s := by
    intro s
    have he : e.symm (q s) = (s : G L Ω ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift q.ker r hle (e.symm (q s)) = r s
    rw [he]
    rfl
  have hqq : Topology.IsQuotientMap q := Topology.IsQuotientMap.of_surjective_continuous hqs hqc
  have hr'c : Continuous r' := by
    rw [hqq.continuous_iff]
    convert hr using 1
    funext s
    exact hr'q s
  refine ⟨r', hr'c, fun s => hr'q s, ?_⟩
  intro P hP g
  obtain ⟨s, rfl⟩ := hqs g
  obtain ⟨hσ, hσc⟩ := k.c
  have hs'gal : σ * galEmb ℚ L Ω s * σ⁻¹ ∈ galOf ℚ L Ω := by
    rw [k.gal]
    refine ⟨(upl Ω L).mul_mem ((upl Ω L).mul_mem hσ (hmem s)) ((upl Ω L).inv_mem hσ),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hgal s).2, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [← range_galEmb ℚ L Ω] at hs'gal
  obtain ⟨s', hs'⟩ := hs'gal
  have hconj : Φ.conj (q s) = q s' := by
    apply Subtype.ext
    rw [show ((Φ.conj (q s) : Φ.G0) : Φ.Γ) = Φ.c * (q s : Φ.Γ) * Φ.c⁻¹ from
      MulAut.conjNormal_apply _ _]
    rw [hqv, hqv, ← hσc, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg k.p
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hs'.symm
  rw [hconj, hr'q, hr'q]
  have h := hP s s' hs'
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkHost
section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  have h2 : B.valuation (2 : Ω) < 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (1 : _) ≤ B.valuation (2 : Ω) * B.valuation (2 : Ω) := one_le_mul hc hc
    rw [← map_mul] at h4
    have : ((4 : ℕ) : Ω) = 2 * 2 := by norm_num
    rw [this] at h
    exact absurd h (not_lt.mpr h4)
  obtain ⟨k, rfl⟩ := hM
  have hk : B.valuation (k : Ω) ≤ 1 := by
    exact B.valuation_le_one (k : B)
  have : ((k + k : ℕ) : Ω) = 2 * (k : Ω) := by push_cast; ring
  rw [this, map_mul]
  exact mul_lt_one_of_lt_of_le h2 hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ValIntLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω]

private theorem val_int_le (A : ValuationSubring Ω) (a : ℤ) : A.valuation (a : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (intCast_mem A a)

private theorem val_dvd (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b) (ha : A.valuation (a : Ω) < 1) :
    A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha (by simpa only [Int.cast_natCast] using val_int_le A (c : ℤ))

private theorem val_prime (A : ValuationSubring Ω) (n : ℕ) (hn : n ≠ 0) (h : A.valuation (n : Ω) < 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ A.valuation (p : Ω) < 1 := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp only [Nat.cast_one, map_one, lt_self_iff_false] at h
  | prime p hp => exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    rw [Nat.cast_mul, map_mul] at h
    by_cases ha : A.valuation (a : Ω) < 1
    · obtain ⟨p, hp, hd, hv⟩ := iha (left_ne_zero_of_mul hn) ha
      exact ⟨p, hp, hd.mul_right _, hv⟩
    · have h1 : A.valuation (a : Ω) = 1 := le_antisymm (by simpa only [Int.cast_natCast] using val_int_le A (a : ℤ)) (not_lt.1 ha)
      rw [h1, one_mul] at h
      obtain ⟨p, hp, hd, hv⟩ := ihb (right_ne_zero_of_mul hn) h
      exact ⟨p, hp, hd.mul_left _, hv⟩

private theorem val_cop (A : ValuationSubring Ω) {a b : ℕ} (h : a.Coprime b) (ha : A.valuation (a : Ω) < 1) :
    ¬ A.valuation (b : Ω) < 1 := by
  intro hb
  obtain ⟨u, v, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (a : Ω) * (u : Ω) + (b : Ω) * (v : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) e
    push_cast at this
    rw [← this]; ring
  have h1 : A.valuation ((a : Ω) * (u : Ω) + (b : Ω) * (v : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_lt_of_le ha (val_int_le A u)
    · exact mul_lt_one_of_lt_of_le hb (val_int_le A v)
  rw [e', map_one] at h1
  exact lt_irrefl _ h1

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem algClo (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem exists_alg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω]
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) : ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := algClo (Ω := Ω) L
  have h1 : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) _).2 fun f => h (galEmb_mem ℚ L Ω f) x
  choose f hf using h1
  have hi := (algebraMap L Ω).injective
  let g : K →+* L :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun a b => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun a b => hi (by simp [hf]) }
  letI := g.toAlgebra
  exact ⟨_, IsScalarTower.of_algebraMap_eq fun x => (hf x).symm⟩

private theorem discr_over (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois ℚ K] (M : ℕ)
    (h : ∀ B : ValuationSubring Ω, ¬ Ine (F := ℚ) B ≤ galOf ℚ K Ω → B.valuation (M : Ω) < 1)
    (A : ValuationSubring Ω) (hA : A.valuation ((discr K : ℤ) : Ω) < 1) : A.valuation (M : Ω) < 1 := by
  haveI := algClo (Ω := Ω) K
  have hA' : A.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
    rcases Int.natAbs_eq (discr K) with e | e
    · rwa [e, Int.cast_natCast] at hA
    · rwa [e, Int.cast_neg, Valuation.map_neg, Int.cast_natCast] at hA
  obtain ⟨p, hp, hd, hv⟩ := val_prime A _ (Int.natAbs_ne_zero.2 (discr_ne_zero K)) hA'
  by_cases hM : p ∣ M
  · exact val_dvd A hM hv
  exfalso
  refine (CF.unramIff.2.1 K p hp).1 ((CF.unramIff.1 K p hp).2 fun w hw => ?_) (Int.natCast_dvd.2 hd)
  obtain ⟨B, hB⟩ : ∃ B : ValuationSubring Ω, IsPlaceOver B w := exists_isPlaceOver Ω w
  have hpB : B.valuation (p : Ω) < 1 := by
    have := (hB (p : 𝓞 K)).2 hw
    simpa only [map_natCast] using this
  have hI : Ine (F := ℚ) B ≤ galOf ℚ K Ω := by
    by_contra hc
    exact val_cop B ((Nat.Prime.coprime_iff_not_dvd hp).2 hM) hpB (h B hc)
  rw [← CF.ineAbs ℚ K Ω B w hB, eq_bot_iff]
  rintro _ ⟨s, hs, rfl⟩
  refine Subgroup.mem_bot.2 (AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_)
  rw [CF.resTo_commutes]
  exact hI hs x

end

theorem UpperTheory.V.Pr.kaOf :
    UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → UpperTheory.V.Pr.KaOf := by
  intro hC hR Ω _ _ _ l hl ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k
  have hlM : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 :=
    fun A h h' => h (val_dvd A ((Dvd.intro _ rfl).trans H.dvd) h')
  have hcyc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, (cycBar L Ω l)⁻¹ s = 1 := by
    intro A hA s hs
    have h1 : cycZ L Ω l s = 1 := (places L Ω l A).2.2.2 hA hs
    simp [cycBar, h1]
  refine ⟨⟨?_, ?_, fun A hA => hcyc A (hlM A hA), 1, fun h => hl.out.one_lt.ne' (Nat.dvd_one.1 h),
    fun A hA s hs => by rw [pow_one]; exact hcyc A hA s hs⟩, fun K _ _ _ hK κ hκ => ?_⟩
  · have h := (hC L Ω l ι).1 (-1) 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    rwa [mul_one, zpow_neg_one] at h
  · intro s s' h
    have h1 : cycBar L Ω l s' = cycBar L Ω l s := by
      change cycBar ℚ Ω l (galEmb ℚ L Ω s') = cycBar ℚ Ω l (galEmb ℚ L Ω s)
      rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, h1, ← zpow_neg_one, ← zpow_add]
    norm_num
  · have hle : galOf ℚ L Ω ≤ galOf ℚ K Ω := by
      rw [k.gal, hK]
      exact inf_le_right
    obtain ⟨_, _⟩ := exists_alg K L hle
    haveI := algClo (Ω := Ω) K
    haveI := k.ab
    haveI : IsAbelianGalois ℚ K := IsAbelianGalois.tower_bot ℚ K L
    have hI : ∀ (A : ValuationSubring Ω) (s : G L Ω), s ∈ Ine (F := L) A → galEmb K L Ω s ∈ Ine (F := K) A :=
      fun A s hs => ⟨hs.1, hs.2⟩
    refine ⟨κ.comp (galEmb K L Ω), ⟨hR K L Ω l ι κ ⟨hκ.cont, ?_⟩, fun s s' h => ?_, fun A hA s hs => ?_, ?_⟩,
      fun s s' h => ?_⟩
    · obtain ⟨art, Y, a, -, h1, h2, h3, -⟩ := hκ.alg
      exact ⟨art, Y, a, h1, h2, h3⟩
    · rw [show (1 : ℤ) - ((2 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
      exact hκ.conj (galEmb K L Ω s) (galEmb K L Ω s') h
    · exact hκ.unr A (hlM A hA) (fun h => hA (discr_over K M (fun B' hB' => H.ram B' (hK ▸ hB')) A h)) _ (hI A s hs)
    · obtain ⟨m, -, h1, h2⟩ := hκ.ord
      exact ⟨m, h1, fun A hA s hs => h2 A hA _ (hI A s hs)⟩
    · exact congrArg κ (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
end

